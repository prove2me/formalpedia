-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_40_adaptive0seed25646_b4_part_3
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T14:29:07.184943+00:00
-- url     : https://prove2.me/submissions/7705dc05-04c2-487f-a06b-dff04c3b73cf

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Bands
import Definitions.Def_GaussLocalMaxColoring_Main_Section5

set_option autoImplicit false

section
-- Source module: Solutions.GaussLocalMaxCertificateInterval

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace GaussLocalMaxColoring.Certificate

structure RatInterval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq,Repr

def RatInterval.Contains (I : RatInterval) (x : ℝ) : Prop := (I.lo:ℝ) ≤ x ∧ x ≤ I.hi

def RatInterval.point (q : ℚ) : RatInterval := ⟨q,q⟩
def RatInterval.add (I J : RatInterval) : RatInterval := ⟨I.lo+J.lo,I.hi+J.hi⟩
def RatInterval.neg (I : RatInterval) : RatInterval := ⟨-I.hi,-I.lo⟩
def RatInterval.mul (I J : RatInterval) : RatInterval :=
  ⟨min (min (I.lo*J.lo) (I.lo*J.hi)) (min (I.hi*J.lo) (I.hi*J.hi)),
   max (max (I.lo*J.lo) (I.lo*J.hi)) (max (I.hi*J.lo) (I.hi*J.hi))⟩

theorem RatInterval.contains_point (q : ℚ) : (RatInterval.point q).Contains (q:ℝ) := ⟨le_rfl,le_rfl⟩

theorem RatInterval.contains_add (I J : RatInterval) (x y : ℝ) (hx : I.Contains x) (hy : J.Contains y) :
    (I.add J).Contains (x+y) := by
  change ((I.lo+J.lo:ℚ):ℝ) ≤ x+y ∧ x+y ≤ ((I.hi+J.hi:ℚ):ℝ)
  rw [Rat.cast_add,Rat.cast_add]
  exact ⟨add_le_add hx.1 hy.1,add_le_add hx.2 hy.2⟩

theorem RatInterval.contains_neg (I : RatInterval) (x : ℝ) (hx : I.Contains x) :
    I.neg.Contains (-x) := by
  change ((-I.hi:ℚ):ℝ) ≤ -x ∧ -x ≤ ((-I.lo:ℚ):ℝ)
  rw [Rat.cast_neg,Rat.cast_neg]
  exact ⟨neg_le_neg hx.2,neg_le_neg hx.1⟩

theorem real_mul_interval (x c l u L U : ℝ) (hx : l ≤ x ∧ x ≤ u)
    (hl : L ≤ l*c ∧ l*c ≤ U) (hu : L ≤ u*c ∧ u*c ≤ U) : L ≤ x*c ∧ x*c ≤ U := by
  by_cases hc : 0 ≤ c
  · exact ⟨hl.1.trans (mul_le_mul_of_nonneg_right hx.1 hc),
      (mul_le_mul_of_nonneg_right hx.2 hc).trans hu.2⟩
  · have hc' : c ≤ 0 := (lt_of_not_ge hc).le
    exact ⟨hu.1.trans (mul_le_mul_of_nonpos_right hx.2 hc'),
      (mul_le_mul_of_nonpos_right hx.1 hc').trans hl.2⟩

theorem real_mul_interval_corners (x y l u a b L U : ℝ)
    (hx : l ≤ x ∧ x ≤ u) (hy : a ≤ y ∧ y ≤ b)
    (hla : L ≤ l*a ∧ l*a ≤ U) (hlb : L ≤ l*b ∧ l*b ≤ U)
    (hua : L ≤ u*a ∧ u*a ≤ U) (hub : L ≤ u*b ∧ u*b ≤ U) : L ≤ x*y ∧ x*y ≤ U := by
  have ha := real_mul_interval x a l u L U hx hla hua
  have hb := real_mul_interval x b l u L U hx hlb hub
  have hh := real_mul_interval y x a b L U hy
    (by simpa only [mul_comm] using ha) (by simpa only [mul_comm] using hb)
  simpa only [mul_comm] using hh

theorem RatInterval.contains_mul (I J : RatInterval) (x y : ℝ) (hx : I.Contains x) (hy : J.Contains y) :
    (I.mul J).Contains (x*y) := by
  change (I.mul J).lo ≤ x*y ∧ x*y ≤ (I.mul J).hi
  apply real_mul_interval_corners x y I.lo I.hi J.lo J.hi (I.mul J).lo (I.mul J).hi hx hy
  all_goals
    simp only [RatInterval.mul,Rat.cast_min,Rat.cast_max,Rat.cast_mul]
    constructor
    · first | exact (min_le_left _ _).trans (min_le_left _ _) | exact (min_le_left _ _).trans (min_le_right _ _) | exact (min_le_right _ _).trans (min_le_left _ _) | exact (min_le_right _ _).trans (min_le_right _ _)
    · first | exact (le_max_left _ _).trans (le_max_left _ _) | exact (le_max_right _ _).trans (le_max_left _ _) | exact (le_max_left _ _).trans (le_max_right _ _) | exact (le_max_right _ _).trans (le_max_right _ _)

theorem RatInterval.contains_sqrt_of_checks (I J : RatInterval) (x : ℝ) (hx : I.Contains x)
    (hlo : 0 ≤ J.lo) (hhi : 0 ≤ J.hi) (hl2 : J.lo^2 ≤ I.lo) (hh2 : I.hi ≤ J.hi^2) :
    J.Contains (Real.sqrt x) := by
  have hl : (0:ℝ) ≤ J.lo := by exact_mod_cast hlo
  have hh : (0:ℝ) ≤ J.hi := by exact_mod_cast hhi
  have hlower : (J.lo:ℝ)^2 ≤ I.lo := by exact_mod_cast hl2
  have hupper : (I.hi:ℝ) ≤ (J.hi:ℝ)^2 := by exact_mod_cast hh2
  exact ⟨Real.le_sqrt_of_sq_le (hlower.trans hx.1),Real.sqrt_le_iff.mpr ⟨hh,hx.2.trans hupper⟩⟩

end GaussLocalMaxColoring.Certificate
end

section
-- Source module: Solutions.GaussLocalMaxCertificateReciprocal

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace GaussLocalMaxColoring.Certificate

def RatInterval.inv (I : RatInterval) : RatInterval := ⟨I.hi⁻¹,I.lo⁻¹⟩
def RatInterval.AwayZero (I : RatInterval) : Prop := 0 < I.lo ∨ I.hi < 0

theorem RatInterval.contains_ne_zero (I : RatInterval) (x : ℝ) (hx : I.Contains x)
    (hI : I.AwayZero) : x≠0 := by
  rcases hI with hp|hn
  · have hh : (0:ℝ) < I.lo := by exact_mod_cast hp
    exact (hh.trans_le hx.1).ne'
  · have hh : (I.hi:ℝ) < 0 := by exact_mod_cast hn
    exact (hx.2.trans_lt hh).ne

theorem RatInterval.contains_inv (I : RatInterval) (x : ℝ) (hx : I.Contains x)
    (hI : I.AwayZero) : I.inv.Contains x⁻¹ := by
  change ((I.hi⁻¹:ℚ):ℝ) ≤ x⁻¹ ∧ x⁻¹ ≤ ((I.lo⁻¹:ℚ):ℝ)
  rw [Rat.cast_inv,Rat.cast_inv]
  rcases hI with hp|hn
  · have hl : (0:ℝ) < I.lo := by exact_mod_cast hp
    have hx0 : 0 < x := hl.trans_le hx.1
    have hh : (0:ℝ) < I.hi := hx0.trans_le hx.2
    exact ⟨(inv_le_inv₀ hh hx0).mpr hx.2,(inv_le_inv₀ hx0 hl).mpr hx.1⟩
  · have hh : (I.hi:ℝ) < 0 := by exact_mod_cast hn
    have hx0 : x < 0 := hx.2.trans_lt hh
    have hl : (I.lo:ℝ) < 0 := hx.1.trans_lt hx0
    exact ⟨(inv_le_inv_of_neg hh hx0).mpr hx.2,(inv_le_inv_of_neg hx0 hl).mpr hx.1⟩

theorem RatInterval.contains_widen (I J : RatInterval) (x : ℝ) (hx : I.Contains x)
    (hlo : J.lo ≤ I.lo) (hhi : I.hi ≤ J.hi) : J.Contains x := by
  have hl : (J.lo:ℝ) ≤ I.lo := by exact_mod_cast hlo
  have hh : (I.hi:ℝ) ≤ J.hi := by exact_mod_cast hhi
  exact ⟨hl.trans hx.1,hx.2.trans hh⟩

end GaussLocalMaxColoring.Certificate
end

section
-- Source module: Solutions.GaussLocalMaxCertificateExpr

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace GaussLocalMaxColoring.Certificate

instance (I : RatInterval) : Decidable I.AwayZero := by
  unfold RatInterval.AwayZero
  infer_instance

inductive BoxExpr (m : ℕ) where
  | lit (q : ℚ)
  | var (i : Fin m)
  | add (I : RatInterval) (a b : BoxExpr m)
  | neg (I : RatInterval) (a : BoxExpr m)
  | mul (I : RatInterval) (a b : BoxExpr m)
  | inv (I : RatInterval) (a : BoxExpr m)
  | sqrt (I : RatInterval) (a : BoxExpr m)
  deriving Repr

def BoxExpr.bounds {m : ℕ} (box : Fin m→RatInterval) : BoxExpr m→RatInterval
  | .lit q => RatInterval.point q
  | .var i => box i
  | .add I _ _ | .neg I _ | .mul I _ _ | .inv I _ | .sqrt I _ => I

noncomputable def BoxExpr.eval {m : ℕ} (x : Fin m→ℝ) : BoxExpr m→ℝ
  | .lit q => q
  | .var i => x i
  | .add _ a b => a.eval x+b.eval x
  | .neg _ a => -(a.eval x)
  | .mul _ a b => a.eval x*b.eval x
  | .inv _ a => (a.eval x)⁻¹
  | .sqrt _ a => Real.sqrt (a.eval x)

def BoxExpr.check {m : ℕ} (box : Fin m→RatInterval) : BoxExpr m→Bool
  | .lit _ | .var _ => true
  | .add I a b => a.check box && b.check box && decide
      (I.lo ≤ ((a.bounds box).add (b.bounds box)).lo ∧ ((a.bounds box).add (b.bounds box)).hi ≤ I.hi)
  | .neg I a => a.check box && decide (I.lo ≤ (a.bounds box).neg.lo ∧ (a.bounds box).neg.hi ≤ I.hi)
  | .mul I a b => a.check box && b.check box && decide
      (I.lo ≤ ((a.bounds box).mul (b.bounds box)).lo ∧ ((a.bounds box).mul (b.bounds box)).hi ≤ I.hi)
  | .inv I a => a.check box && decide ((a.bounds box).AwayZero ∧ I.lo ≤ (a.bounds box).inv.lo ∧ (a.bounds box).inv.hi ≤ I.hi)
  | .sqrt I a => a.check box && decide
      (0 < (a.bounds box).lo ∧ 0 ≤ I.lo ∧ 0 ≤ I.hi ∧ I.lo^2 ≤ (a.bounds box).lo ∧ (a.bounds box).hi ≤ I.hi^2)

theorem BoxExpr.check_sound {m : ℕ} (e : BoxExpr m) (box : Fin m→RatInterval)
    (x : Fin m→ℝ) (hx : ∀i,(box i).Contains (x i)) (he : e.check box=true) :
    (e.bounds box).Contains (e.eval x) := by
  induction e with
  | lit q => exact RatInterval.contains_point q
  | var i => exact hx i
  | add I a b ha hb =>
      simp only [check,Bool.and_eq_true,decide_eq_true_eq] at he
      exact RatInterval.contains_widen _ I _
        (RatInterval.contains_add _ _ _ _ (ha he.1.1) (hb he.1.2)) he.2.1 he.2.2
  | neg I a ha =>
      simp only [check,Bool.and_eq_true,decide_eq_true_eq] at he
      exact RatInterval.contains_widen _ I _ (RatInterval.contains_neg _ _ (ha he.1)) he.2.1 he.2.2
  | mul I a b ha hb =>
      simp only [check,Bool.and_eq_true,decide_eq_true_eq] at he
      exact RatInterval.contains_widen _ I _
        (RatInterval.contains_mul _ _ _ _ (ha he.1.1) (hb he.1.2)) he.2.1 he.2.2
  | inv I a ha =>
      simp only [check,Bool.and_eq_true,decide_eq_true_eq] at he
      exact RatInterval.contains_widen _ I _ (RatInterval.contains_inv _ _ (ha he.1) he.2.1) he.2.2.1 he.2.2.2
  | sqrt I a ha =>
      simp only [check,Bool.and_eq_true,decide_eq_true_eq] at he
      exact RatInterval.contains_sqrt_of_checks _ I _ (ha he.1) he.2.2.1 he.2.2.2.1 he.2.2.2.2.1 he.2.2.2.2.2

theorem BoxExpr.check_contDiffAt {m : ℕ} (e : BoxExpr m) (box : Fin m→RatInterval)
    (x : Fin m→ℝ) (hx : ∀i,(box i).Contains (x i)) (he : e.check box=true) :
    ContDiffAt ℝ ⊤ (fun y => e.eval y) x := by
  induction e with
  | lit q => exact contDiffAt_const
  | var i => exact (contDiff_apply ℝ ℝ i).contDiffAt
  | add I a b ha hb =>
      simp only [check,Bool.and_eq_true,decide_eq_true_eq] at he
      exact (ha he.1.1).add (hb he.1.2)
  | neg I a ha =>
      simp only [check,Bool.and_eq_true,decide_eq_true_eq] at he
      exact (ha he.1).neg
  | mul I a b ha hb =>
      simp only [check,Bool.and_eq_true,decide_eq_true_eq] at he
      exact (ha he.1.1).mul (hb he.1.2)
  | inv I a ha =>
      simp only [check,Bool.and_eq_true,decide_eq_true_eq] at he
      have hn := RatInterval.contains_ne_zero _ _ (BoxExpr.check_sound a box x hx he.1) he.2.1
      exact (ha he.1).inv hn
  | sqrt I a ha =>
      simp only [check,Bool.and_eq_true,decide_eq_true_eq] at he
      have hb := BoxExpr.check_sound a box x hx he.1
      have hp : (0:ℝ) < (a.bounds box).lo := by exact_mod_cast he.2.1
      have hn : a.eval x≠0 := (hp.trans_le hb.1).ne'
      exact (ha he.1).sqrt hn

end GaussLocalMaxColoring.Certificate
end

section
-- Source module: Solutions.GaussLocalMaxCertificateDifferentiation

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace GaussLocalMaxColoring.Certificate

/-- The exact rational expression underlying a checked interval expression. -/
inductive CertificateFormula (m : ℕ) where
  | lit (q : ℚ)
  | var (i : Fin m)
  | add (a b : CertificateFormula m)
  | neg (a : CertificateFormula m)
  | mul (a b : CertificateFormula m)
  | inv (a : CertificateFormula m)
  | sqrt (a : CertificateFormula m)
  deriving DecidableEq, Repr

namespace CertificateFormula

noncomputable def eval {m : ℕ} (x : Fin m → ℝ) : CertificateFormula m → ℝ
  | .lit q => q
  | .var i => x i
  | .add a b => a.eval x + b.eval x
  | .neg a => -(a.eval x)
  | .mul a b => a.eval x * b.eval x
  | .inv a => (a.eval x)⁻¹
  | .sqrt a => Real.sqrt (a.eval x)

def regular {m : ℕ} (x : Fin m → ℝ) : CertificateFormula m → Prop
  | .lit _ | .var _ => True
  | .add a b | .mul a b => a.regular x ∧ b.regular x
  | .neg a => a.regular x
  | .inv a => a.regular x ∧ a.eval x ≠ 0
  | .sqrt a => a.regular x ∧ 0 < a.eval x

/-- Symbolic pdiff differentiation; its correctness is proved below. -/
def pdiff {m : ℕ} (i : Fin m) : CertificateFormula m → CertificateFormula m
  | .lit _ => .lit 0
  | .var j => if j = i then .lit 1 else .lit 0
  | .add a b => .add (a.pdiff i) (b.pdiff i)
  | .neg a => .neg (a.pdiff i)
  | .mul a b => .add (.mul (a.pdiff i) b) (.mul a (b.pdiff i))
  | .inv a => .neg (.mul (a.pdiff i) (.inv (.mul a a)))
  | .sqrt a => .mul (a.pdiff i) (.inv (.mul (.lit 2) (.sqrt a)))

theorem regular_pdiff {m : ℕ} (e : CertificateFormula m) (x : Fin m → ℝ)
    (i : Fin m) (he : e.regular x) : (e.pdiff i).regular x := by
  induction e with
  | lit q => trivial
  | var j => simp only [pdiff]; split <;> trivial
  | add a b ha hb => exact ⟨ha he.1, hb he.2⟩
  | neg a ha => exact ha he
  | mul a b ha hb => exact ⟨⟨ha he.1, he.2⟩, ⟨he.1, hb he.2⟩⟩
  | inv a ha =>
      exact ⟨ha he.1, ⟨⟨he.1, he.1⟩, mul_ne_zero he.2 he.2⟩⟩
  | sqrt a ha =>
      exact ⟨ha he.1, ⟨⟨True.intro, he⟩,
        mul_ne_zero (by norm_num [eval]) (ne_of_gt (Real.sqrt_pos.mpr he.2))⟩⟩

theorem hasDerivAt_eval {m : ℕ} (e : CertificateFormula m)
    (x : ℝ → Fin m → ℝ) (v : Fin m → ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (v i) t)
    (he : e.regular (x t)) :
    HasDerivAt (fun s => e.eval (x s))
      (∑ i, (e.pdiff i).eval (x t) * v i) t := by
  induction e with
  | lit q =>
      simpa [pdiff, eval] using hasDerivAt_const t (q:ℝ)
  | var j =>
      have hsum : (∑ i, eval (x t) (pdiff i (.var j)) * v i) = v j := by
        simp only [pdiff, apply_ite (eval (x t)), eval]
        simp
      rw [hsum]
      exact hx j
  | add a b ha hb =>
      have hh := (ha he.1).add (hb he.2)
      apply hh.congr_deriv
      simp [pdiff, eval, add_mul, Finset.sum_add_distrib]
  | neg a ha =>
      have hh := (ha he).neg
      apply hh.congr_deriv
      simp [pdiff, eval, Finset.sum_neg_distrib]
  | mul a b ha hb =>
      have hh := (ha he.1).mul (hb he.2)
      apply hh.congr_deriv
      simp only [pdiff, eval, add_mul, Finset.sum_add_distrib]
      rw [Finset.sum_mul, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
  | inv a ha =>
      have hh := (ha he.1).inv he.2
      apply hh.congr_deriv
      simp only [pdiff, eval]
      rw [div_eq_mul_inv, ← Finset.sum_neg_distrib, Finset.sum_mul]
      simp only [pow_two]
      apply Finset.sum_congr rfl
      intro i hi
      ring
  | sqrt a ha =>
      have hh := (ha he.1).sqrt (ne_of_gt he.2)
      apply hh.congr_deriv
      simp only [pdiff, eval]
      rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

noncomputable def line {m : ℕ} (center δ : Fin m → ℝ) (t : ℝ) : Fin m → ℝ :=
  fun i => center i + t * δ i

theorem hasDerivAt_line {m : ℕ} (e : CertificateFormula m)
    (center δ : Fin m → ℝ) (t : ℝ) (he : e.regular (line center δ t)) :
    HasDerivAt (fun s => e.eval (line center δ s))
      (∑ i, (e.pdiff i).eval (line center δ t) * δ i) t := by
  apply hasDerivAt_eval e _ δ t _ he
  intro i
  have hh := ((hasDerivAt_id t).mul_const (δ i)).const_add (center i)
  change HasDerivAt (fun s => center i + s * δ i) (1 * δ i) t at hh
  simpa only [line, one_mul] using hh

/-- The second derivative on a line is the quadratic form of the symbolic Hessian. -/
theorem hasDerivAt_line_gradient {m : ℕ} (e : CertificateFormula m)
    (center δ : Fin m → ℝ) (t : ℝ) (he : e.regular (line center δ t)) :
    HasDerivAt (fun s => ∑ i, (e.pdiff i).eval (line center δ s) * δ i)
      (∑ i, ∑ j, ((e.pdiff i).pdiff j).eval (line center δ t) * δ i * δ j) t := by
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((e.pdiff i).hasDerivAt_line center δ t (e.regular_pdiff _ i he)).mul_const (δ i))
  apply hh.congr_deriv
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end CertificateFormula

def BoxExpr.formula {m : ℕ} : BoxExpr m → CertificateFormula m
  | .lit q => .lit q
  | .var i => .var i
  | .add _ a b => .add a.formula b.formula
  | .neg _ a => .neg a.formula
  | .mul _ a b => .mul a.formula b.formula
  | .inv _ a => .inv a.formula
  | .sqrt _ a => .sqrt a.formula

theorem BoxExpr.formula_eval {m : ℕ} (e : BoxExpr m) (x : Fin m → ℝ) :
    e.formula.eval x = e.eval x := by
  induction e <;> simp_all only [formula, CertificateFormula.eval, BoxExpr.eval]

theorem BoxExpr.check_regular {m : ℕ} (e : BoxExpr m) (box : Fin m → RatInterval)
    (x : Fin m → ℝ) (hx : ∀ i, (box i).Contains (x i)) (he : e.check box = true) :
    e.formula.regular x := by
  induction e with
  | lit q => trivial
  | var i => trivial
  | add I a b ha hb =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at he
      exact ⟨ha he.1.1, hb he.1.2⟩
  | neg I a ha =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at he
      exact ha he.1
  | mul I a b ha hb =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at he
      exact ⟨ha he.1.1, hb he.1.2⟩
  | inv I a ha =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at he
      refine ⟨ha he.1, ?_⟩
      rw [formula_eval]
      exact RatInterval.contains_ne_zero _ _ (a.check_sound box x hx he.1) he.2.1
  | sqrt I a ha =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at he
      refine ⟨ha he.1, ?_⟩
      rw [formula_eval]
      have hpos : (0:ℝ) < (a.bounds box).lo := by exact_mod_cast he.2.1
      exact hpos.trans_le (a.check_sound box x hx he.1).1

theorem BoxExpr.checked_line_derivatives {m : ℕ} (e : BoxExpr m)
    (box : Fin m → RatInterval) (center δ : Fin m → ℝ) (t : ℝ)
    (hx : ∀ i, (box i).Contains (CertificateFormula.line center δ t i))
    (he : e.check box = true) :
    HasDerivAt (fun s => e.eval (CertificateFormula.line center δ s))
        (∑ i, (e.formula.pdiff i).eval (CertificateFormula.line center δ t) * δ i) t ∧
      HasDerivAt (fun s => ∑ i,
        (e.formula.pdiff i).eval (CertificateFormula.line center δ s) * δ i)
        (∑ i, ∑ j, ((e.formula.pdiff i).pdiff j).eval
          (CertificateFormula.line center δ t) * δ i * δ j) t := by
  have hregular := e.check_regular box _ hx he
  constructor
  · simpa only [formula_eval] using e.formula.hasDerivAt_line center δ t hregular
  · exact e.formula.hasDerivAt_line_gradient center δ t hregular


end GaussLocalMaxColoring.Certificate
end

section
-- Source module: Solutions.GaussLocalMaxCertificateTaylor

set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped Topology
open Filter

namespace GaussLocalMaxColoring.Certificate
noncomputable section

theorem second_order_lower_on_unit (f g h : ℝ→ℝ) (K : ℝ)
    (hf : ∀x∈Set.Icc (0:ℝ) 1,HasDerivAt f (g x) x)
    (hg : ∀x∈Set.Icc (0:ℝ) 1,HasDerivAt g (h x) x)
    (hK : ∀x∈Set.Icc (0:ℝ) 1,K ≤ h x) :
    f 0+g 0+K/2 ≤ f 1 := by
  let Q : ℝ→ℝ := fun x => g x-K*x
  have hQ : ∀x∈Set.Icc (0:ℝ) 1,HasDerivAt Q (h x-K) x := by
    intro x hx
    have hh := (hg x hx).sub ((hasDerivAt_id x).const_mul K)
    change HasDerivAt Q (h x-K*1) x at hh
    simpa only [mul_one] using hh
  have hQmono : MonotoneOn Q (Set.Icc (0:ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) 1)
    · intro x hx
      exact (hQ x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hQ x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      exact sub_nonneg.mpr (hK x (interior_subset hx))
  have hglower : ∀x∈Set.Icc (0:ℝ) 1,g 0+K*x ≤ g x := by
    intro x hx
    have hh := hQmono (by constructor <;> norm_num) hx hx.1
    change g 0-K*0 ≤ g x-K*x at hh
    linarith only [hh]
  let F : ℝ→ℝ := fun x => f x-f 0-g 0*x-K*x^2/2
  have hF : ∀x∈Set.Icc (0:ℝ) 1,HasDerivAt F (g x-g 0-K*x) x := by
    intro x hx
    have hh := (((hf x hx).sub_const (f 0)).sub ((hasDerivAt_id x).const_mul (g 0))).sub
      (((hasDerivAt_pow 2 x).const_mul K).div_const 2)
    change HasDerivAt (fun y => f y-f 0-g 0*y-K*y^2/2)
      (g x-g 0*1-K*((2:ℝ)*x^(2-1))/2) x at hh
    convert hh using 1 <;> ring
  have hFmono : MonotoneOn F (Set.Icc (0:ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) 1)
    · intro x hx
      exact (hF x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hF x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      have hh := hglower x (interior_subset hx)
      linarith only [hh]
  have hh := hFmono (show (0:ℝ)∈Set.Icc (0:ℝ) 1 from ⟨le_rfl,by norm_num⟩)
    (show (1:ℝ)∈Set.Icc (0:ℝ) 1 from ⟨by norm_num,le_rfl⟩) (by norm_num)
  dsimp only [F] at hh
  norm_num only [zero_pow,one_pow,mul_zero,mul_one,zero_div,sub_self] at hh
  linarith only [hh]

end
end GaussLocalMaxColoring.Certificate
end

section
-- Source module: Solutions.GaussLocalMaxCertificateQuadratic

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace GaussLocalMaxColoring.Certificate

def ratMinQuadratic (a g r : ℚ) : ℚ :=
  if r=0 then 0 else if 0 < a ∧ g ≤ 2*a*r then -(g*g)/(4*a) else a*r*r-g*r

theorem ratMinQuadratic_lower (a g r : ℚ) (hg : 0 ≤ g) (hr : 0 ≤ r)
    (u : ℝ) (hu : 0 ≤ u) (hur : u ≤ (r:ℝ)) :
    (ratMinQuadratic a g r:ℝ) ≤ (a:ℝ)*u^2-(g:ℝ)*u := by
  have hgR : (0:ℝ) ≤ g := by exact_mod_cast hg
  have hrR : (0:ℝ) ≤ r := by exact_mod_cast hr
  unfold ratMinQuadratic
  split
  · rename_i hr0
    subst r
    norm_num only [Rat.cast_zero] at hur
    have hu0 : u=0 := le_antisymm hur hu
    subst u
    norm_num
  · split
    · rename_i hc
      have haR : (0:ℝ) < a := by exact_mod_cast hc.1
      push_cast
      apply (div_le_iff₀ (show 0 < 4*(a:ℝ) by positivity)).mpr
      nlinarith only [sq_nonneg (2*(a:ℝ)*u-(g:ℝ))]
    · rename_i hc
      push_cast
      have hfac : 0 ≤ (g:ℝ)-(a:ℝ)*((r:ℝ)+u) := by
        by_cases ha : a ≤ 0
        · have haR : (a:ℝ) ≤ 0 := by exact_mod_cast ha
          have hh := mul_nonpos_of_nonpos_of_nonneg haR (add_nonneg hrR hu)
          linarith only [hgR,hh]
        · have haPos : 0 < a := lt_of_not_ge ha
          have hgGt : 2*a*r < g := lt_of_not_ge (fun hh => hc ⟨haPos,hh⟩)
          have hgGtR : 2*(a:ℝ)*(r:ℝ) < g := by exact_mod_cast hgGt
          have haR : (0:ℝ) < a := by exact_mod_cast haPos
          have hm := mul_le_mul_of_nonneg_left hur haR.le
          linarith only [hgGtR,hm]
      have hh := mul_nonneg (sub_nonneg.mpr hur) hfac
      nlinarith only [hh]

theorem weighted_cross_bound (p q x y : ℝ) (hp : 0 < p) (hq : 0 < q) :
    2*|x*y| ≤ (q/p)*x^2+(p/q)*y^2 := by
  have he : (q/p)*x^2+(p/q)*y^2=(q^2*x^2+p^2*y^2)/(p*q) := by
    field_simp [hp.ne',hq.ne']
    <;> ring
  rw [he]
  apply (le_div_iff₀ (mul_pos hp hq)).mpr
  rw [abs_mul]
  have hs := sq_nonneg (q*|x|-p*|y|)
  rw [sub_sq,mul_pow,mul_pow,sq_abs,sq_abs] at hs
  nlinarith only [hs]

theorem mixed_term_lower (h M p q x y : ℝ) (hp : 0 < p) (hq : 0 < q) (hM : |h| ≤ M) :
    -(M/2)*((q/p)*x^2+(p/q)*y^2) ≤ h*x*y := by
  have hM0 : 0 ≤ M := (abs_nonneg h).trans hM
  have hw := mul_le_mul_of_nonneg_left (weighted_cross_bound p q x y hp hq) hM0
  have hh := neg_abs_le (h*x*y)
  rw [abs_mul,abs_mul] at hh
  have hb := mul_le_mul_of_nonneg_right hM (mul_nonneg (abs_nonneg x) (abs_nonneg y))
  rw [abs_mul] at hw
  nlinarith only [hw,hh,hb]

end GaussLocalMaxColoring.Certificate
end

section
-- Source module: Solutions.GaussLocalMaxCertificateFiniteTaylor

set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped BigOperators

namespace GaussLocalMaxColoring.Certificate
noncomputable section

theorem finite_taylor_lower {m : ℕ} (f g h : ℝ→ℝ)
    (centerLo : ℚ) (a G r : Fin m→ℚ) (δ grad : Fin m→ℝ)
    (hf : ∀x∈Set.Icc (0:ℝ) 1,HasDerivAt f (g x) x)
    (hg : ∀x∈Set.Icc (0:ℝ) 1,HasDerivAt g (h x) x)
    (hcenter : (centerLo:ℝ) ≤ f 0)
    (hfirst : g 0=∑i,grad i*δ i)
    (hgrad : ∀i,|grad i| ≤ (G i:ℝ))
    (hG : ∀i,0 ≤ G i) (hr : ∀i,0 ≤ r i) (hδ : ∀i,|δ i| ≤ (r i:ℝ))
    (hsecond : ∀x∈Set.Icc (0:ℝ) 1,2*(∑i,(a i:ℝ)*(δ i)^2) ≤ h x) :
    ((centerLo+∑i,ratMinQuadratic (a i) (G i) (r i):ℚ):ℝ) ≤ f 1 := by
  have hT := second_order_lower_on_unit f g h (2*(∑i,(a i:ℝ)*(δ i)^2)) hf hg hsecond
  rw [hfirst] at hT
  have heach (i : Fin m) : (ratMinQuadratic (a i) (G i) (r i):ℝ) ≤
      (a i:ℝ)*(δ i)^2+grad i*δ i := by
    have hmin := ratMinQuadratic_lower (a i) (G i) (r i) (hG i) (hr i) |δ i| (abs_nonneg _) (hδ i)
    rw [sq_abs] at hmin
    have hh := neg_abs_le (grad i*δ i)
    rw [abs_mul] at hh
    have hm := mul_le_mul_of_nonneg_right (hgrad i) (abs_nonneg (δ i))
    linarith only [hmin,hh,hm]
  have hsum := Finset.sum_le_sum (fun (i : Fin m) (_ : i∈Finset.univ) => heach i)
  rw [Finset.sum_add_distrib] at hsum
  push_cast
  linarith only [hcenter,hsum,hT]

end
end GaussLocalMaxColoring.Certificate
end

section
-- Source module: Solutions.GaussLocalMaxCertificateTaylorOne

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace GaussLocalMaxColoring.Certificate

def RatInterval.absmax (I : RatInterval) : ℚ := max |I.lo| |I.hi|

theorem RatInterval.absmax_nonneg (I : RatInterval) : 0 ≤ I.absmax :=
  (abs_nonneg I.lo).trans (le_max_left _ _)

theorem RatInterval.contains_abs {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    |x| ≤ (I.absmax:ℝ) := by
  have hlo : |(I.lo:ℝ)| ≤ (I.absmax:ℝ) := by
    exact_mod_cast (le_max_left |I.lo| |I.hi|)
  have hhi : |(I.hi:ℝ)| ≤ (I.absmax:ℝ) := by
    exact_mod_cast (le_max_right |I.lo| |I.hi|)
  exact abs_le.mpr ⟨(neg_le_of_abs_le hlo).trans hx.1, hx.2.trans (le_of_abs_le hhi)⟩

/-- A rational interval/Taylor certificate for one exact expression in one variable. -/
structure TaylorCertificate1 where
  center : ℚ
  radius : ℚ
  whole : BoxExpr 1
  centerValue : BoxExpr 1
  gradient : BoxExpr 1
  hessian : BoxExpr 1

namespace TaylorCertificate1

def box (c : TaylorCertificate1) : Fin 1 → RatInterval :=
  fun _ => ⟨c.center-c.radius, c.center+c.radius⟩

def centerBox (c : TaylorCertificate1) : Fin 1 → RatInterval :=
  fun _ => RatInterval.point c.center

def lower (c : TaylorCertificate1) : ℚ :=
  (c.centerValue.bounds c.centerBox).lo + ratMinQuadratic
    ((c.hessian.bounds c.box).lo / 2) (c.gradient.bounds c.centerBox).absmax c.radius

def check (c : TaylorCertificate1) : Bool :=
  c.whole.check c.box && c.centerValue.check c.centerBox &&
    c.gradient.check c.centerBox && c.hessian.check c.box && decide
      (0 ≤ c.radius ∧ c.centerValue.formula = c.whole.formula ∧
        c.gradient.formula = c.whole.formula.pdiff 0 ∧
        c.hessian.formula = (c.whole.formula.pdiff 0).pdiff 0)

theorem line_contains (c : TaylorCertificate1) (x t : ℝ)
    (hx : (c.center-c.radius:ℚ) ≤ x ∧ x ≤ (c.center+c.radius:ℚ))
    (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∀ i, (c.box i).Contains
      (CertificateFormula.line (fun _ => (c.center:ℝ)) (fun _ => x-c.center) t i) := by
  intro i
  have hxlo : (c.center:ℝ) - c.radius ≤ x := by exact_mod_cast hx.1
  have hxhi : x ≤ (c.center:ℝ) + c.radius := by exact_mod_cast hx.2
  have hp := mul_le_mul_of_nonneg_left (show x-(c.center:ℝ) ≤ c.radius by linarith) ht.1
  have hm := mul_le_mul_of_nonneg_left (show -(c.radius:ℝ) ≤ x-c.center by linarith) ht.1
  have hr : (0:ℝ) ≤ c.radius := by linarith only [hxlo, hxhi]
  have htr := mul_le_mul_of_nonneg_right ht.2 hr
  change ((c.center-c.radius:ℚ):ℝ) ≤ (c.center:ℝ)+t*(x-c.center) ∧
    (c.center:ℝ)+t*(x-c.center) ≤ ((c.center+c.radius:ℚ):ℝ)
  push_cast
  constructor <;> nlinarith only [hp, hm, htr]

theorem lower_sound (c : TaylorCertificate1) (hc : c.check = true)
    (x : ℝ) (hx : (c.center-c.radius:ℚ) ≤ x ∧ x ≤ (c.center+c.radius:ℚ)) :
    (c.lower:ℝ) ≤ c.whole.eval (fun _ => x) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨⟨⟨he, hcenter⟩, hgrad⟩, hhess⟩, hr, hceq, hgeq, hheq⟩
  let z : Fin 1 → ℝ := fun _ => c.center
  let δ : Fin 1 → ℝ := fun _ => x-c.center
  let f : ℝ → ℝ := fun t => c.whole.eval (CertificateFormula.line z δ t)
  let g : ℝ → ℝ := fun t => ∑ i,
    (c.whole.formula.pdiff i).eval (CertificateFormula.line z δ t) * δ i
  let h : ℝ → ℝ := fun t => ∑ i, ∑ j,
    ((c.whole.formula.pdiff i).pdiff j).eval (CertificateFormula.line z δ t) * δ i * δ j
  have hder (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      HasDerivAt f (g t) t ∧ HasDerivAt g (h t) t :=
    c.whole.checked_line_derivatives c.box z δ t (c.line_contains x t hx ht) he
  have hz : ∀ i, (c.centerBox i).Contains (z i) := by
    intro i
    exact RatInterval.contains_point _
  have hcval := c.centerValue.check_sound c.centerBox z hz hcenter
  have hgval := c.gradient.check_sound c.centerBox z hz hgrad
  have hcenterEq : c.centerValue.eval z = c.whole.eval z := by
    rw [← BoxExpr.formula_eval, hceq, BoxExpr.formula_eval]
  have hgradEq : c.gradient.eval z = (c.whole.formula.pdiff 0).eval z := by
    rw [← BoxExpr.formula_eval, hgeq]
  have hdelta : |x-(c.center:ℝ)| ≤ (c.radius:ℝ) := by
    have hxlo : (c.center:ℝ) - c.radius ≤ x := by exact_mod_cast hx.1
    have hxhi : x ≤ (c.center:ℝ) + c.radius := by exact_mod_cast hx.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsecond (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      (c.hessian.bounds c.box).lo * (x-c.center)^2 ≤ h t := by
    have hhv := c.hessian.check_sound c.box (CertificateFormula.line z δ t)
      (c.line_contains x t hx ht) hhess
    have hheval : c.hessian.eval (CertificateFormula.line z δ t) =
        ((c.whole.formula.pdiff 0).pdiff 0).eval (CertificateFormula.line z δ t) := by
      rw [← BoxExpr.formula_eval, hheq]
    rw [hheval] at hhv
    have hm := mul_le_mul_of_nonneg_right hhv.1 (sq_nonneg (x-c.center))
    simpa only [h, Fin.sum_univ_one, δ, pow_two, mul_assoc] using hm
  have hT := second_order_lower_on_unit f g h
    ((c.hessian.bounds c.box).lo * (x-c.center)^2)
    (fun t ht => (hder t ht).1) (fun t ht => (hder t ht).2) hsecond
  have hmin := ratMinQuadratic_lower ((c.hessian.bounds c.box).lo/2)
    (c.gradient.bounds c.centerBox).absmax c.radius
    (RatInterval.absmax_nonneg _) hr |x-c.center| (abs_nonneg _) hdelta
  have hgabs := RatInterval.contains_abs hgval
  rw [hgradEq] at hgabs
  have hmul := mul_le_mul_of_nonneg_right hgabs (abs_nonneg (x-c.center))
  have hneg := neg_abs_le ((c.whole.formula.pdiff 0).eval z * (x-c.center))
  rw [abs_mul] at hneg
  rw [sq_abs] at hmin
  rw [hcenterEq] at hcval
  have hline0 : CertificateFormula.line z δ 0 = z := by
    funext i
    dsimp only [CertificateFormula.line]
    ring
  have hline1 : CertificateFormula.line z δ 1 = (fun _ => x) := by
    funext i
    dsimp only [CertificateFormula.line, z, δ]
    ring
  have hf0 : f 0 = c.whole.eval z := by
    change c.whole.eval (CertificateFormula.line z δ 0) = _
    rw [hline0]
  have hf1 : f 1 = c.whole.eval (fun _ => x) := by
    change c.whole.eval (CertificateFormula.line z δ 1) = _
    rw [hline1]
  have hg0 : g 0 = (c.whole.formula.pdiff 0).eval z * (x-c.center) := by
    simp only [g, Fin.sum_univ_one, hline0, δ]
  rw [hf0, hf1, hg0] at hT
  unfold lower
  push_cast at hmin ⊢
  nlinarith only [hT, hmin, hmul, hneg, hcval.1]

theorem positive_sound (c : TaylorCertificate1) (hc : c.check = true) (hl : 0 < c.lower)
    (x : ℝ) (hx : (c.center-c.radius:ℚ) ≤ x ∧ x ≤ (c.center+c.radius:ℚ)) :
    0 < c.whole.eval (fun _ => x) := by
  have hpos : (0:ℝ) < c.lower := by exact_mod_cast hl
  exact hpos.trans_le (c.lower_sound hc x hx)


end TaylorCertificate1
end GaussLocalMaxColoring.Certificate
end

section
-- Source module: Solutions.GaussLocalMaxCertificateHessianThree

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace GaussLocalMaxColoring.Certificate

/-- The off-diagonal AM-GM penalty; a fixed coordinate has zero penalty. -/
def crossPenalty (M p q : ℚ) : ℚ :=
  if p = 0 ∨ q = 0 then 0 else M*q/p

theorem cross_pair_lower (M p q : ℚ) (a b x y : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hx : |x| ≤ (p:ℝ)) (hy : |y| ≤ (q:ℝ))
    (ha : |a| ≤ (M:ℝ)) (hb : |b| ≤ (M:ℝ)) :
    -(crossPenalty M p q:ℝ)*x^2 - (crossPenalty M q p:ℝ)*y^2 ≤
      a*x*y + b*y*x := by
  by_cases hp0 : p = 0
  · subst p
    norm_num only [Rat.cast_zero] at hx
    have hx0 : x = 0 := by have hh := abs_le.mp hx; linarith
    subst x
    simp [crossPenalty]
  by_cases hq0 : q = 0
  · subst q
    norm_num only [Rat.cast_zero] at hy
    have hy0 : y = 0 := by have hh := abs_le.mp hy; linarith
    subst y
    simp [crossPenalty]
  have hpR : (0:ℝ) < p := by exact_mod_cast lt_of_le_of_ne hp (Ne.symm hp0)
  have hqR : (0:ℝ) < q := by exact_mod_cast lt_of_le_of_ne hq (Ne.symm hq0)
  have h1 := mixed_term_lower a M p q x y hpR hqR ha
  have h2 := mixed_term_lower b M p q x y hpR hqR hb
  simp only [crossPenalty, if_neg (show ¬ (p = 0 ∨ q = 0) from not_or.mpr ⟨hp0,hq0⟩),
    if_neg (show ¬ (q = 0 ∨ p = 0) from not_or.mpr ⟨hq0,hp0⟩)]
  push_cast
  calc
    -((M:ℝ)*q/p)*x^2 - ((M:ℝ)*p/q)*y^2 =
        -((M:ℝ)/2)*(((q:ℝ)/p)*x^2+((p:ℝ)/q)*y^2) +
        -((M:ℝ)/2)*(((q:ℝ)/p)*x^2+((p:ℝ)/q)*y^2) := by ring
    _ ≤ a*x*y+b*x*y := add_le_add h1 h2
    _ = a*x*y+b*y*x := by ring

def hessianAbsPair (H : Fin 3 → Fin 3 → RatInterval) (i j : Fin 3) : ℚ :=
  max (H i j).absmax (H j i).absmax

def hessianDiagonal3 (H : Fin 3 → Fin 3 → RatInterval) (r : Fin 3 → ℚ) : Fin 3 → ℚ :=
  ![((H 0 0).lo-crossPenalty (hessianAbsPair H 0 1) (r 0) (r 1)-
      crossPenalty (hessianAbsPair H 0 2) (r 0) (r 2))/2,
    ((H 1 1).lo-crossPenalty (hessianAbsPair H 0 1) (r 1) (r 0)-
      crossPenalty (hessianAbsPair H 1 2) (r 1) (r 2))/2,
    ((H 2 2).lo-crossPenalty (hessianAbsPair H 0 2) (r 2) (r 0)-
      crossPenalty (hessianAbsPair H 1 2) (r 2) (r 1))/2]

/-- The paper's weighted diagonal Hessian lower bound, including zero radii. -/
theorem hessian_three_lower (H : Fin 3 → Fin 3 → RatInterval) (r : Fin 3 → ℚ)
    (K : Fin 3 → Fin 3 → ℝ) (δ : Fin 3 → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hδ : ∀ i, |δ i| ≤ (r i:ℝ))
    (hK : ∀ i j, (H i j).Contains (K i j)) :
    2*(∑ i, (hessianDiagonal3 H r i:ℝ)*(δ i)^2) ≤
      ∑ i, ∑ j, K i j * δ i * δ j := by
  have hleft (i j : Fin 3) : |K i j| ≤ (hessianAbsPair H i j:ℝ) :=
    (RatInterval.contains_abs (hK i j)).trans (by
      exact_mod_cast (le_max_left (H i j).absmax (H j i).absmax))
  have hright (i j : Fin 3) : |K j i| ≤ (hessianAbsPair H i j:ℝ) :=
    (RatInterval.contains_abs (hK j i)).trans (by
      exact_mod_cast (le_max_right (H i j).absmax (H j i).absmax))
  have hp01 := cross_pair_lower (hessianAbsPair H 0 1) (r 0) (r 1)
    (K 0 1) (K 1 0) (δ 0) (δ 1) (hr 0) (hr 1) (hδ 0) (hδ 1) (hleft 0 1) (hright 0 1)
  have hp02 := cross_pair_lower (hessianAbsPair H 0 2) (r 0) (r 2)
    (K 0 2) (K 2 0) (δ 0) (δ 2) (hr 0) (hr 2) (hδ 0) (hδ 2) (hleft 0 2) (hright 0 2)
  have hp12 := cross_pair_lower (hessianAbsPair H 1 2) (r 1) (r 2)
    (K 1 2) (K 2 1) (δ 1) (δ 2) (hr 1) (hr 2) (hδ 1) (hδ 2) (hleft 1 2) (hright 1 2)
  have hd0 := mul_le_mul_of_nonneg_right (hK 0 0).1 (sq_nonneg (δ 0))
  have hd1 := mul_le_mul_of_nonneg_right (hK 1 1).1 (sq_nonneg (δ 1))
  have hd2 := mul_le_mul_of_nonneg_right (hK 2 2).1 (sq_nonneg (δ 2))
  norm_num [Fin.sum_univ_three, hessianDiagonal3, Matrix.cons_val_two]
  nlinarith only [hp01,hp02,hp12,hd0,hd1,hd2]


end GaussLocalMaxColoring.Certificate
end

section
-- Source module: Solutions.GaussLocalMaxCertificateNormalize

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace GaussLocalMaxColoring.Certificate.CertificateFormula

def smartAdd {m : ℕ} (a b : CertificateFormula m) : CertificateFormula m :=
  match a,b with
  | .lit x,.lit y => .lit (x+y)
  | .lit x,b => if x=0 then b else .add (.lit x) b
  | a,.lit y => if y=0 then a else .add a (.lit y)
  | a,b => .add a b

def smartMul {m : ℕ} (a b : CertificateFormula m) : CertificateFormula m :=
  match a,b with
  | .lit x,.lit y => .lit (x*y)
  | .lit x,b => if x=0 then .lit 0 else if x=1 then b else .mul (.lit x) b
  | a,.lit y => if y=0 then .lit 0 else if y=1 then a else .mul a (.lit y)
  | a,b => .mul a b

def smartNeg {m : ℕ} : CertificateFormula m → CertificateFormula m
  | .lit q => .lit (-q)
  | .neg a => a
  | a => .neg a

def smartInv {m : ℕ} : CertificateFormula m → CertificateFormula m
  | .lit q => .lit q⁻¹
  | a => .inv a

def normalize {m : ℕ} : CertificateFormula m → CertificateFormula m
  | .lit q => .lit q
  | .var i => .var i
  | .add a b => smartAdd a.normalize b.normalize
  | .mul a b => smartMul a.normalize b.normalize
  | .neg a => smartNeg a.normalize
  | .inv a => smartInv a.normalize
  | .sqrt a => .sqrt a.normalize

theorem smartAdd_eval {m : ℕ} (a b : CertificateFormula m) (x : Fin m → ℝ) :
    (smartAdd a b).eval x = a.eval x+b.eval x := by
  cases a <;> cases b <;> simp only [smartAdd,eval]
  all_goals first | rfl | push_cast
  all_goals try rfl
  all_goals split <;> simp_all [eval]

theorem smartMul_eval {m : ℕ} (a b : CertificateFormula m) (x : Fin m → ℝ) :
    (smartMul a b).eval x = a.eval x*b.eval x := by
  cases a <;> cases b <;> simp only [smartMul,eval]
  all_goals first | rfl | push_cast
  all_goals try rfl
  all_goals repeat' first | split | simp_all [eval]

theorem smartNeg_eval {m : ℕ} (a : CertificateFormula m) (x : Fin m → ℝ) :
    (smartNeg a).eval x = -a.eval x := by
  cases a <;> simp [smartNeg,eval]

theorem smartInv_eval {m : ℕ} (a : CertificateFormula m) (x : Fin m → ℝ) :
    (smartInv a).eval x = (a.eval x)⁻¹ := by
  cases a <;> simp [smartInv,eval]

theorem normalize_eval {m : ℕ} (a : CertificateFormula m) (x : Fin m → ℝ) :
    a.normalize.eval x = a.eval x := by
  induction a with
  | lit q => rfl
  | var i => rfl
  | add a b ha hb => simpa only [normalize,smartAdd_eval,ha,hb,eval]
  | mul a b ha hb => simpa only [normalize,smartMul_eval,ha,hb,eval]
  | neg a ha => simpa only [normalize,smartNeg_eval,ha,eval]
  | inv a ha => simpa only [normalize,smartInv_eval,ha,eval]
  | sqrt a ha => simp only [normalize,eval,ha]

end GaussLocalMaxColoring.Certificate.CertificateFormula
end

section
-- Source module: Solutions.GaussLocalMaxCertificateTaylorThreeReduced

set_option autoImplicit false
set_option maxHeartbeats 3000000

open scoped BigOperators

namespace GaussLocalMaxColoring.Certificate

/-- A sound three-variable Taylor certificate with normalized derivative formulas; the old checker is unchanged. -/
structure TaylorCertificate3Reduced where
  center : Fin 3 → ℚ
  radius : Fin 3 → ℚ
  whole : BoxExpr 3
  centerValue : BoxExpr 3
  gradient : Fin 3 → BoxExpr 3
  hessian : Fin 3 → Fin 3 → BoxExpr 3

namespace TaylorCertificate3Reduced

def box (c : TaylorCertificate3Reduced) : Fin 3 → RatInterval :=
  fun i => ⟨c.center i-c.radius i, c.center i+c.radius i⟩

def centerBox (c : TaylorCertificate3Reduced) : Fin 3 → RatInterval :=
  fun i => RatInterval.point (c.center i)

def hessianIntervals (c : TaylorCertificate3Reduced) : Fin 3 → Fin 3 → RatInterval :=
  fun i j => (c.hessian i j).bounds c.box

def diagonal (c : TaylorCertificate3Reduced) : Fin 3 → ℚ :=
  hessianDiagonal3 c.hessianIntervals c.radius

def gradientAbs (c : TaylorCertificate3Reduced) : Fin 3 → ℚ :=
  fun i => (c.gradient i |>.bounds c.centerBox).absmax

def lower (c : TaylorCertificate3Reduced) : ℚ :=
  (c.centerValue.bounds c.centerBox).lo +
    ∑ i, ratMinQuadratic (c.diagonal i) (c.gradientAbs i) (c.radius i)

def check (c : TaylorCertificate3Reduced) : Bool :=
  c.whole.check c.box && c.centerValue.check c.centerBox && decide
    ((∀ i, 0 ≤ c.radius i) ∧ c.centerValue.formula = c.whole.formula ∧
      (∀ i, (c.gradient i).check c.centerBox = true ∧
        (c.gradient i).formula = (c.whole.formula.pdiff i).normalize) ∧
      (∀ i j, (c.hessian i j).check c.box = true ∧
        (c.hessian i j).formula = ((c.whole.formula.pdiff i).pdiff j).normalize))

theorem line_contains (c : TaylorCertificate3Reduced) (x : Fin 3 → ℝ) (t : ℝ)
    (hx : ∀ i, (c.center i-c.radius i:ℚ) ≤ x i ∧ x i ≤ (c.center i+c.radius i:ℚ))
    (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∀ i, (c.box i).Contains (CertificateFormula.line
      (fun j => (c.center j:ℝ)) (fun j => x j-c.center j) t i) := by
  intro i
  have hxlo : (c.center i:ℝ)-c.radius i ≤ x i := by exact_mod_cast (hx i).1
  have hxhi : x i ≤ (c.center i:ℝ)+c.radius i := by exact_mod_cast (hx i).2
  have hr : (0:ℝ) ≤ c.radius i := by linarith only [hxlo,hxhi]
  have hp := mul_le_mul_of_nonneg_left
    (show x i-(c.center i:ℝ) ≤ c.radius i by linarith) ht.1
  have hm := mul_le_mul_of_nonneg_left
    (show -(c.radius i:ℝ) ≤ x i-c.center i by linarith) ht.1
  have htr := mul_le_mul_of_nonneg_right ht.2 hr
  change ((c.center i-c.radius i:ℚ):ℝ) ≤ (c.center i:ℝ)+t*(x i-c.center i) ∧
    (c.center i:ℝ)+t*(x i-c.center i) ≤ ((c.center i+c.radius i:ℚ):ℝ)
  push_cast
  constructor <;> nlinarith only [hp,hm,htr]

theorem lower_sound (c : TaylorCertificate3Reduced) (hc : c.check = true)
    (x : Fin 3 → ℝ)
    (hx : ∀ i, (c.center i-c.radius i:ℚ) ≤ x i ∧ x i ≤ (c.center i+c.radius i:ℚ)) :
    (c.lower:ℝ) ≤ c.whole.eval x := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨he,hcenter⟩,hr,hceq,hgrad,hhess⟩
  let z : Fin 3 → ℝ := fun i => c.center i
  let δ : Fin 3 → ℝ := fun i => x i-c.center i
  let grad : Fin 3 → ℝ := fun i => (c.whole.formula.pdiff i).eval z
  let f : ℝ → ℝ := fun t => c.whole.eval (CertificateFormula.line z δ t)
  let g : ℝ → ℝ := fun t => ∑ i,
    (c.whole.formula.pdiff i).eval (CertificateFormula.line z δ t) * δ i
  let h : ℝ → ℝ := fun t => ∑ i, ∑ j,
    ((c.whole.formula.pdiff i).pdiff j).eval (CertificateFormula.line z δ t) * δ i * δ j
  have hder (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      HasDerivAt f (g t) t ∧ HasDerivAt g (h t) t :=
    c.whole.checked_line_derivatives c.box z δ t (c.line_contains x t hx ht) he
  have hz : ∀ i, (c.centerBox i).Contains (z i) := fun i => RatInterval.contains_point _
  have hline0 : CertificateFormula.line z δ 0 = z := by
    funext i
    dsimp only [CertificateFormula.line]
    ring
  have hline1 : CertificateFormula.line z δ 1 = x := by
    funext i
    dsimp only [CertificateFormula.line,z,δ]
    ring
  have hcenterEq : c.centerValue.eval z = c.whole.eval z := by
    rw [← BoxExpr.formula_eval,hceq,BoxExpr.formula_eval]
  have hcval := c.centerValue.check_sound c.centerBox z hz hcenter
  have hcenterLo : ((c.centerValue.bounds c.centerBox).lo:ℝ) ≤ f 0 := by
    change _ ≤ c.whole.eval (CertificateFormula.line z δ 0)
    rw [hline0,← hcenterEq]
    exact hcval.1
  have hfirst : g 0 = ∑ i, grad i * δ i := by
    simp only [g,hline0,grad]
  have hdelta (i : Fin 3) : |δ i| ≤ (c.radius i:ℝ) := by
    have hxlo : (c.center i:ℝ)-c.radius i ≤ x i := by exact_mod_cast (hx i).1
    have hxhi : x i ≤ (c.center i:ℝ)+c.radius i := by exact_mod_cast (hx i).2
    exact abs_le.mpr ⟨by dsimp only [δ]; linarith, by dsimp only [δ]; linarith⟩
  have hgradBound (i : Fin 3) : |grad i| ≤ (c.gradientAbs i:ℝ) := by
    have hgv := (c.gradient i).check_sound c.centerBox z hz (hgrad i).1
    have heval : (c.gradient i).eval z = grad i := by
      rw [← BoxExpr.formula_eval,(hgrad i).2,CertificateFormula.normalize_eval]
    rw [heval] at hgv
    exact RatInterval.contains_abs hgv
  have hsecond (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      2*(∑ i, (c.diagonal i:ℝ)*(δ i)^2) ≤ h t := by
    apply hessian_three_lower c.hessianIntervals c.radius _ δ hr hdelta
    intro i j
    have hhv := (c.hessian i j).check_sound c.box (CertificateFormula.line z δ t)
      (c.line_contains x t hx ht) (hhess i j).1
    have heval : (c.hessian i j).eval (CertificateFormula.line z δ t) =
        ((c.whole.formula.pdiff i).pdiff j).eval (CertificateFormula.line z δ t) := by
      rw [← BoxExpr.formula_eval,(hhess i j).2,CertificateFormula.normalize_eval]
    rw [heval] at hhv
    exact hhv
  have hT := finite_taylor_lower f g h (c.centerValue.bounds c.centerBox).lo
    c.diagonal c.gradientAbs c.radius δ grad
    (fun t ht => (hder t ht).1) (fun t ht => (hder t ht).2)
    hcenterLo hfirst hgradBound (fun i => RatInterval.absmax_nonneg _) hr hdelta hsecond
  change (c.lower:ℝ) ≤ c.whole.eval (CertificateFormula.line z δ 1) at hT
  rw [hline1] at hT
  exact hT

theorem positive_sound (c : TaylorCertificate3Reduced) (hc : c.check = true) (hl : 0 < c.lower)
    (x : Fin 3 → ℝ)
    (hx : ∀ i, (c.center i-c.radius i:ℚ) ≤ x i ∧ x i ≤ (c.center i+c.radius i:ℚ)) :
    0 < c.whole.eval x := by
  have hpos : (0:ℝ) < c.lower := by exact_mod_cast hl
  exact hpos.trans_le (c.lower_sound hc x hx)


end TaylorCertificate3Reduced
end GaussLocalMaxColoring.Certificate
end

section
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646DefsB4Part3
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part3

def node0 : BoxExpr 3 := .lit (1769451672197/307399000000:ℚ)
def node1 : BoxExpr 3 := .var 0
def node2 : BoxExpr 3 := .lit (13/25:ℚ)
def node3 : BoxExpr 3 := .mul ⟨(77391957894234691485/73786976294838206464:ℚ),(4967819088657573548111/4722366482869645213696:ℚ)⟩ node1 node2
def node4 : BoxExpr 3 := .lit (713/500:ℚ)
def node5 : BoxExpr 3 := .add ⟨(5843589954901567164885/2361183241434822606848:ℚ),(5850956846614843811421/2361183241434822606848:ℚ)⟩ node3 node4
def node6 : BoxExpr 3 := .lit (-2/1:ℚ)
def node7 : BoxExpr 3 := .add ⟨(40215541390951185383/2361183241434822606848:ℚ),(54382640839560121025/2361183241434822606848:ℚ)⟩ node1 node6
def node8 : BoxExpr 3 := .mul ⟨(1369897719911418559/4722366482869645213696:ℚ),(2505075906677554237/4722366482869645213696:ℚ)⟩ node7 node7
def node9 : BoxExpr 3 := .lit (123/50:ℚ)
def node10 : BoxExpr 3 := .mul ⟨(3369948390982089655/4722366482869645213696:ℚ),(96288855162918491/73786976294838206464:ℚ)⟩ node8 node9
def node11 : BoxExpr 3 := .add ⟨(11690549858194116419425/4722366482869645213696:ℚ),(5854038089980057203133/2361183241434822606848:ℚ)⟩ node5 node10
def node12 : BoxExpr 3 := .lit (1/1:ℚ)
def node13 : BoxExpr 3 := .var 1
def node14 : BoxExpr 3 := .mul ⟨(373126622950815737411/2361183241434822606848:ℚ),(761346833071342472695/4722366482869645213696:ℚ)⟩ node13 node13
def node15 : BoxExpr 3 := .neg ⟨(-761346833071342472695/4722366482869645213696:ℚ),(-373126622950815737411/2361183241434822606848:ℚ)⟩ node14
def node16 : BoxExpr 3 := .add ⟨(3961019649798302741001/4722366482869645213696:ℚ),(1988056618484006869437/2361183241434822606848:ℚ)⟩ node12 node15
def node17 : BoxExpr 3 := .sqrt ⟨(2162486209909531695023/2361183241434822606848:ℚ),(1083301201257990367975/1180591620717411303424:ℚ)⟩ node16
def node18 : BoxExpr 3 := .mul ⟨(5353386473987145563103/2361183241434822606848:ℚ),(5371617402495003677019/2361183241434822606848:ℚ)⟩ node11 node17
def node19 : BoxExpr 3 := .lit (-1/50:ℚ)
def node20 : BoxExpr 3 := .add ⟨(1782806333590742539173/4722366482869645213696:ℚ),(900847899761110560015/2361183241434822606848:ℚ)⟩ node13 node19
def node21 : BoxExpr 3 := .lit (-4/5:ℚ)
def node22 : BoxExpr 3 := .mul ⟨(-1441356639617776896025/4722366482869645213696:ℚ),(-713122533436297015669/2361183241434822606848:ℚ)⟩ node20 node21
def node23 : BoxExpr 3 := .mul ⟨(336526022982426957585/2361183241434822606848:ℚ),(687390054497305769809/4722366482869645213696:ℚ)⟩ node20 node20
def node24 : BoxExpr 3 := .lit (9/20:ℚ)
def node25 : BoxExpr 3 := .mul ⟨(151436710342092130913/2361183241434822606848:ℚ),(309325524523787596415/4722366482869645213696:ℚ)⟩ node23 node24
def node26 : BoxExpr 3 := .add ⟨(-1138483218933592634199/4722366482869645213696:ℚ),(-1116919542348806434923/4722366482869645213696:ℚ)⟩ node22 node25
def node27 : BoxExpr 3 := .add ⟨(9568289729040698492007/4722366482869645213696:ℚ),(9626315262641200919115/4722366482869645213696:ℚ)⟩ node18 node26
def node28 : BoxExpr 3 := .lit (-1/4:ℚ)
def node29 : BoxExpr 3 := .add ⟨(696662042530724140023/4722366482869645213696:ℚ),(715551508462202720879/4722366482869645213696:ℚ)⟩ node13 node28
def node30 : BoxExpr 3 := .lit (39/100:ℚ)
def node31 : BoxExpr 3 := .mul ⟨(16981137286686400913/295147905179352825856:ℚ),(279065088300259061143/4722366482869645213696:ℚ)⟩ node29 node30
def node32 : BoxExpr 3 := .mul ⟨(102774319456916578955/4722366482869645213696:ℚ),(1694112088451379475/73786976294838206464:ℚ)⟩ node29 node29
def node33 : BoxExpr 3 := .lit (13/20:ℚ)
def node34 : BoxExpr 3 := .mul ⟨(1043801681984309005/73786976294838206464:ℚ),(70475062879577386161/4722366482869645213696:ℚ)⟩ node32 node33
def node35 : BoxExpr 3 := .add ⟨(21156344014623636933/295147905179352825856:ℚ),(43692518897479555913/590295810358705651712:ℚ)⟩ node31 node34
def node36 : BoxExpr 3 := .add ⟨(9906791233274676682935/4722366482869645213696:ℚ),(9975855413821037366419/4722366482869645213696:ℚ)⟩ node27 node35
def node37 : BoxExpr 3 := .inv ⟨(2573239230769076712819/2361183241434822606848:ℚ),(1289068636388181983933/1180591620717411303424:ℚ)⟩ node17
def node38 : BoxExpr 3 := .mul ⟨(10796512276196946897423/4722366482869645213696:ℚ),(5446236492550050579831/2361183241434822606848:ℚ)⟩ node36 node37
def node39 : BoxExpr 3 := .mul ⟨(24683530546159222288615/4722366482869645213696:ℚ),(25124260931785580827949/4722366482869645213696:ℚ)⟩ node38 node38
def node40 : BoxExpr 3 := .neg ⟨(-25124260931785580827949/4722366482869645213696:ℚ),(-24683530546159222288615/4722366482869645213696:ℚ)⟩ node39
def node41 : BoxExpr 3 := .add ⟨(2058648803902431425007/4722366482869645213696:ℚ),(1249689594764394982171/2361183241434822606848:ℚ)⟩ node0 node40
def node42 : BoxExpr 3 := .lit (1/1000000000000000000:ℚ)
def node43 : BoxExpr 3 := .add ⟨(2058648803902431429729/4722366482869645213696:ℚ),(2499379189528789969065/4722366482869645213696:ℚ)⟩ node41 node42
def node44 : BoxExpr 3 := .var 0
def node45 : BoxExpr 3 := .mul ⟨(4960452196944296901573/4722366482869645213696:ℚ),(4960452196944296901577/4722366482869645213696:ℚ)⟩ node44 node2
def node46 : BoxExpr 3 := .add ⟨(11694546801516410976303/4722366482869645213696:ℚ),(2923636700379102744077/1180591620717411303424:ℚ)⟩ node45 node4
def node47 : BoxExpr 3 := .add ⟨(94598182230511306407/4722366482869645213696:ℚ),(11824772778813913301/590295810358705651712:ℚ)⟩ node44 node6
def node48 : BoxExpr 3 := .mul ⟨(947492757474329795/2361183241434822606848:ℚ),(1894985514948659591/4722366482869645213696:ℚ)⟩ node47 node47
def node49 : BoxExpr 3 := .mul ⟨(4661664366773702591/4722366482869645213696:ℚ),(2330832183386851297/2361183241434822606848:ℚ)⟩ node48 node9
def node50 : BoxExpr 3 := .add ⟨(5849604232941592339447/2361183241434822606848:ℚ),(5849604232941592339451/2361183241434822606848:ℚ)⟩ node46 node49
def node51 : BoxExpr 3 := .var 1
def node52 : BoxExpr 3 := .mul ⟨(376890575010277747589/2361183241434822606848:ℚ),(753781150020555495179/4722366482869645213696:ℚ)⟩ node51 node51
def node53 : BoxExpr 3 := .neg ⟨(-753781150020555495179/4722366482869645213696:ℚ),(-376890575010277747589/2361183241434822606848:ℚ)⟩ node52
def node54 : BoxExpr 3 := .add ⟨(3968585332849089718517/4722366482869645213696:ℚ),(1984292666424544859259/2361183241434822606848:ℚ)⟩ node12 node53
def node55 : BoxExpr 3 := .sqrt ⟨(4329100872035048352505/4722366482869645213696:ℚ),(4329100872035048352507/4722366482869645213696:ℚ)⟩ node54
def node56 : BoxExpr 3 := .mul ⟨(5362465382080846973071/2361183241434822606848:ℚ),(10724930764161693946155/4722366482869645213696:ℚ)⟩ node50 node55
def node57 : BoxExpr 3 := .add ⟨(1792251066556481829601/4722366482869645213696:ℚ),(1792251066556481829603/4722366482869645213696:ℚ)⟩ node51 node19
def node58 : BoxExpr 3 := .mul ⟨(-1433800853245185463683/4722366482869645213696:ℚ),(-11201569165978011435/36893488147419103232:ℚ)⟩ node57 node21
def node59 : BoxExpr 3 := .mul ⟨(170050540191287090977/1180591620717411303424:ℚ),(680202160765148363911/4722366482869645213696:ℚ)⟩ node57 node57
def node60 : BoxExpr 3 := .mul ⟨(153045486172158381879/2361183241434822606848:ℚ),(306090972344316763761/4722366482869645213696:ℚ)⟩ node59 node24
def node61 : BoxExpr 3 := .add ⟨(-1127709880900868699925/4722366482869645213696:ℚ),(-1127709880900868699919/4722366482869645213696:ℚ)⟩ node58 node60
def node62 : BoxExpr 3 := .add ⟨(9597220883260825246217/4722366482869645213696:ℚ),(2399305220815206311559/1180591620717411303424:ℚ)⟩ node56 node61
def node63 : BoxExpr 3 := .add ⟨(706106775496463430451/4722366482869645213696:ℚ),(176526693874115857613/1180591620717411303424:ℚ)⟩ node51 node28
def node64 : BoxExpr 3 := .mul ⟨(275381642443620737875/4722366482869645213696:ℚ),(275381642443620737877/4722366482869645213696:ℚ)⟩ node63 node30
def node65 : BoxExpr 3 := .mul ⟨(6598741068310684631/295147905179352825856:ℚ),(105579857092970954097/4722366482869645213696:ℚ)⟩ node63 node63
def node66 : BoxExpr 3 := .mul ⟨(34313453555215560081/2361183241434822606848:ℚ),(17156726777607780041/1180591620717411303424:ℚ)⟩ node65 node33
def node67 : BoxExpr 3 := .add ⟨(344008549554051858037/4722366482869645213696:ℚ),(344008549554051858041/4722366482869645213696:ℚ)⟩ node64 node66
def node68 : BoxExpr 3 := .add ⟨(4970614716407438552127/2361183241434822606848:ℚ),(9941229432814877104277/4722366482869645213696:ℚ)⟩ node62 node67
def node69 : BoxExpr 3 := .inv ⟨(2575678629087633391193/2361183241434822606848:ℚ),(5151357258175266782389/4722366482869645213696:ℚ)⟩ node55
def node70 : BoxExpr 3 := .mul ⟨(10844313879425379628121/4722366482869645213696:ℚ),(5422156939712689814077/2361183241434822606848:ℚ)⟩ node68 node69
def node71 : BoxExpr 3 := .mul ⟨(6225646820407103212051/1180591620717411303424:ℚ),(6225646820407103212089/1180591620717411303424:ℚ)⟩ node70 node70
def node72 : BoxExpr 3 := .neg ⟨(-6225646820407103212089/1180591620717411303424:ℚ),(-6225646820407103212051/1180591620717411303424:ℚ)⟩ node71
def node73 : BoxExpr 3 := .add ⟨(285040306757449925575/590295810358705651712:ℚ),(2280322454059599404753/4722366482869645213696:ℚ)⟩ node0 node72
def node74 : BoxExpr 3 := .add ⟨(1140161227029799704661/2361183241434822606848:ℚ),(570080613514899852369/1180591620717411303424:ℚ)⟩ node73 node42
def node75 : BoxExpr 3 := .add ⟨(94598182230511306407/2361183241434822606848:ℚ),(11824772778813913301/295147905179352825856:ℚ)⟩ node47 node47
def node76 : BoxExpr 3 := .mul ⟨(232711528287057813761/2361183241434822606848:ℚ),(58177882071764453441/590295810358705651712:ℚ)⟩ node75 node9
def node77 : BoxExpr 3 := .add ⟨(2921053627666331138643/4722366482869645213696:ℚ),(1460526813833165569325/2361183241434822606848:ℚ)⟩ node2 node76
def node78 : BoxExpr 3 := .mul ⟨(1338898183004544159139/2361183241434822606848:ℚ),(2677796366009088318287/4722366482869645213696:ℚ)⟩ node77 node55
def node79 : BoxExpr 3 := .mul ⟨(182565851729145696165/295147905179352825856:ℚ),(2921053627666331138653/4722366482869645213696:ℚ)⟩ node78 node69
def node80 : BoxExpr 3 := .mul ⟨(6707828058655617759425/4722366482869645213696:ℚ),(6707828058655617759477/4722366482869645213696:ℚ)⟩ node79 node70
def node81 : BoxExpr 3 := .mul ⟨(6707828058655617759425/4722366482869645213696:ℚ),(6707828058655617759477/4722366482869645213696:ℚ)⟩ node70 node79
def node82 : BoxExpr 3 := .add ⟨(6707828058655617759425/2361183241434822606848:ℚ),(6707828058655617759477/2361183241434822606848:ℚ)⟩ node80 node81
def node83 : BoxExpr 3 := .neg ⟨(-6707828058655617759477/2361183241434822606848:ℚ),(-6707828058655617759425/2361183241434822606848:ℚ)⟩ node82
def node84 : BoxExpr 3 := .add ⟨(1886698396213874733875/2361183241434822606848:ℚ),(471674599053468683469/590295810358705651712:ℚ)⟩ node51 node51
def node85 : BoxExpr 3 := .neg ⟨(-471674599053468683469/590295810358705651712:ℚ),(-1886698396213874733875/2361183241434822606848:ℚ)⟩ node84
def node86 : BoxExpr 3 := .lit (2/1:ℚ)
def node87 : BoxExpr 3 := .mul ⟨(4329100872035048352505/2361183241434822606848:ℚ),(4329100872035048352507/2361183241434822606848:ℚ)⟩ node86 node55
def node88 : BoxExpr 3 := .inv ⟨(2575678629087633391193/4722366482869645213696:ℚ),(2575678629087633391195/4722366482869645213696:ℚ)⟩ node87
def node89 : BoxExpr 3 := .mul ⟨(-2058090474887918780773/4722366482869645213696:ℚ),(-1029045237443959390385/2361183241434822606848:ℚ)⟩ node85 node88
def node90 : BoxExpr 3 := .mul ⟨(-637340134303033877791/590295810358705651712:ℚ),(-1274680268606067755579/1180591620717411303424:ℚ)⟩ node50 node89
def node91 : BoxExpr 3 := .add ⟨(1792251066556481829601/2361183241434822606848:ℚ),(1792251066556481829603/2361183241434822606848:ℚ)⟩ node57 node57
def node92 : BoxExpr 3 := .mul ⟨(100814122493802102915/295147905179352825856:ℚ),(403256489975208411661/1180591620717411303424:ℚ)⟩ node91 node24
def node93 : BoxExpr 3 := .add ⟨(-2164867226394882524317/4722366482869645213696:ℚ),(-270608403299360315539/590295810358705651712:ℚ)⟩ node21 node92
def node94 : BoxExpr 3 := .add ⟨(-7263588300819153546645/4722366482869645213696:ℚ),(-1815897075204788386657/1180591620717411303424:ℚ)⟩ node90 node93
def node95 : BoxExpr 3 := .add ⟨(706106775496463430451/2361183241434822606848:ℚ),(176526693874115857613/590295810358705651712:ℚ)⟩ node63 node63
def node96 : BoxExpr 3 := .mul ⟨(458969404072701229793/2361183241434822606848:ℚ),(229484702036350614897/1180591620717411303424:ℚ)⟩ node95 node33
def node97 : BoxExpr 3 := .add ⟨(2759661736464564092927/4722366482869645213696:ℚ),(1379830868232282046465/2361183241434822606848:ℚ)⟩ node30 node96
def node98 : BoxExpr 3 := .add ⟨(-2251963282177294726859/2361183241434822606848:ℚ),(-2251963282177294726849/2361183241434822606848:ℚ)⟩ node94 node97
def node99 : BoxExpr 3 := .mul ⟨(-4913073748456224985377/4722366482869645213696:ℚ),(-4913073748456224985351/4722366482869645213696:ℚ)⟩ node98 node69
def node100 : BoxExpr 3 := .mul ⟨(3968585332849089718515/4722366482869645213696:ℚ),(496073166606136214815/590295810358705651712:ℚ)⟩ node55 node55
def node101 : BoxExpr 3 := .inv ⟨(1404829638784702685289/1180591620717411303424:ℚ),(1404829638784702685291/1180591620717411303424:ℚ)⟩ node100
def node102 : BoxExpr 3 := .mul ⟨(-612249495864220457153/1180591620717411303424:ℚ),(-612249495864220457151/1180591620717411303424:ℚ)⟩ node89 node101
def node103 : BoxExpr 3 := .neg ⟨(612249495864220457151/1180591620717411303424:ℚ),(612249495864220457153/1180591620717411303424:ℚ)⟩ node102
def node104 : BoxExpr 3 := .mul ⟨(5155476797991215159749/4722366482869645213696:ℚ),(5155476797991215159779/4722366482869645213696:ℚ)⟩ node68 node103
def node105 : BoxExpr 3 := .add ⟨(60600762383747543593/1180591620717411303424:ℚ),(60600762383747543607/1180591620717411303424:ℚ)⟩ node99 node104
def node106 : BoxExpr 3 := .mul ⟨(556647766331331016217/4722366482869645213696:ℚ),(139161941582832754087/1180591620717411303424:ℚ)⟩ node105 node70
def node107 : BoxExpr 3 := .mul ⟨(556647766331331016217/4722366482869645213696:ℚ),(139161941582832754087/1180591620717411303424:ℚ)⟩ node70 node105
def node108 : BoxExpr 3 := .add ⟨(556647766331331016217/2361183241434822606848:ℚ),(139161941582832754087/590295810358705651712:ℚ)⟩ node106 node107
def node109 : BoxExpr 3 := .neg ⟨(-139161941582832754087/590295810358705651712:ℚ),(-556647766331331016217/2361183241434822606848:ℚ)⟩ node108
def node111 : BoxExpr 3 := .lit (123/25:ℚ)
def node112 : BoxExpr 3 := .mul ⟨(10639432152754895939513/2361183241434822606848:ℚ),(21319367640757250441749/4722366482869645213696:ℚ)⟩ node111 node17
def node113 : BoxExpr 3 := .mul ⟨(11594951094070146100713/2361183241434822606848:ℚ),(23278268023475542420729/4722366482869645213696:ℚ)⟩ node112 node37
def node114 : BoxExpr 3 := .mul ⟨(26508961615566998096481/2361183241434822606848:ℚ),(3355810938559705510239/295147905179352825856:ℚ)⟩ node113 node38
def node115 : BoxExpr 3 := .add ⟨(40215541390951185383/1180591620717411303424:ℚ),(54382640839560121025/1180591620717411303424:ℚ)⟩ node7 node7
def node116 : BoxExpr 3 := .mul ⟨(49465115910869958021/590295810358705651712:ℚ),(535125185861271590887/4722366482869645213696:ℚ)⟩ node115 node9
def node117 : BoxExpr 3 := .add ⟨(2851351498379175175289/4722366482869645213696:ℚ),(2990755756953487102009/4722366482869645213696:ℚ)⟩ node2 node116
def node118 : BoxExpr 3 := .mul ⟨(652851522347641074869/1180591620717411303424:ℚ),(1372146493047348603437/2361183241434822606848:ℚ)⟩ node117 node17
def node119 : BoxExpr 3 := .mul ⟨(88935449803940876225/147573952589676412928:ℚ),(2996448522381564381297/4722366482869645213696:ℚ)⟩ node118 node37
def node120 : BoxExpr 3 := .mul ⟨(857551251345432898853/2361183241434822606848:ℚ),(1901314474396015650979/4722366482869645213696:ℚ)⟩ node119 node119
def node121 : BoxExpr 3 := .add ⟨(13683256433456215497667/1180591620717411303424:ℚ),(55594289491351303814803/4722366482869645213696:ℚ)⟩ node114 node120
def node122 : BoxExpr 3 := .mul ⟨(26508961615566998096481/2361183241434822606848:ℚ),(3355810938559705510239/295147905179352825856:ℚ)⟩ node38 node113
def node123 : BoxExpr 3 := .add ⟨(13683256433456215497667/1180591620717411303424:ℚ),(55594289491351303814803/4722366482869645213696:ℚ)⟩ node120 node122
def node124 : BoxExpr 3 := .add ⟨(13683256433456215497667/590295810358705651712:ℚ),(55594289491351303814803/2361183241434822606848:ℚ)⟩ node121 node123
def node125 : BoxExpr 3 := .neg ⟨(-55594289491351303814803/2361183241434822606848:ℚ),(-13683256433456215497667/590295810358705651712:ℚ)⟩ node124
def node126 : BoxExpr 3 := .add ⟨(1877253663248135443447/2361183241434822606848:ℚ),(1896143129179614024303/2361183241434822606848:ℚ)⟩ node13 node13
def node127 : BoxExpr 3 := .neg ⟨(-1896143129179614024303/2361183241434822606848:ℚ),(-1877253663248135443447/2361183241434822606848:ℚ)⟩ node126
def node128 : BoxExpr 3 := .mul ⟨(2162486209909531695023/1180591620717411303424:ℚ),(1083301201257990367975/590295810358705651712:ℚ)⟩ node86 node17
def node129 : BoxExpr 3 := .inv ⟨(2573239230769076712819/4722366482869645213696:ℚ),(1289068636388181983933/2361183241434822606848:ℚ)⟩ node128
def node130 : BoxExpr 3 := .mul ⟨(-1035183798968131051963/2361183241434822606848:ℚ),(-2045848321979294585087/4722366482869645213696:ℚ)⟩ node127 node129
def node131 : BoxExpr 3 := .mul ⟨(-327799834839118707127/1180591620717411303424:ℚ),(-1235277418534313945195/4722366482869645213696:ℚ)⟩ node117 node130
def node132 : BoxExpr 3 := .mul ⟨(-1431677063225499413443/4722366482869645213696:ℚ),(-336554175304503970301/1180591620717411303424:ℚ)⟩ node131 node37
def node133 : BoxExpr 3 := .mul ⟨(495127456224787842625/590295810358705651712:ℚ),(994028309242003434719/1180591620717411303424:ℚ)⟩ node17 node17
def node134 : BoxExpr 3 := .inv ⟨(1402169899940781278595/1180591620717411303424:ℚ),(1407512911458681423515/1180591620717411303424:ℚ)⟩ node133
def node135 : BoxExpr 3 := .mul ⟨(-2468312559926682939273/4722366482869645213696:ℚ),(-303727691119447101705/590295810358705651712:ℚ)⟩ node130 node134
def node136 : BoxExpr 3 := .neg ⟨(303727691119447101705/590295810358705651712:ℚ),(2468312559926682939273/4722366482869645213696:ℚ)⟩ node135
def node137 : BoxExpr 3 := .mul ⟨(1343659108174734400609/4722366482869645213696:ℚ),(1434402194380309420203/4722366482869645213696:ℚ)⟩ node118 node136
def node138 : BoxExpr 3 := .add ⟨(-44008977525382506417/2361183241434822606848:ℚ),(88185493162293538999/4722366482869645213696:ℚ)⟩ node132 node137
def node139 : BoxExpr 3 := .mul ⟨(-101509825748595705563/2361183241434822606848:ℚ),(203406090025505337663/4722366482869645213696:ℚ)⟩ node138 node38
def node140 : BoxExpr 3 := .mul ⟨(-5133024225266996062639/4722366482869645213696:ℚ),(-5064641191479063265619/4722366482869645213696:ℚ)⟩ node11 node130
def node141 : BoxExpr 3 := .add ⟨(1782806333590742539173/2361183241434822606848:ℚ),(900847899761110560015/1180591620717411303424:ℚ)⟩ node20 node20
def node142 : BoxExpr 3 := .mul ⟨(1604525700231668285255/4722366482869645213696:ℚ),(405381554892499752007/1180591620717411303424:ℚ)⟩ node141 node24
def node143 : BoxExpr 3 := .add ⟨(-1086683743032023942851/2361183241434822606848:ℚ),(-134772935420357322683/295147905179352825856:ℚ)⟩ node21 node142
def node144 : BoxExpr 3 := .add ⟨(-7306391711331043948341/4722366482869645213696:ℚ),(-7221008158204780428547/4722366482869645213696:ℚ)⟩ node140 node143
def node145 : BoxExpr 3 := .add ⟨(696662042530724140023/2361183241434822606848:ℚ),(715551508462202720879/2361183241434822606848:ℚ)⟩ node29 node29
def node146 : BoxExpr 3 := .mul ⟨(905660655289941382029/4722366482869645213696:ℚ),(930216961000863537143/4722366482869645213696:ℚ)⟩ node145 node33
def node147 : BoxExpr 3 := .add ⟨(1373691791804551507685/2361183241434822606848:ℚ),(2771939889320025170485/4722366482869645213696:ℚ)⟩ node30 node146
def node148 : BoxExpr 3 := .add ⟨(-4559008127721940932971/4722366482869645213696:ℚ),(-2224534134442377629031/2361183241434822606848:ℚ)⟩ node144 node147
def node149 : BoxExpr 3 := .mul ⟨(-4977906235615965836441/4722366482869645213696:ℚ),(-1212158888069523934487/1180591620717411303424:ℚ)⟩ node148 node37
def node150 : BoxExpr 3 := .mul ⟨(5097388080488722263249/4722366482869645213696:ℚ),(5214235130472986679623/4722366482869645213696:ℚ)⟩ node36 node136
def node151 : BoxExpr 3 := .add ⟨(14935230609094553351/590295810358705651712:ℚ),(365599578194890941675/4722366482869645213696:ℚ)⟩ node149 node150
def node152 : BoxExpr 3 := .mul ⟨(18001434925831615337/1180591620717411303424:ℚ),(57995303829093140543/1180591620717411303424:ℚ)⟩ node119 node151
def node153 : BoxExpr 3 := .add ⟨(-65506955896932474889/2361183241434822606848:ℚ),(435387305341877899835/4722366482869645213696:ℚ)⟩ node139 node152
def node154 : BoxExpr 3 := .mul ⟨(18001434925831615337/1180591620717411303424:ℚ),(57995303829093140543/1180591620717411303424:ℚ)⟩ node151 node119
def node155 : BoxExpr 3 := .mul ⟨(-101509825748595705563/2361183241434822606848:ℚ),(203406090025505337663/4722366482869645213696:ℚ)⟩ node38 node138
def node156 : BoxExpr 3 := .add ⟨(-65506955896932474889/2361183241434822606848:ℚ),(435387305341877899835/4722366482869645213696:ℚ)⟩ node154 node155
def node157 : BoxExpr 3 := .add ⟨(-65506955896932474889/1180591620717411303424:ℚ),(435387305341877899835/2361183241434822606848:ℚ)⟩ node153 node156
def node158 : BoxExpr 3 := .neg ⟨(-435387305341877899835/2361183241434822606848:ℚ),(65506955896932474889/1180591620717411303424:ℚ)⟩ node157
def node159 : BoxExpr 3 := .add ⟨(-65506955896932474889/2361183241434822606848:ℚ),(435387305341877899835/4722366482869645213696:ℚ)⟩ node139 node154
def node160 : BoxExpr 3 := .add ⟨(-65506955896932474889/2361183241434822606848:ℚ),(435387305341877899835/4722366482869645213696:ℚ)⟩ node152 node155
def node161 : BoxExpr 3 := .add ⟨(-65506955896932474889/1180591620717411303424:ℚ),(435387305341877899835/2361183241434822606848:ℚ)⟩ node159 node160
def node162 : BoxExpr 3 := .neg ⟨(-435387305341877899835/2361183241434822606848:ℚ),(65506955896932474889/1180591620717411303424:ℚ)⟩ node161
def node163 : BoxExpr 3 := .mul ⟨(-1289068636388181983933/1180591620717411303424:ℚ),(-2573239230769076712819/2361183241434822606848:ℚ)⟩ node6 node129
def node164 : BoxExpr 3 := .mul ⟨(-1035183798968131051963/1180591620717411303424:ℚ),(-2045848321979294585087/2361183241434822606848:ℚ)⟩ node86 node130
def node165 : BoxExpr 3 := .mul ⟨(15844078599193210964003/4722366482869645213696:ℚ),(994028309242003434719/295147905179352825856:ℚ)⟩ node128 node128
def node166 : BoxExpr 3 := .inv ⟨(1402169899940781278595/4722366482869645213696:ℚ),(1407512911458681423515/4722366482869645213696:ℚ)⟩ node165
def node167 : BoxExpr 3 := .mul ⟨(-1234156279963341469637/4722366482869645213696:ℚ),(-303727691119447101705/1180591620717411303424:ℚ)⟩ node164 node166
def node168 : BoxExpr 3 := .neg ⟨(303727691119447101705/1180591620717411303424:ℚ),(1234156279963341469637/4722366482869645213696:ℚ)⟩ node167
def node169 : BoxExpr 3 := .mul ⟨(-991086549116928633451/4722366482869645213696:ℚ),(-965912193138220115093/4722366482869645213696:ℚ)⟩ node127 node168
def node170 : BoxExpr 3 := .add ⟨(-6147361094669656569183/4722366482869645213696:ℚ),(-6112390654676373540731/4722366482869645213696:ℚ)⟩ node163 node169
def node171 : BoxExpr 3 := .mul ⟨(-15241039055990200303239/4722366482869645213696:ℚ),(-15131652310438949137339/4722366482869645213696:ℚ)⟩ node11 node170
def node172 : BoxExpr 3 := .lit (9/10:ℚ)
def node173 : BoxExpr 3 := .add ⟨(-10990909221407519610913/4722366482869645213696:ℚ),(-2720380618964067111253/1180591620717411303424:ℚ)⟩ node171 node172
def node174 : BoxExpr 3 := .lit (13/10:ℚ)
def node175 : BoxExpr 3 := .add ⟨(-4851832793676980833109/4722366482869645213696:ℚ),(-4742446048125729667207/4722366482869645213696:ℚ)⟩ node173 node174
def node176 : BoxExpr 3 := .mul ⟨(-5297636687890487267197/4722366482869645213696:ℚ),(-5168361356582904872161/4722366482869645213696:ℚ)⟩ node175 node37
def node177 : BoxExpr 3 := .mul ⟨(-595731878459893554365/1180591620717411303424:ℚ),(-572300027049155724537/1180591620717411303424:ℚ)⟩ node148 node136
def node178 : BoxExpr 3 := .add ⟨(-7680564201730061484657/4722366482869645213696:ℚ),(-7457561464779527770309/4722366482869645213696:ℚ)⟩ node176 node177
def node179 : BoxExpr 3 := .mul ⟨(-7328944200779985061237/4722366482869645213696:ℚ),(-7259589211262083922209/4722366482869645213696:ℚ)⟩ node170 node134
def node180 : BoxExpr 3 := .mul ⟨(-1899752350035373745451/4722366482869645213696:ℚ),(-1873687186242424490047/4722366482869645213696:ℚ)⟩ node130 node17
def node181 : BoxExpr 3 := .mul ⟨(-1899752350035373745451/4722366482869645213696:ℚ),(-1873687186242424490047/4722366482869645213696:ℚ)⟩ node17 node130
def node182 : BoxExpr 3 := .add ⟨(-1899752350035373745451/2361183241434822606848:ℚ),(-1873687186242424490047/2361183241434822606848:ℚ)⟩ node180 node181
def node183 : BoxExpr 3 := .mul ⟨(830604566746485715875/1180591620717411303424:ℚ),(1673893431454444809297/2361183241434822606848:ℚ)⟩ node133 node133
def node184 : BoxExpr 3 := .inv ⟨(3330669799443791582419/2361183241434822606848:ℚ),(6712202801232966340577/4722366482869645213696:ℚ)⟩ node183
def node185 : BoxExpr 3 := .mul ⟨(-5400480073629362013773/4722366482869645213696:ℚ),(-5286022037857770143049/4722366482869645213696:ℚ)⟩ node182 node184
def node186 : BoxExpr 3 := .neg ⟨(5286022037857770143049/4722366482869645213696:ℚ),(5400480073629362013773/4722366482869645213696:ℚ)⟩ node185
def node187 : BoxExpr 3 := .mul ⟨(-2367664389941272273475/4722366482869645213696:ℚ),(-1145019065687304861545/2361183241434822606848:ℚ)⟩ node130 node186
def node188 : BoxExpr 3 := .add ⟨(-1212076073840157166839/590295810358705651712:ℚ),(-9549627342636693645299/4722366482869645213696:ℚ)⟩ node179 node187
def node189 : BoxExpr 3 := .neg ⟨(9549627342636693645299/4722366482869645213696:ℚ),(1212076073840157166839/590295810358705651712:ℚ)⟩ node188
def node190 : BoxExpr 3 := .mul ⟨(5008408643328329745855/1180591620717411303424:ℚ),(20483790416594059724447/4722366482869645213696:ℚ)⟩ node36 node189
def node191 : BoxExpr 3 := .add ⟨(2206338382434218095745/590295810358705651712:ℚ),(18194590308397436826299/4722366482869645213696:ℚ)⟩ node177 node190
def node192 : BoxExpr 3 := .add ⟨(9970142857743683281303/4722366482869645213696:ℚ),(5368514421808954527995/2361183241434822606848:ℚ)⟩ node178 node191
def node193 : BoxExpr 3 := .mul ⟨(22794243129909645685349/4722366482869645213696:ℚ),(24765718002529915671311/4722366482869645213696:ℚ)⟩ node192 node38
def node194 : BoxExpr 3 := .mul ⟨(3023041796095921343/4722366482869645213696:ℚ),(28304252128915461567/4722366482869645213696:ℚ)⟩ node151 node151
def node195 : BoxExpr 3 := .add ⟨(5699316542926435401673/1180591620717411303424:ℚ),(12397011127329415566439/2361183241434822606848:ℚ)⟩ node193 node194
def node196 : BoxExpr 3 := .mul ⟨(22794243129909645685349/4722366482869645213696:ℚ),(24765718002529915671311/4722366482869645213696:ℚ)⟩ node38 node192
def node197 : BoxExpr 3 := .add ⟨(5699316542926435401673/1180591620717411303424:ℚ),(12397011127329415566439/2361183241434822606848:ℚ)⟩ node194 node196
def node198 : BoxExpr 3 := .add ⟨(5699316542926435401673/590295810358705651712:ℚ),(12397011127329415566439/1180591620717411303424:ℚ)⟩ node195 node197
def node199 : BoxExpr 3 := .neg ⟨(-12397011127329415566439/1180591620717411303424:ℚ),(-5699316542926435401673/590295810358705651712:ℚ)⟩ node198
def node200 : BoxExpr 3 := .sqrt ⟨(3117963135052838795999/4722366482869645213696:ℚ),(107360849768890601595/147573952589676412928:ℚ)⟩ node43
def node201 : BoxExpr 3 := .lit (529601630237086760467563827576046216491453725554801596159/2126764793255865396646091296448551321600000000000000000000:ℚ)
def node202 : BoxExpr 3 := .sqrt ⟨(2356538900649602022061/4722366482869645213696:ℚ),(2356538900649602022063/4722366482869645213696:ℚ)⟩ node201
def node203 : BoxExpr 3 := .lit (105113898053531722649817636563532003778556764000751/182628568201966125342452015454275643968150995402752:ℚ)
def node204 : BoxExpr 3 := .mul ⟨(1356332101821719635057/4722366482869645213696:ℚ),(1356332101821719635059/4722366482869645213696:ℚ)⟩ node202 node203
def node205 : BoxExpr 3 := .neg ⟨(-1356332101821719635059/4722366482869645213696:ℚ),(-1356332101821719635057/4722366482869645213696:ℚ)⟩ node204
def node206 : BoxExpr 3 := .add ⟨(440407758307779790235/1180591620717411303424:ℚ),(2079215090782779615983/4722366482869645213696:ℚ)⟩ node200 node205
def node207 : BoxExpr 3 := .sqrt ⟨(3281542065429926587517/4722366482869645213696:ℚ),(3281542065429926587629/4722366482869645213696:ℚ)⟩ node74
def node208 : BoxExpr 3 := .add ⟨(962604981804103476229/2361183241434822606848:ℚ),(481302490902051738143/1180591620717411303424:ℚ)⟩ node207 node205
def node209 : BoxExpr 3 := .mul ⟨(3281542065429926587517/2361183241434822606848:ℚ),(3281542065429926587629/2361183241434822606848:ℚ)⟩ node86 node207
def node210 : BoxExpr 3 := .inv ⟨(212369146443587896145/295147905179352825856:ℚ),(3397906343097406338437/4722366482869645213696:ℚ)⟩ node209
def node211 : BoxExpr 3 := .mul ⟨(-4826514755174676667947/2361183241434822606848:ℚ),(-9653029510349353335485/4722366482869645213696:ℚ)⟩ node83 node210
def node212 : BoxExpr 3 := .mul ⟨(-400527359100444297115/2361183241434822606848:ℚ),(-801054718200888594013/4722366482869645213696:ℚ)⟩ node109 node210
def node213 : BoxExpr 3 := .mul ⟨(3117963135052838795999/2361183241434822606848:ℚ),(107360849768890601595/73786976294838206464:ℚ)⟩ node86 node200
def node214 : BoxExpr 3 := .inv ⟨(3245588540674994671633/4722366482869645213696:ℚ),(3576172044470420252629/4722366482869645213696:ℚ)⟩ node213
def node215 : BoxExpr 3 := .mul ⟨(-10525164905792753923009/590295810358705651712:ℚ),(-37616919771593912677471/2361183241434822606848:ℚ)⟩ node125 node214
def node216 : BoxExpr 3 := .mul ⟨(1626629663886422928485/1180591620717411303424:ℚ),(107992513855609757445/73786976294838206464:ℚ)⟩ node119 node38
def node217 : BoxExpr 3 := .mul ⟨(1626629663886422928485/1180591620717411303424:ℚ),(107992513855609757445/73786976294838206464:ℚ)⟩ node38 node119
def node218 : BoxExpr 3 := .add ⟨(1626629663886422928485/590295810358705651712:ℚ),(107992513855609757445/36893488147419103232:ℚ)⟩ node216 node217
def node219 : BoxExpr 3 := .neg ⟨(-107992513855609757445/36893488147419103232:ℚ),(-1626629663886422928485/590295810358705651712:ℚ)⟩ node218
def node220 : BoxExpr 3 := .mul ⟨(-10467966799976674866945/4722366482869645213696:ℚ),(-4471800836451534364945/2361183241434822606848:ℚ)⟩ node219 node214
def node221 : BoxExpr 3 := .mul ⟨(-10467966799976674866945/2361183241434822606848:ℚ),(-4471800836451534364945/1180591620717411303424:ℚ)⟩ node86 node220
def node222 : BoxExpr 3 := .mul ⟨(4117297607804862859457/2361183241434822606848:ℚ),(9997516758115159876263/4722366482869645213696:ℚ)⟩ node213 node213
def node223 : BoxExpr 3 := .inv ⟨(557657109712487271795/1180591620717411303424:ℚ),(2708177465269539383131/4722366482869645213696:ℚ)⟩ node222
def node224 : BoxExpr 3 := .mul ⟨(-187598685278627965679/73786976294838206464:ℚ),(-8449091068933988507949/4722366482869645213696:ℚ)⟩ node221 node223
def node225 : BoxExpr 3 := .neg ⟨(8449091068933988507949/4722366482869645213696:ℚ),(187598685278627965679/73786976294838206464:ℚ)⟩ node224
def node226 : BoxExpr 3 := .mul ⟨(-35144202859074832902971/4722366482869645213696:ℚ),(-5820616513123445423689/1180591620717411303424:ℚ)⟩ node219 node225
def node227 : BoxExpr 3 := .add ⟨(-119345522105416864287043/4722366482869645213696:ℚ),(-49258152797840803524849/2361183241434822606848:ℚ)⟩ node215 node226
def node228 : BoxExpr 3 := .mul ⟨(-659423581600034884059/4722366482869645213696:ℚ),(198429448664569659907/4722366482869645213696:ℚ)⟩ node158 node214
def node229 : BoxExpr 3 := .mul ⟨(1067052406377245599/18446744073709551616:ℚ),(843281338561407739783/4722366482869645213696:ℚ)⟩ node151 node38
def node230 : BoxExpr 3 := .mul ⟨(1067052406377245599/18446744073709551616:ℚ),(843281338561407739783/4722366482869645213696:ℚ)⟩ node38 node151
def node231 : BoxExpr 3 := .add ⟨(1067052406377245599/9223372036854775808:ℚ),(843281338561407739783/2361183241434822606848:ℚ)⟩ node229 node230
def node232 : BoxExpr 3 := .neg ⟨(-843281338561407739783/2361183241434822606848:ℚ),(-1067052406377245599/9223372036854775808:ℚ)⟩ node231
def node233 : BoxExpr 3 := .mul ⟨(-79825421203712281917/295147905179352825856:ℚ),(-187741156303754715223/2361183241434822606848:ℚ)⟩ node232 node214
def node234 : BoxExpr 3 := .mul ⟨(-79825421203712281917/147573952589676412928:ℚ),(-187741156303754715223/1180591620717411303424:ℚ)⟩ node86 node233
def node235 : BoxExpr 3 := .mul ⟨(-732451096775278472713/2361183241434822606848:ℚ),(-354721103423762849697/4722366482869645213696:ℚ)⟩ node234 node223
def node236 : BoxExpr 3 := .neg ⟨(354721103423762849697/4722366482869645213696:ℚ),(732451096775278472713/2361183241434822606848:ℚ)⟩ node235
def node237 : BoxExpr 3 := .mul ⟨(-4287978133213963301973/4722366482869645213696:ℚ),(-122184474950997521047/590295810358705651712:ℚ)⟩ node219 node236
def node238 : BoxExpr 3 := .add ⟨(-309212607175874886627/295147905179352825856:ℚ),(-779046350943410508469/4722366482869645213696:ℚ)⟩ node228 node237
def node239 : BoxExpr 3 := .mul ⟨(-659423581600034884059/4722366482869645213696:ℚ),(198429448664569659907/4722366482869645213696:ℚ)⟩ node162 node214
def node240 : BoxExpr 3 := .mul ⟨(-1071994533303490825493/1180591620717411303424:ℚ),(-977475799607980168379/4722366482869645213696:ℚ)⟩ node232 node225
def node241 : BoxExpr 3 := .add ⟨(-4947401714813998186031/4722366482869645213696:ℚ),(-97380793867926313559/590295810358705651712:ℚ)⟩ node239 node240
def node242 : BoxExpr 3 := .mul ⟨(-18776113539415006714525/2361183241434822606848:ℚ),(-31336215058278979917675/4722366482869645213696:ℚ)⟩ node199 node214
def node243 : BoxExpr 3 := .mul ⟨(-261590176687893367943/2361183241434822606848:ℚ),(-2564856469308910281/295147905179352825856:ℚ)⟩ node232 node236
def node244 : BoxExpr 3 := .add ⟨(-4759425929025725020617/590295810358705651712:ℚ),(-31377252761787922482171/4722366482869645213696:ℚ)⟩ node242 node243
def node245 : BoxExpr 3 := .lit (10231972443309968137205539920015976811802592462832573896597365056442366775419985120081998712237847234256419/10234589323870945947863443762579093077777685434865006133338577527430059824928599063384943477956000000000000:ℚ)
def node246 : BoxExpr 3 := .lit (182628568201966125342452015454275643968150995402752/287742466255497847992269652017807647746707759403503:ℚ)
def node247 : BoxExpr 3 := .mul ⟨(559048786725623557425/2361183241434822606848:ℚ),(329916609073274677351/1180591620717411303424:ℚ)⟩ node206 node246
def node248 : BoxExpr 3 := .mul ⟨(33090988074846844921/590295810358705651712:ℚ),(92195274837090589267/1180591620717411303424:ℚ)⟩ node247 node247
def node249 : BoxExpr 3 := .neg ⟨(-92195274837090589267/1180591620717411303424:ℚ),(-33090988074846844921/590295810358705651712:ℚ)⟩ node248
def node250 : BoxExpr 3 := .add ⟨(4352377922365805764071/4722366482869645213696:ℚ),(1114107779278848340443/1180591620717411303424:ℚ)⟩ node245 node249
def node251 : BoxExpr 3 := .mul ⟨(610960112557261807961/2361183241434822606848:ℚ),(1221920225114523615995/4722366482869645213696:ℚ)⟩ node208 node246
def node252 : BoxExpr 3 := .mul ⟨(158086950892110892051/2361183241434822606848:ℚ),(316173901784221784141/4722366482869645213696:ℚ)⟩ node251 node251
def node253 : BoxExpr 3 := .neg ⟨(-316173901784221784141/4722366482869645213696:ℚ),(-158086950892110892051/2361183241434822606848:ℚ)⟩ node252
def node254 : BoxExpr 3 := .add ⟨(2202492559964973168499/2361183241434822606848:ℚ),(2202492559964973168519/2361183241434822606848:ℚ)⟩ node245 node253
def node255 : BoxExpr 3 := .mul ⟨(-3063362494295616931387/2361183241434822606848:ℚ),(-6126724988591233862511/4722366482869645213696:ℚ)⟩ node211 node246
def node256 : BoxExpr 3 := .mul ⟨(-792650168557537289001/2361183241434822606848:ℚ),(-1585300337115074577839/4722366482869645213696:ℚ)⟩ node255 node251
def node257 : BoxExpr 3 := .mul ⟨(-792650168557537289001/2361183241434822606848:ℚ),(-1585300337115074577839/4722366482869645213696:ℚ)⟩ node251 node255
def node258 : BoxExpr 3 := .add ⟨(-792650168557537289001/1180591620717411303424:ℚ),(-1585300337115074577839/2361183241434822606848:ℚ)⟩ node256 node257
def node259 : BoxExpr 3 := .neg ⟨(1585300337115074577839/2361183241434822606848:ℚ),(792650168557537289001/1180591620717411303424:ℚ)⟩ node258
def node260 : BoxExpr 3 := .mul ⟨(-63553130573780267611/590295810358705651712:ℚ),(-508425044590242140749/4722366482869645213696:ℚ)⟩ node212 node246
def node261 : BoxExpr 3 := .mul ⟨(-131555830576294414283/4722366482869645213696:ℚ),(-65777915288147207119/2361183241434822606848:ℚ)⟩ node260 node251
def node262 : BoxExpr 3 := .mul ⟨(-131555830576294414283/4722366482869645213696:ℚ),(-65777915288147207119/2361183241434822606848:ℚ)⟩ node251 node260
def node263 : BoxExpr 3 := .add ⟨(-131555830576294414283/2361183241434822606848:ℚ),(-65777915288147207119/1180591620717411303424:ℚ)⟩ node261 node262
def node264 : BoxExpr 3 := .neg ⟨(65777915288147207119/1180591620717411303424:ℚ),(131555830576294414283/2361183241434822606848:ℚ)⟩ node263
def node265 : BoxExpr 3 := .mul ⟨(-75747949571249387774143/4722366482869645213696:ℚ),(-31263879936844232293701/2361183241434822606848:ℚ)⟩ node227 node246
def node266 : BoxExpr 3 := .mul ⟨(-2645972814419731569379/590295810358705651712:ℚ),(-14804470775768709791307/4722366482869645213696:ℚ)⟩ node265 node247
def node267 : BoxExpr 3 := .mul ⟨(-830495153158909929529/590295810358705651712:ℚ),(-2838227511820716756251/2361183241434822606848:ℚ)⟩ node220 node246
def node268 : BoxExpr 3 := .mul ⟨(6823303899074687257597/4722366482869645213696:ℚ),(4673739418894517143555/2361183241434822606848:ℚ)⟩ node267 node267
def node269 : BoxExpr 3 := .add ⟨(-14344478616283165297435/4722366482869645213696:ℚ),(-5456991937979675504197/4722366482869645213696:ℚ)⟩ node266 node268
def node270 : BoxExpr 3 := .mul ⟨(-2645972814419731569379/590295810358705651712:ℚ),(-14804470775768709791307/4722366482869645213696:ℚ)⟩ node247 node265
def node271 : BoxExpr 3 := .add ⟨(-14344478616283165297435/4722366482869645213696:ℚ),(-5456991937979675504197/4722366482869645213696:ℚ)⟩ node268 node270
def node272 : BoxExpr 3 := .add ⟨(-14344478616283165297435/2361183241434822606848:ℚ),(-5456991937979675504197/2361183241434822606848:ℚ)⟩ node269 node271
def node273 : BoxExpr 3 := .neg ⟨(5456991937979675504197/2361183241434822606848:ℚ),(14344478616283165297435/2361183241434822606848:ℚ)⟩ node272
def node274 : BoxExpr 3 := .mul ⟨(-3140088785831655806547/4722366482869645213696:ℚ),(-123614113591968836417/1180591620717411303424:ℚ)⟩ node238 node246
def node275 : BoxExpr 3 := .mul ⟨(-877498557698612782933/4722366482869645213696:ℚ),(-58535330094719529469/2361183241434822606848:ℚ)⟩ node274 node247
def node276 : BoxExpr 3 := .mul ⟨(-810636125853351364611/4722366482869645213696:ℚ),(-238316568385088945395/4722366482869645213696:ℚ)⟩ node233 node246
def node277 : BoxExpr 3 := .mul ⟨(286465120132834780551/4722366482869645213696:ℚ),(570247460411096643987/2361183241434822606848:ℚ)⟩ node267 node276
def node278 : BoxExpr 3 := .add ⟨(-295516718782889001191/2361183241434822606848:ℚ),(255856065158188557259/1180591620717411303424:ℚ)⟩ node275 node277
def node279 : BoxExpr 3 := .mul ⟨(286465120132834780551/4722366482869645213696:ℚ),(570247460411096643987/2361183241434822606848:ℚ)⟩ node276 node267
def node280 : BoxExpr 3 := .mul ⟨(-877498557698612782933/4722366482869645213696:ℚ),(-58535330094719529469/2361183241434822606848:ℚ)⟩ node247 node274
def node281 : BoxExpr 3 := .add ⟨(-295516718782889001191/2361183241434822606848:ℚ),(255856065158188557259/1180591620717411303424:ℚ)⟩ node279 node280
def node282 : BoxExpr 3 := .add ⟨(-295516718782889001191/1180591620717411303424:ℚ),(255856065158188557259/590295810358705651712:ℚ)⟩ node278 node281
def node283 : BoxExpr 3 := .neg ⟨(-255856065158188557259/590295810358705651712:ℚ),(295516718782889001191/1180591620717411303424:ℚ)⟩ node282
def node284 : BoxExpr 3 := .mul ⟨(-1570044392915827903273/2361183241434822606848:ℚ),(-247228227183937672835/2361183241434822606848:ℚ)⟩ node241 node246
def node285 : BoxExpr 3 := .mul ⟨(-877498557698612782933/4722366482869645213696:ℚ),(-58535330094719529469/2361183241434822606848:ℚ)⟩ node284 node247
def node286 : BoxExpr 3 := .add ⟨(-295516718782889001191/2361183241434822606848:ℚ),(255856065158188557259/1180591620717411303424:ℚ)⟩ node285 node279
def node287 : BoxExpr 3 := .mul ⟨(-877498557698612782933/4722366482869645213696:ℚ),(-58535330094719529469/2361183241434822606848:ℚ)⟩ node247 node284
def node288 : BoxExpr 3 := .add ⟨(-295516718782889001191/2361183241434822606848:ℚ),(255856065158188557259/1180591620717411303424:ℚ)⟩ node277 node287
def node289 : BoxExpr 3 := .add ⟨(-295516718782889001191/1180591620717411303424:ℚ),(255856065158188557259/590295810358705651712:ℚ)⟩ node286 node288
def node290 : BoxExpr 3 := .neg ⟨(-255856065158188557259/590295810358705651712:ℚ),(295516718782889001191/1180591620717411303424:ℚ)⟩ node289
def node291 : BoxExpr 3 := .mul ⟨(-12083126334358688863885/2361183241434822606848:ℚ),(-9957485282878411566165/2361183241434822606848:ℚ)⟩ node244 node246
def node292 : BoxExpr 3 := .mul ⟨(-1688316263338025244095/1180591620717411303424:ℚ),(-4715195304239660837613/4722366482869645213696:ℚ)⟩ node291 node247
def node293 : BoxExpr 3 := .mul ⟨(12026763905950016473/4722366482869645213696:ℚ),(139152886782986630285/4722366482869645213696:ℚ)⟩ node276 node276
def node294 : BoxExpr 3 := .add ⟨(-6741238289446150959907/4722366482869645213696:ℚ),(-143001325545521068979/147573952589676412928:ℚ)⟩ node292 node293
def node295 : BoxExpr 3 := .mul ⟨(-1688316263338025244095/1180591620717411303424:ℚ),(-4715195304239660837613/4722366482869645213696:ℚ)⟩ node247 node291
def node296 : BoxExpr 3 := .add ⟨(-6741238289446150959907/4722366482869645213696:ℚ),(-143001325545521068979/147573952589676412928:ℚ)⟩ node293 node295
def node297 : BoxExpr 3 := .add ⟨(-6741238289446150959907/2361183241434822606848:ℚ),(-143001325545521068979/73786976294838206464:ℚ)⟩ node294 node296
def node298 : BoxExpr 3 := .neg ⟨(143001325545521068979/73786976294838206464:ℚ),(6741238289446150959907/2361183241434822606848:ℚ)⟩ node297
def node301 : BoxExpr 3 := .lit (1/2:ℚ)
def node304 : BoxExpr 3 := .inv ⟨(5608679599763125114383/4722366482869645213696:ℚ),(2815025822917362847029/2361183241434822606848:ℚ)⟩ node16
def node306 : BoxExpr 3 := .mul ⟨(938626831624067721723/4722366482869645213696:ℚ),(118508945573725876519/590295810358705651712:ℚ)⟩ node13 node301
def node308 : BoxExpr 3 := .lit (-1886104779486749201381471199754505392441916025864035703364771907920146519389705837816997363452447960883131061278435345/43624816861295183480575856049041147371514908121470076568809273260400089500027672742507792890927579075052513478012043264:ℚ)
def node312 : BoxExpr 3 := .sqrt ⟨(4533599411214240034727/4722366482869645213696:ℚ),(4587472173287055931965/4722366482869645213696:ℚ)⟩ node250
def node313 : BoxExpr 3 := .lit (287742466255497847992269652017807647746707759403503/182628568201966125342452015454275643968150995402752:ℚ)
def node314 : BoxExpr 3 := .mul ⟨(3571481418379795453269/2361183241434822606848:ℚ),(1806960666143298416207/1180591620717411303424:ℚ)⟩ node312 node313
def node315 : BoxExpr 3 := .lit (3/2:ℚ)
def node316 : BoxExpr 3 := .mul ⟨(10714444255139386359807/4722366482869645213696:ℚ),(5420881998429895248621/2361183241434822606848:ℚ)⟩ node314 node315
def node318 : BoxExpr 3 := .lit (3/1:ℚ)
def node319 : BoxExpr 3 := .sqrt ⟨(8179378680290567732005/4722366482869645213696:ℚ),(4089689340145283866003/2361183241434822606848:ℚ)⟩ node318
def node320 : BoxExpr 3 := .mul ⟨(2044844670072641933001/2361183241434822606848:ℚ),(4089689340145283866003/4722366482869645213696:ℚ)⟩ node319 node301
def node321 : BoxExpr 3 := .mul ⟨(294233257564094231095/590295810358705651712:ℚ),(1176933030256376924381/2361183241434822606848:ℚ)⟩ node320 node203
def node322 : BoxExpr 3 := .mul ⟨(4747823036598744829265/4722366482869645213696:ℚ),(1190486558240455338091/1180591620717411303424:ℚ)⟩ node321 node1
def node323 : BoxExpr 3 := .neg ⟨(-1190486558240455338091/1180591620717411303424:ℚ),(-4747823036598744829265/4722366482869645213696:ℚ)⟩ node322
def node325 : BoxExpr 3 := .lit (-3/1000000:ℚ)
def node332 : BoxExpr 3 := .lit (-1/40:ℚ)
def node335 : BoxExpr 3 := .lit (357/500:ℚ)
def node340 : BoxExpr 3 := .lit (413/500:ℚ)
def node349 : BoxExpr 3 := .inv ⟨(5619318555138810741159/4722366482869645213696:ℚ),(5619318555138810741161/4722366482869645213696:ℚ)⟩ node54
def node351 : BoxExpr 3 := .mul ⟨(943349198106937366937/4722366482869645213696:ℚ),(471674599053468683469/2361183241434822606848:ℚ)⟩ node51 node301
def node356 : BoxExpr 3 := .sqrt ⟨(4560915926422751217325/4722366482869645213696:ℚ),(2280457963211375608673/2361183241434822606848:ℚ)⟩ node254
def node357 : BoxExpr 3 := .mul ⟨(7186001675277507967931/4722366482869645213696:ℚ),(3593000837638753983983/2361183241434822606848:ℚ)⟩ node356 node313
def node358 : BoxExpr 3 := .mul ⟨(1347375314114532743987/590295810358705651712:ℚ),(10779002512916261951949/4722366482869645213696:ℚ)⟩ node357 node315
def node360 : BoxExpr 3 := .mul ⟨(1188721158695070772703/1180591620717411303424:ℚ),(4754884634780283090817/4722366482869645213696:ℚ)⟩ node321 node44
def node361 : BoxExpr 3 := .neg ⟨(-4754884634780283090817/4722366482869645213696:ℚ),(-1188721158695070772703/1180591620717411303424:ℚ)⟩ node360
def node381 : BoxExpr 3 := .mul ⟨(4560915926422751217325/2361183241434822606848:ℚ),(2280457963211375608673/1180591620717411303424:ℚ)⟩ node86 node356
def node382 : BoxExpr 3 := .inv ⟨(2444766090659085683355/4722366482869645213696:ℚ),(2444766090659085683367/4722366482869645213696:ℚ)⟩ node381
def node383 : BoxExpr 3 := .mul ⟨(1641417929653866236565/4722366482869645213696:ℚ),(820708964826933118371/2361183241434822606848:ℚ)⟩ node259 node382
def node384 : BoxExpr 3 := .mul ⟨(1293077112427123662531/2361183241434822606848:ℚ),(1293077112427123662671/2361183241434822606848:ℚ)⟩ node383 node313
def node385 : BoxExpr 3 := .mul ⟨(3879231337281370987593/4722366482869645213696:ℚ),(3879231337281370988013/4722366482869645213696:ℚ)⟩ node384 node315
def node387 : BoxExpr 3 := .neg ⟨(-1176933030256376924381/2361183241434822606848:ℚ),(-294233257564094231095/590295810358705651712:ℚ)⟩ node321
def node396 : BoxExpr 3 := .mul ⟨(3335122253056120841147/4722366482869645213696:ℚ),(1667561126528060420575/2361183241434822606848:ℚ)⟩ node54 node54
def node397 : BoxExpr 3 := .inv ⟨(6686635003588086928419/4722366482869645213696:ℚ),(3343317501794043464213/2361183241434822606848:ℚ)⟩ node396
def node398 : BoxExpr 3 := .mul ⟨(-5342941333799670338881/4722366482869645213696:ℚ),(-667867666724958792359/590295810358705651712:ℚ)⟩ node85 node397
def node399 : BoxExpr 3 := .neg ⟨(667867666724958792359/590295810358705651712:ℚ),(5342941333799670338881/4722366482869645213696:ℚ)⟩ node398
def node402 : BoxExpr 3 := .lit (-1886104779486749201381471199754505392441916025864035703364771907920146519389705837816997363452447960883131061278435345/87249633722590366961151712098082294743029816242940153137618546520800179000055345485015585781855158150105026956024086528:ℚ)
def node403 : BoxExpr 3 := .mul ⟨(-111358628465766203533/4722366482869645213696:ℚ),(-111358628465766203531/4722366482869645213696:ℚ)⟩ node402 node69
def node407 : BoxExpr 3 := .mul ⟨(17026592217487914599/590295810358705651712:ℚ),(17026592217487914605/590295810358705651712:ℚ)⟩ node264 node382
def node408 : BoxExpr 3 := .mul ⟨(214611489749779220183/4722366482869645213696:ℚ),(53652872437444805065/1180591620717411303424:ℚ)⟩ node407 node313
def node409 : BoxExpr 3 := .mul ⟨(160958617312334415137/2361183241434822606848:ℚ),(160958617312334415195/2361183241434822606848:ℚ)⟩ node408 node315
def node411 : BoxExpr 3 := .mul ⟨(1985879505045154496735/2361183241434822606848:ℚ),(1985879505045154496741/2361183241434822606848:ℚ)⟩ node68 node51
def node412 : BoxExpr 3 := .mul ⟨(4726142958811166820663/4722366482869645213696:ℚ),(590767869851395852585/590295810358705651712:ℚ)⟩ node411 node349
def node413 : BoxExpr 3 := .mul ⟨(-27839657116441550883/590295810358705651712:ℚ),(-111358628465766203531/2361183241434822606848:ℚ)⟩ node308 node69
def node414 : BoxExpr 3 := .add ⟨(4503425701879634413599/4722366482869645213696:ℚ),(2251712850939817206809/2361183241434822606848:ℚ)⟩ node412 node413
def node422 : BoxExpr 3 := .lit (-1/1:ℚ)
def node432 : BoxExpr 3 := .mul ⟨(4533599411214240034727/2361183241434822606848:ℚ),(4587472173287055931965/2361183241434822606848:ℚ)⟩ node86 node312
def node433 : BoxExpr 3 := .inv ⟨(2430613675259799662433/4722366482869645213696:ℚ),(1229748328853661583623/2361183241434822606848:ℚ)⟩ node432
def node434 : BoxExpr 3 := .mul ⟨(5617454417546952105553/4722366482869645213696:ℚ),(3735436178162083236107/1180591620717411303424:ℚ)⟩ node273 node433
def node435 : BoxExpr 3 := .mul ⟨(-464164135970199699675/1180591620717411303424:ℚ),(-335998413653499602299/1180591620717411303424:ℚ)⟩ node267 node247
def node436 : BoxExpr 3 := .mul ⟨(-464164135970199699675/1180591620717411303424:ℚ),(-335998413653499602299/1180591620717411303424:ℚ)⟩ node247 node267
def node437 : BoxExpr 3 := .add ⟨(-464164135970199699675/590295810358705651712:ℚ),(-335998413653499602299/590295810358705651712:ℚ)⟩ node435 node436
def node438 : BoxExpr 3 := .neg ⟨(335998413653499602299/590295810358705651712:ℚ),(464164135970199699675/590295810358705651712:ℚ)⟩ node437
def node439 : BoxExpr 3 := .mul ⟨(1383513697302918238495/4722366482869645213696:ℚ),(60436337649116035541/147573952589676412928:ℚ)⟩ node438 node433
def node440 : BoxExpr 3 := .mul ⟨(1383513697302918238495/2361183241434822606848:ℚ),(60436337649116035541/73786976294838206464:ℚ)⟩ node86 node439
def node441 : BoxExpr 3 := .mul ⟨(17409511689463223056279/4722366482869645213696:ℚ),(17825724468461573447095/4722366482869645213696:ℚ)⟩ node432 node432
def node442 : BoxExpr 3 := .inv ⟨(312760713288070651493/1180591620717411303424:ℚ),(1280951792118771857959/4722366482869645213696:ℚ)⟩ node441
def node443 : BoxExpr 3 := .mul ⟨(733037103125180620167/4722366482869645213696:ℚ),(524591458466811131897/2361183241434822606848:ℚ)⟩ node440 node442
def node444 : BoxExpr 3 := .neg ⟨(-524591458466811131897/2361183241434822606848:ℚ),(-733037103125180620167/4722366482869645213696:ℚ)⟩ node443
def node445 : BoxExpr 3 := .mul ⟨(-412499185634789617579/2361183241434822606848:ℚ),(-52155906300933369575/590295810358705651712:ℚ)⟩ node438 node444
def node446 : BoxExpr 3 := .add ⟨(4792456046277372870395/4722366482869645213696:ℚ),(3631124365560216496957/1180591620717411303424:ℚ)⟩ node434 node445
def node447 : BoxExpr 3 := .mul ⟨(3775403639620928054241/2361183241434822606848:ℚ),(22884233075107212276187/4722366482869645213696:ℚ)⟩ node446 node313
def node448 : BoxExpr 3 := .mul ⟨(11326210918862784162723/4722366482869645213696:ℚ),(34326349612660818414281/4722366482869645213696:ℚ)⟩ node447 node315
def node458 : BoxExpr 3 := .mul ⟨(3322418266985942863501/4722366482869645213696:ℚ),(3347786862908889618591/4722366482869645213696:ℚ)⟩ node16 node16
def node459 : BoxExpr 3 := .inv ⟨(1665334899721895791211/1180591620717411303424:ℚ),(6712202801232966340575/4722366482869645213696:ℚ)⟩ node458
def node460 : BoxExpr 3 := .mul ⟨(-5390220038781927845849/4722366482869645213696:ℚ),(-1324020934155944627541/1180591620717411303424:ℚ)⟩ node127 node459
def node461 : BoxExpr 3 := .neg ⟨(1324020934155944627541/1180591620717411303424:ℚ),(5390220038781927845849/4722366482869645213696:ℚ)⟩ node460
def node464 : BoxExpr 3 := .mul ⟨(-1066036936173269434493/4722366482869645213696:ℚ),(307821252238552030869/2361183241434822606848:ℚ)⟩ node283 node433
def node465 : BoxExpr 3 := .mul ⟨(-113266229041722771185/2361183241434822606848:ℚ),(-56425348983646735205/4722366482869645213696:ℚ)⟩ node276 node247
def node466 : BoxExpr 3 := .mul ⟨(-113266229041722771185/2361183241434822606848:ℚ),(-56425348983646735205/4722366482869645213696:ℚ)⟩ node247 node276
def node467 : BoxExpr 3 := .add ⟨(-113266229041722771185/1180591620717411303424:ℚ),(-56425348983646735205/2361183241434822606848:ℚ)⟩ node465 node466
def node468 : BoxExpr 3 := .neg ⟨(56425348983646735205/2361183241434822606848:ℚ),(113266229041722771185/1180591620717411303424:ℚ)⟩ node467
def node469 : BoxExpr 3 := .mul ⟨(58084532561571711033/4722366482869645213696:ℚ),(58991167409342100851/1180591620717411303424:ℚ)⟩ node468 node433
def node470 : BoxExpr 3 := .mul ⟨(58084532561571711033/2361183241434822606848:ℚ),(58991167409342100851/590295810358705651712:ℚ)⟩ node86 node469
def node471 : BoxExpr 3 := .mul ⟨(15387674718478894593/2361183241434822606848:ℚ),(128011820999130399561/4722366482869645213696:ℚ)⟩ node470 node442
def node472 : BoxExpr 3 := .neg ⟨(-128011820999130399561/4722366482869645213696:ℚ),(-15387674718478894593/2361183241434822606848:ℚ)⟩ node471
def node473 : BoxExpr 3 := .mul ⟨(-12582356008067872415/590295810358705651712:ℚ),(-8758717586159332837/2361183241434822606848:ℚ)⟩ node438 node472
def node474 : BoxExpr 3 := .add ⟨(-1166695784237812413813/4722366482869645213696:ℚ),(18691408415774543627/147573952589676412928:ℚ)⟩ node464 node473
def node475 : BoxExpr 3 := .mul ⟨(-919100241631490280653/2361183241434822606848:ℚ),(58898911690485823871/295147905179352825856:ℚ)⟩ node474 node313
def node476 : BoxExpr 3 := .mul ⟨(-2757300724894470841959/4722366482869645213696:ℚ),(176696735071457471613/590295810358705651712:ℚ)⟩ node475 node315
def node478 : BoxExpr 3 := .mul ⟨(259524100115899746407/1180591620717411303424:ℚ),(550949646635346069789/2361183241434822606848:ℚ)⟩ node118 node13
def node479 : BoxExpr 3 := .mul ⟨(1232930592106363975947/4722366482869645213696:ℚ),(656847573364630350863/2361183241434822606848:ℚ)⟩ node478 node304
def node488 : BoxExpr 3 := .mul ⟨(-1066036936173269434493/4722366482869645213696:ℚ),(307821252238552030869/2361183241434822606848:ℚ)⟩ node290 node433
def node489 : BoxExpr 3 := .mul ⟨(-100658848064542979319/4722366482869645213696:ℚ),(-8758717586159332837/2361183241434822606848:ℚ)⟩ node468 node444
def node490 : BoxExpr 3 := .add ⟨(-291673946059453103453/1180591620717411303424:ℚ),(18691408415774543627/147573952589676412928:ℚ)⟩ node488 node489
def node491 : BoxExpr 3 := .mul ⟨(-1838200483262980561305/4722366482869645213696:ℚ),(58898911690485823871/295147905179352825856:ℚ)⟩ node490 node313
def node492 : BoxExpr 3 := .mul ⟨(-1378650362447235420979/2361183241434822606848:ℚ),(176696735071457471613/590295810358705651712:ℚ)⟩ node491 node315
def node504 : BoxExpr 3 := .mul ⟨(-6712202801232966340575/2361183241434822606848:ℚ),(-1665334899721895791211/590295810358705651712:ℚ)⟩ node6 node459
def node505 : BoxExpr 3 := .mul ⟨(-3193009192516380884537/4722366482869645213696:ℚ),(-1574600081284493365345/2361183241434822606848:ℚ)⟩ node127 node16
def node506 : BoxExpr 3 := .mul ⟨(-3193009192516380884537/4722366482869645213696:ℚ),(-1574600081284493365345/2361183241434822606848:ℚ)⟩ node16 node127
def node507 : BoxExpr 3 := .add ⟨(-3193009192516380884537/2361183241434822606848:ℚ),(-1574600081284493365345/1180591620717411303424:ℚ)⟩ node505 node506
def node508 : BoxExpr 3 := .mul ⟨(2337485491827843454691/4722366482869645213696:ℚ),(2373317894771852640241/4722366482869645213696:ℚ)⟩ node458 node458
def node509 : BoxExpr 3 := .inv ⟨(2349110631961336630737/1180591620717411303424:ℚ),(9540484968354652818637/4722366482869645213696:ℚ)⟩ node508
def node510 : BoxExpr 3 := .mul ⟨(-3225380359140335611229/1180591620717411303424:ℚ),(-12532393851092617394479/4722366482869645213696:ℚ)⟩ node507 node509
def node511 : BoxExpr 3 := .neg ⟨(12532393851092617394479/4722366482869645213696:ℚ),(3225380359140335611229/1180591620717411303424:ℚ)⟩ node510
def node512 : BoxExpr 3 := .mul ⟨(-10360539071518124688133/4722366482869645213696:ℚ),(-9963852806246271002681/4722366482869645213696:ℚ)⟩ node127 node511
def node513 : BoxExpr 3 := .add ⟨(-23784944673984057369283/4722366482869645213696:ℚ),(-23286532004021437332369/4722366482869645213696:ℚ)⟩ node504 node512
def node514 : BoxExpr 3 := .neg ⟨(23286532004021437332369/4722366482869645213696:ℚ),(23784944673984057369283/4722366482869645213696:ℚ)⟩ node513
def node518 : BoxExpr 3 := .mul ⟨(-6669793209887575063/590295810358705651712:ℚ),(-26263136035815392967/2361183241434822606848:ℚ)⟩ node402 node136
def node523 : BoxExpr 3 := .mul ⟨(4710600635840625837895/4722366482869645213696:ℚ),(3510962798386249577057/2361183241434822606848:ℚ)⟩ node298 node433
def node524 : BoxExpr 3 := .mul ⟨(-12281483268977163869/4722366482869645213696:ℚ),(-367720260249431685/2361183241434822606848:ℚ)⟩ node468 node472
def node525 : BoxExpr 3 := .add ⟨(2349159576285824337013/2361183241434822606848:ℚ),(877648769531500036343/590295810358705651712:ℚ)⟩ node523 node524
def node526 : BoxExpr 3 := .mul ⟨(7402488852244380914349/4722366482869645213696:ℚ),(11062314026218297649695/4722366482869645213696:ℚ)⟩ node525 node313
def node527 : BoxExpr 3 := .mul ⟨(11103733278366571371523/4722366482869645213696:ℚ),(16593471039327446474543/4722366482869645213696:ℚ)⟩ node526 node315
def node529 : BoxExpr 3 := .mul ⟨(-57204713784735629119/147573952589676412928:ℚ),(-884305542157928933957/2361183241434822606848:ℚ)⟩ node148 node13
def node530 : BoxExpr 3 := .add ⟨(8076240392163136551127/4722366482869645213696:ℚ),(8207244329505179498505/4722366482869645213696:ℚ)⟩ node529 node36
def node531 : BoxExpr 3 := .mul ⟨(9592022324955733713563/4722366482869645213696:ℚ),(9784757200169600967561/4722366482869645213696:ℚ)⟩ node530 node304
def node532 : BoxExpr 3 := .mul ⟨(984546635736655182275/1180591620717411303424:ℚ),(4005544628783559212985/4722366482869645213696:ℚ)⟩ node36 node13
def node533 : BoxExpr 3 := .mul ⟨(1104158570578370606741/1180591620717411303424:ℚ),(4572022735343567862705/4722366482869645213696:ℚ)⟩ node532 node461
def node534 : BoxExpr 3 := .add ⟨(14008656607269216140527/4722366482869645213696:ℚ),(7178389967756584415133/2361183241434822606848:ℚ)⟩ node531 node533
def node535 : BoxExpr 3 := .mul ⟨(-106716691358201201007/4722366482869645213696:ℚ),(-26263136035815392967/1180591620717411303424:ℚ)⟩ node308 node136
def node536 : BoxExpr 3 := .add ⟨(108608905593054804215/36893488147419103232:ℚ),(7125863695684953629199/2361183241434822606848:ℚ)⟩ node534 node535
def node546 : BoxExpr 3 := .lit (413/250:ℚ)
def node1508 : BoxExpr 3 := .var 2
def node1509 : BoxExpr 3 := .mul ⟨(-220722911131064445017/2361183241434822606848:ℚ),(-435306525720966563521/4722366482869645213696:ℚ)⟩ node13 node1508
def node1510 : BoxExpr 3 := .add ⟨(959868709586346858407/2361183241434822606848:ℚ),(1925876715713856043327/4722366482869645213696:ℚ)⟩ node1509 node301
def node1511 : BoxExpr 3 := .mul ⟨(2013655431385795580155/2361183241434822606848:ℚ),(2034177962521368270399/2361183241434822606848:ℚ)⟩ node36 node1510
def node1512 : BoxExpr 3 := .mul ⟨(4783173089142680057069/4722366482869645213696:ℚ),(2425166921575893817775/2361183241434822606848:ℚ)⟩ node1511 node304
def node1513 : BoxExpr 3 := .add ⟨(-160799115169021554591/4722366482869645213696:ℚ),(-36743320121444061413/1180591620717411303424:ℚ)⟩ node1508 node306
def node1514 : BoxExpr 3 := .mul ⟨(3177171008676632259/2361183241434822606848:ℚ),(1738024371665680535/1180591620717411303424:ℚ)⟩ node1513 node308
def node1515 : BoxExpr 3 := .mul ⟨(6925020421050236509/4722366482869645213696:ℚ),(3795440637518771473/2361183241434822606848:ℚ)⟩ node1514 node37
def node1516 : BoxExpr 3 := .add ⟨(2395049054781865146789/2361183241434822606848:ℚ),(37952536909584571707/36893488147419103232:ℚ)⟩ node1512 node1515
def node1517 : BoxExpr 3 := .add ⟨(15504542364703116653385/4722366482869645213696:ℚ),(7849844360643307837869/2361183241434822606848:ℚ)⟩ node1516 node316
def node1518 : BoxExpr 3 := .add ⟨(10742596131741295301021/4722366482869645213696:ℚ),(10951865684687870846473/4722366482869645213696:ℚ)⟩ node1517 node323
def node1519 : BoxExpr 3 := .add ⟨(10742581964641846692085/4722366482869645213696:ℚ),(5475925758794211118769/2361183241434822606848:ℚ)⟩ node1518 node325
def node1520 : BoxExpr 3 := .mul ⟨(253924217249216059145/4722366482869645213696:ℚ),(127980051618883048571/2361183241434822606848:ℚ)⟩ node1508 node1508
def node1521 : BoxExpr 3 := .neg ⟨(-127980051618883048571/2361183241434822606848:ℚ),(-253924217249216059145/4722366482869645213696:ℚ)⟩ node1520
def node1522 : BoxExpr 3 := .add ⟨(2233203189815939558277/2361183241434822606848:ℚ),(4468442265620429154551/4722366482869645213696:ℚ)⟩ node12 node1521
def node1523 : BoxExpr 3 := .sqrt ⟨(4592603595570680468649/4722366482869645213696:ℚ),(4593650181043830312063/4722366482869645213696:ℚ)⟩ node1522
def node1524 : BoxExpr 3 := .mul ⟨(2842328179510260813303/1180591620717411303424:ℚ),(11388952225297534405973/4722366482869645213696:ℚ)⟩ node11 node1523
def node1525 : BoxExpr 3 := .neg ⟨(273761211268895814451/1180591620717411303424:ℚ),(549712973396544638157/2361183241434822606848:ℚ)⟩ node1508
def node1526 : BoxExpr 3 := .add ⟨(976985683003842127461/4722366482869645213696:ℚ),(245341696180337036493/1180591620717411303424:ℚ)⟩ node332 node1525
def node1527 : BoxExpr 3 := .mul ⟨(348783888832371639503/2361183241434822606848:ℚ),(700695884291042576225/4722366482869645213696:ℚ)⟩ node1526 node335
def node1528 : BoxExpr 3 := .neg ⟨(-700695884291042576225/4722366482869645213696:ℚ),(-348783888832371639503/2361183241434822606848:ℚ)⟩ node1527
def node1529 : BoxExpr 3 := .add ⟨(10668616833750000676987/4722366482869645213696:ℚ),(10691384447632791126967/4722366482869645213696:ℚ)⟩ node1524 node1528
def node1530 : BoxExpr 3 := .mul ⟨(202123454047230424513/4722366482869645213696:ℚ),(203940284949905161585/4722366482869645213696:ℚ)⟩ node1526 node1526
def node1531 : BoxExpr 3 := .mul ⟨(166953973043012330647/4722366482869645213696:ℚ),(84227337684310831735/2361183241434822606848:ℚ)⟩ node1530 node340
def node1532 : BoxExpr 3 := .add ⟨(5417785403396506503817/2361183241434822606848:ℚ),(10859839123001412790437/4722366482869645213696:ℚ)⟩ node1529 node1531
def node1533 : BoxExpr 3 := .neg ⟨(-10859839123001412790437/4722366482869645213696:ℚ),(-5417785403396506503817/2361183241434822606848:ℚ)⟩ node1532
def node1534 : BoxExpr 3 := .add ⟨(-7328572397472881147/295147905179352825856:ℚ),(7267544424713076869/295147905179352825856:ℚ)⟩ node1519 node1533
def node1535 : BoxExpr 3 := .var 2
def node1536 : BoxExpr 3 := .mul ⟨(-54796474111228777595/590295810358705651712:ℚ),(-219185896444915110379/2361183241434822606848:ℚ)⟩ node51 node1535
def node1537 : BoxExpr 3 := .add ⟨(240351431068124048261/590295810358705651712:ℚ),(961405724272496193045/2361183241434822606848:ℚ)⟩ node1536 node301
def node1538 : BoxExpr 3 := .mul ⟨(505972742569028358167/590295810358705651712:ℚ),(2023890970276113432675/2361183241434822606848:ℚ)⟩ node68 node1537
def node1539 : BoxExpr 3 := .mul ⟨(75259460246954146645/73786976294838206464:ℚ),(4816605455805065385299/4722366482869645213696:ℚ)⟩ node1538 node349
def node1540 : BoxExpr 3 := .add ⟨(-153886197827398900123/4722366482869645213696:ℚ),(-153886197827398900121/4722366482869645213696:ℚ)⟩ node1535 node351
def node1541 : BoxExpr 3 := .mul ⟨(6653219752007993329/4722366482869645213696:ℚ),(3326609876003996665/2361183241434822606848:ℚ)⟩ node1540 node308
def node1542 : BoxExpr 3 := .mul ⟨(7257613737533273445/4722366482869645213696:ℚ),(7257613737533273447/4722366482869645213696:ℚ)⟩ node1541 node69
def node1543 : BoxExpr 3 := .add ⟨(4823863069542598658725/4722366482869645213696:ℚ),(2411931534771299329373/2361183241434822606848:ℚ)⟩ node1539 node1542
def node1544 : BoxExpr 3 := .add ⟨(15602865582458860610621/4722366482869645213696:ℚ),(15602865582458860610695/4722366482869645213696:ℚ)⟩ node1543 node358
def node1545 : BoxExpr 3 := .add ⟨(2711995236919644379951/1180591620717411303424:ℚ),(10847980947678577519883/4722366482869645213696:ℚ)⟩ node1544 node361
def node1546 : BoxExpr 3 := .add ⟨(2711991695144782227717/1180591620717411303424:ℚ),(2711991695144782227737/1180591620717411303424:ℚ)⟩ node1545 node325
def node1547 : BoxExpr 3 := .mul ⟨(254941144118825152675/4722366482869645213696:ℚ),(254941144118825152677/4722366482869645213696:ℚ)⟩ node1535 node1535
def node1548 : BoxExpr 3 := .neg ⟨(-254941144118825152677/4722366482869645213696:ℚ),(-254941144118825152675/4722366482869645213696:ℚ)⟩ node1547
def node1549 : BoxExpr 3 := .add ⟨(4467425338750820061019/4722366482869645213696:ℚ),(4467425338750820061021/4722366482869645213696:ℚ)⟩ node12 node1548
def node1550 : BoxExpr 3 := .sqrt ⟨(4593127440474457755229/4722366482869645213696:ℚ),(4593127440474457755231/4722366482869645213696:ℚ)⟩ node1549
def node1551 : BoxExpr 3 := .mul ⟨(711189448545104196587/295147905179352825856:ℚ),(5689515588360833572703/2361183241434822606848:ℚ)⟩ node50 node1550
def node1552 : BoxExpr 3 := .neg ⟨(1097235395934336267059/4722366482869645213696:ℚ),(274308848983584066765/1180591620717411303424:ℚ)⟩ node1535
def node1553 : BoxExpr 3 := .add ⟨(244794058465648784179/1180591620717411303424:ℚ),(489588116931297568359/2361183241434822606848:ℚ)⟩ node332 node1552
def node1554 : BoxExpr 3 := .mul ⟨(699131830977892927615/4722366482869645213696:ℚ),(699131830977892927617/4722366482869645213696:ℚ)⟩ node1553 node335
def node1555 : BoxExpr 3 := .neg ⟨(-699131830977892927617/4722366482869645213696:ℚ),(-699131830977892927615/4722366482869645213696:ℚ)⟩ node1554
def node1556 : BoxExpr 3 := .add ⟨(10679899345743774217775/4722366482869645213696:ℚ),(10679899345743774217791/4722366482869645213696:ℚ)⟩ node1551 node1555
def node1557 : BoxExpr 3 := .mul ⟨(203030853373901867581/4722366482869645213696:ℚ),(101515426686950933791/2361183241434822606848:ℚ)⟩ node1553 node1553
def node1558 : BoxExpr 3 := .mul ⟨(167703484886842942621/4722366482869645213696:ℚ),(167703484886842942623/4722366482869645213696:ℚ)⟩ node1557 node340
def node1559 : BoxExpr 3 := .add ⟨(2711900707657654290099/1180591620717411303424:ℚ),(5423801415315308580207/2361183241434822606848:ℚ)⟩ node1556 node1558
def node1560 : BoxExpr 3 := .neg ⟨(-5423801415315308580207/2361183241434822606848:ℚ),(-2711900707657654290099/1180591620717411303424:ℚ)⟩ node1559
def node1561 : BoxExpr 3 := .add ⟨(181974974255875227/2361183241434822606848:ℚ),(45493743563968819/590295810358705651712:ℚ)⟩ node1546 node1560
def node1562 : BoxExpr 3 := .mul ⟨(1090321458131647581845/4722366482869645213696:ℚ),(1090321458131647581851/4722366482869645213696:ℚ)⟩ node78 node1537
def node1563 : BoxExpr 3 := .mul ⟨(324353458322767329051/1180591620717411303424:ℚ),(1297413833291069316213/4722366482869645213696:ℚ)⟩ node1562 node349
def node1564 : BoxExpr 3 := .add ⟨(5176645170572440303797/4722366482869645213696:ℚ),(2588322585286220152113/2361183241434822606848:ℚ)⟩ node1563 node385
def node1565 : BoxExpr 3 := .add ⟨(2822779110059686455035/4722366482869645213696:ℚ),(1411389555029843227733/2361183241434822606848:ℚ)⟩ node1564 node387
def node1566 : BoxExpr 3 := .mul ⟨(177569493242965946731/295147905179352825856:ℚ),(2841111891887455147705/4722366482869645213696:ℚ)⟩ node77 node1550
def node1567 : BoxExpr 3 := .neg ⟨(-2841111891887455147705/4722366482869645213696:ℚ),(-177569493242965946731/295147905179352825856:ℚ)⟩ node1566
def node1568 : BoxExpr 3 := .add ⟨(-9166390913884346335/2361183241434822606848:ℚ),(-9166390913884346115/2361183241434822606848:ℚ)⟩ node1565 node1567
def node1569 : BoxExpr 3 := .mul ⟨(-916934506540496787333/2361183241434822606848:ℚ),(-1833869013080993574655/4722366482869645213696:ℚ)⟩ node98 node1537
def node1570 : BoxExpr 3 := .mul ⟨(-2309831067189921518591/4722366482869645213696:ℚ),(-2309831067189921518583/4722366482869645213696:ℚ)⟩ node68 node1535
def node1571 : BoxExpr 3 := .add ⟨(-4143700080270915093257/4722366482869645213696:ℚ),(-2071850040135457546619/2361183241434822606848:ℚ)⟩ node1569 node1570
def node1572 : BoxExpr 3 := .mul ⟨(-4930741998204055631563/4722366482869645213696:ℚ),(-4930741998204055631537/4722366482869645213696:ℚ)⟩ node1571 node349
def node1573 : BoxExpr 3 := .mul ⟨(572463549759330480727/590295810358705651712:ℚ),(286231774879665240365/295147905179352825856:ℚ)⟩ node1538 node399
def node1574 : BoxExpr 3 := .add ⟨(-351033600129411785747/4722366482869645213696:ℚ),(-351033600129411785697/4722366482869645213696:ℚ)⟩ node1572 node1573
def node1575 : BoxExpr 3 := .mul ⟨(862582447554020029/1180591620717411303424:ℚ),(1725164895108040059/2361183241434822606848:ℚ)⟩ node1541 node103
def node1576 : BoxExpr 3 := .add ⟨(-107908298675550123417/4722366482869645213696:ℚ),(-107908298675550123413/4722366482869645213696:ℚ)⟩ node403 node1575
def node1577 : BoxExpr 3 := .add ⟨(-114735474701240477291/1180591620717411303424:ℚ),(-229470949402480954555/2361183241434822606848:ℚ)⟩ node1574 node1576
def node1578 : BoxExpr 3 := .add ⟨(-68512332090146539445/2361183241434822606848:ℚ),(-2141010377817079355/73786976294838206464:ℚ)⟩ node1577 node409
def node1579 : BoxExpr 3 := .add ⟨(-274308848983584066765/590295810358705651712:ℚ),(-1097235395934336267059/2361183241434822606848:ℚ)⟩ node1535 node1535
def node1580 : BoxExpr 3 := .neg ⟨(1097235395934336267059/2361183241434822606848:ℚ),(274308848983584066765/590295810358705651712:ℚ)⟩ node1579
def node1581 : BoxExpr 3 := .mul ⟨(4593127440474457755229/2361183241434822606848:ℚ),(4593127440474457755231/2361183241434822606848:ℚ)⟩ node86 node1550
def node1582 : BoxExpr 3 := .inv ⟨(1213810496635545993445/2361183241434822606848:ℚ),(606905248317772996723/1180591620717411303424:ℚ)⟩ node1581
def node1583 : BoxExpr 3 := .mul ⟨(1128108837546922970665/4722366482869645213696:ℚ),(282027209386730742667/1180591620717411303424:ℚ)⟩ node1580 node1582
def node1584 : BoxExpr 3 := .mul ⟨(2794781072274291038753/4722366482869645213696:ℚ),(2794781072274291038763/4722366482869645213696:ℚ)⟩ node50 node1583
def node1585 : BoxExpr 3 := .add ⟨(6166550741043217721331/4722366482869645213696:ℚ),(3083275370521608860671/2361183241434822606848:ℚ)⟩ node1584 node335
def node1586 : BoxExpr 3 := .mul ⟨(-489588116931297568359/2361183241434822606848:ℚ),(-244794058465648784179/1180591620717411303424:ℚ)⟩ node422 node1553
def node1587 : BoxExpr 3 := .mul ⟨(-489588116931297568359/2361183241434822606848:ℚ),(-244794058465648784179/1180591620717411303424:ℚ)⟩ node1553 node422
def node1588 : BoxExpr 3 := .add ⟨(-489588116931297568359/1180591620717411303424:ℚ),(-244794058465648784179/590295810358705651712:ℚ)⟩ node1586 node1587
def node1589 : BoxExpr 3 := .mul ⟨(-1617599138341007165859/4722366482869645213696:ℚ),(-808799569170503582927/2361183241434822606848:ℚ)⟩ node1588 node340
def node1590 : BoxExpr 3 := .add ⟨(284309475168888159717/295147905179352825856:ℚ),(142154737584444079859/147573952589676412928:ℚ)⟩ node1585 node1589
def node1591 : BoxExpr 3 := .neg ⟨(-142154737584444079859/147573952589676412928:ℚ),(-284309475168888159717/295147905179352825856:ℚ)⟩ node1590
def node1592 : BoxExpr 3 := .add ⟨(-45525900822576141889/4722366482869645213696:ℚ),(-22762950411288070927/2361183241434822606848:ℚ)⟩ node414 node1591
def node1593 : BoxExpr 3 := .mul ⟨(2162572101983604562423/1180591620717411303424:ℚ),(8694470003973048019545/4722366482869645213696:ℚ)⟩ node112 node1510
def node1594 : BoxExpr 3 := .mul ⟨(5136905013793743505231/2361183241434822606848:ℚ),(2591408107200916856859/1180591620717411303424:ℚ)⟩ node1593 node304
def node1595 : BoxExpr 3 := .add ⟨(21600020946450271173185/4722366482869645213696:ℚ),(44691982041464485841717/4722366482869645213696:ℚ)⟩ node1594 node448
def node1596 : BoxExpr 3 := .mul ⟨(2824451211275968488219/590295810358705651712:ℚ),(22600758890735645135351/4722366482869645213696:ℚ)⟩ node111 node1523
def node1597 : BoxExpr 3 := .neg ⟨(-22600758890735645135351/4722366482869645213696:ℚ),(-2824451211275968488219/590295810358705651712:ℚ)⟩ node1596
def node1598 : BoxExpr 3 := .add ⟨(-500368972142686981083/2361183241434822606848:ℚ),(22096372351256737935965/4722366482869645213696:ℚ)⟩ node1595 node1597
def node1599 : BoxExpr 3 := .mul ⟨(-534733652393604501217/4722366482869645213696:ℚ),(-125541309215498200615/1180591620717411303424:ℚ)⟩ node131 node1510
def node1600 : BoxExpr 3 := .mul ⟨(-159726427706292923369/1180591620717411303424:ℚ),(-302772644495014400835/2361183241434822606848:ℚ)⟩ node118 node1508
def node1601 : BoxExpr 3 := .add ⟨(-1173639363218776194693/4722366482869645213696:ℚ),(-553855262926010802065/2361183241434822606848:ℚ)⟩ node1599 node1600
def node1602 : BoxExpr 3 := .mul ⟨(-87451522616831784529/295147905179352825856:ℚ),(-1315610182167349054067/4722366482869645213696:ℚ)⟩ node1601 node304
def node1603 : BoxExpr 3 := .mul ⟨(1061589354541605547891/4722366482869645213696:ℚ),(559589136314234308977/2361183241434822606848:ℚ)⟩ node118 node1510
def node1604 : BoxExpr 3 := .mul ⟨(37205036235245258925/147573952589676412928:ℚ),(638728185749093806821/2361183241434822606848:ℚ)⟩ node1603 node461
def node1605 : BoxExpr 3 := .add ⟨(-13041450146341266679/295147905179352825856:ℚ),(-38153810669161440425/4722366482869645213696:ℚ)⟩ node1602 node1604
def node1606 : BoxExpr 3 := .add ⟨(-2965963927235931108823/4722366482869645213696:ℚ),(1375420069902498332479/4722366482869645213696:ℚ)⟩ node1605 node476
def node1607 : BoxExpr 3 := .add ⟨(-549712973396544638157/1180591620717411303424:ℚ),(-273761211268895814451/590295810358705651712:ℚ)⟩ node1508 node1508
def node1608 : BoxExpr 3 := .neg ⟨(273761211268895814451/590295810358705651712:ℚ),(549712973396544638157/1180591620717411303424:ℚ)⟩ node1607
def node1609 : BoxExpr 3 := .mul ⟨(4592603595570680468649/2361183241434822606848:ℚ),(4593650181043830312063/2361183241434822606848:ℚ)⟩ node86 node1523
def node1610 : BoxExpr 3 := .inv ⟨(2427344738891627040369/4722366482869645213696:ℚ),(2427897894348915097819/4722366482869645213696:ℚ)⟩ node1609
def node1611 : BoxExpr 3 := .mul ⟨(281432132934480879265/1180591620717411303424:ℚ),(1130489957056213592423/4722366482869645213696:ℚ)⟩ node1608 node1610
def node1612 : BoxExpr 3 := .mul ⟨(679711696960161732143/4722366482869645213696:ℚ),(715958695604967907121/4722366482869645213696:ℚ)⟩ node117 node1611
def node1613 : BoxExpr 3 := .neg ⟨(-715958695604967907121/4722366482869645213696:ℚ),(-679711696960161732143/4722366482869645213696:ℚ)⟩ node1612
def node1614 : BoxExpr 3 := .add ⟨(258485948250698034413/2361183241434822606848:ℚ),(633983449769098969583/4722366482869645213696:ℚ)⟩ node479 node1613
def node1615 : BoxExpr 3 := .add ⟨(-1482981963617965554411/2361183241434822606848:ℚ),(1375420069902498332479/4722366482869645213696:ℚ)⟩ node1605 node492
def node1616 : BoxExpr 3 := .mul ⟨(-1978675699942989076775/4722366482869645213696:ℚ),(-481975042069492201041/1180591620717411303424:ℚ)⟩ node175 node1510
def node1617 : BoxExpr 3 := .mul ⟨(515835576389982976575/2361183241434822606848:ℚ),(530697039867632186729/2361183241434822606848:ℚ)⟩ node148 node1508
def node1618 : BoxExpr 3 := .add ⟨(-947004547163023123625/4722366482869645213696:ℚ),(-433253044271352215353/2361183241434822606848:ℚ)⟩ node1616 node1617
def node1619 : BoxExpr 3 := .add ⟨(84666605616942829525/4722366482869645213696:ℚ),(6090249724767498211/147573952589676412928:ℚ)⟩ node1618 node1617
def node1620 : BoxExpr 3 := .mul ⟨(50278590768793301605/2361183241434822606848:ℚ),(232347374890807097821/4722366482869645213696:ℚ)⟩ node1619 node304
def node1621 : BoxExpr 3 := .mul ⟨(-929627934614945728947/2361183241434822606848:ℚ),(-1808636171549693040821/4722366482869645213696:ℚ)⟩ node148 node1510
def node1622 : BoxExpr 3 := .mul ⟨(-2322503838530210261871/4722366482869645213696:ℚ),(-574308490805925775967/1180591620717411303424:ℚ)⟩ node36 node1508
def node1623 : BoxExpr 3 := .add ⟨(-4181759707760101719765/4722366482869645213696:ℚ),(-4105870134773396144689/4722366482869645213696:ℚ)⟩ node1621 node1622
def node1624 : BoxExpr 3 := .mul ⟨(-4773158766035050828961/4722366482869645213696:ℚ),(-4604689645401862017597/4722366482869645213696:ℚ)⟩ node1623 node461
def node1625 : BoxExpr 3 := .add ⟨(-4672601584497464225751/4722366482869645213696:ℚ),(-136635695953470466243/147573952589676412928:ℚ)⟩ node1620 node1624
def node1626 : BoxExpr 3 := .mul ⟨(9929566419322582837695/2361183241434822606848:ℚ),(10245458600283713785747/2361183241434822606848:ℚ)⟩ node1511 node514
def node1627 : BoxExpr 3 := .add ⟨(15085974072610114846429/4722366482869645213696:ℚ),(15886227555165565553897/4722366482869645213696:ℚ)⟩ node1624 node1626
def node1628 : BoxExpr 3 := .add ⟨(5206686244056325310339/2361183241434822606848:ℚ),(11513885284654510634121/4722366482869645213696:ℚ)⟩ node1625 node1627
def node1629 : BoxExpr 3 := .mul ⟨(3212457064350260589/1180591620717411303424:ℚ),(7137498588603953067/2361183241434822606848:ℚ)⟩ node1514 node189
def node1630 : BoxExpr 3 := .add ⟨(-10127129355424889537/1180591620717411303424:ℚ),(-4781409361802859975/590295810358705651712:ℚ)⟩ node518 node1629
def node1631 : BoxExpr 3 := .add ⟨(-23466715775200039663/1180591620717411303424:ℚ),(-45388773483026832867/2361183241434822606848:ℚ)⟩ node518 node1630
def node1632 : BoxExpr 3 := .add ⟨(5159752812505925231013/2361183241434822606848:ℚ),(11423107737688456968387/4722366482869645213696:ℚ)⟩ node1628 node1631
def node1633 : BoxExpr 3 := .add ⟨(21423238903378421833549/4722366482869645213696:ℚ),(14008289388507951721465/2361183241434822606848:ℚ)⟩ node1632 node527
def node1634 : BoxExpr 3 := .mul ⟨(-2427897894348915097819/2361183241434822606848:ℚ),(-2427344738891627040369/2361183241434822606848:ℚ)⟩ node6 node1610
def node1635 : BoxExpr 3 := .mul ⟨(281432132934480879265/590295810358705651712:ℚ),(1130489957056213592423/2361183241434822606848:ℚ)⟩ node86 node1611
def node1636 : BoxExpr 3 := .mul ⟨(17865625518527516466211/4722366482869645213696:ℚ),(558555283202553644319/147573952589676412928:ℚ)⟩ node1609 node1609
def node1637 : BoxExpr 3 := .inv ⟨(623840028383868880827/2361183241434822606848:ℚ),(1248248776702706176017/4722366482869645213696:ℚ)⟩ node1636
def node1638 : BoxExpr 3 := .mul ⟨(148712413943181593193/1180591620717411303424:ℚ),(597637947452400609523/4722366482869645213696:ℚ)⟩ node1635 node1637
def node1639 : BoxExpr 3 := .neg ⟨(-597637947452400609523/4722366482869645213696:ℚ),(-148712413943181593193/1180591620717411303424:ℚ)⟩ node1638
def node1640 : BoxExpr 3 := .mul ⟨(-139137584641262016905/2361183241434822606848:ℚ),(-137936573010970583217/2361183241434822606848:ℚ)⟩ node1608 node1639
def node1641 : BoxExpr 3 := .add ⟨(-641758869747544278681/590295810358705651712:ℚ),(-1282640655951298811793/1180591620717411303424:ℚ)⟩ node1634 node1640
def node1642 : BoxExpr 3 := .mul ⟨(-6364403748354112203967/2361183241434822606848:ℚ),(-6350534035398953192263/2361183241434822606848:ℚ)⟩ node11 node1641
def node1643 : BoxExpr 3 := .add ⟨(-4927458067007570514909/4722366482869645213696:ℚ),(-1224929660274313122875/1180591620717411303424:ℚ)⟩ node1642 node546
def node1644 : BoxExpr 3 := .neg ⟨(1224929660274313122875/1180591620717411303424:ℚ),(4927458067007570514909/4722366482869645213696:ℚ)⟩ node1643
def cert_iv8 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-9517/40960:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/40960:ℚ)],
    whole := node1534, centerValue := node1561, gradient := ![node1568, node1578, node1592],
    hessian := ![![node1598, node1606, node1614], ![node1615, node1633, node536], ![node1614, node536, node1644]] }
def node1645 : BoxExpr 3 := .var 2
def node1646 : BoxExpr 3 := .mul ⟨(-219843352550634448277/2361183241434822606848:ℚ),(-108391233241744148529/1180591620717411303424:ℚ)⟩ node13 node1645
def node1647 : BoxExpr 3 := .add ⟨(960748268166776855147/2361183241434822606848:ℚ),(481904577116961503183/1180591620717411303424:ℚ)⟩ node1646 node301
def node1648 : BoxExpr 3 := .mul ⟨(4031001217285737384397/4722366482869645213696:ℚ),(127251093334672060519/147573952589676412928:ℚ)⟩ node36 node1647
def node1649 : BoxExpr 3 := .mul ⟨(2393778032266594898059/2361183241434822606848:ℚ),(1213680014140342359235/1180591620717411303424:ℚ)⟩ node1648 node304
def node1650 : BoxExpr 3 := .add ⟨(-78209006725757768041/2361183241434822606848:ℚ),(-17824022346033778393/590295810358705651712:ℚ)⟩ node1645 node306
def node1651 : BoxExpr 3 := .mul ⟨(6164926508399300295/4722366482869645213696:ℚ),(6762681977708757917/4722366482869645213696:ℚ)⟩ node1650 node308
def node1652 : BoxExpr 3 := .mul ⟨(3359296827928804749/2361183241434822606848:ℚ),(461503849127066957/295147905179352825856:ℚ)⟩ node1651 node37
def node1653 : BoxExpr 3 := .add ⟨(299642166136815462851/295147905179352825856:ℚ),(1215526029536850627063/1180591620717411303424:ℚ)⟩ node1649 node1652
def node1654 : BoxExpr 3 := .add ⟨(15508718913328433765423/4722366482869645213696:ℚ),(7851934057503596502747/2361183241434822606848:ℚ)⟩ node1653 node316
def node1655 : BoxExpr 3 := .add ⟨(10746772680366612413059/4722366482869645213696:ℚ),(10956045078408448176229/4722366482869645213696:ℚ)⟩ node1654 node323
def node1656 : BoxExpr 3 := .add ⟨(10746758513267163804123/4722366482869645213696:ℚ),(5478015455654499783647/2361183241434822606848:ℚ)⟩ node1655 node325
def node1657 : BoxExpr 3 := .mul ⟨(223729/4194304:ℚ),(253924217249216059147/4722366482869645213696:ℚ)⟩ node1645 node1645
def node1658 : BoxExpr 3 := .neg ⟨(-253924217249216059147/4722366482869645213696:ℚ),(-223729/4194304:ℚ)⟩ node1657
def node1659 : BoxExpr 3 := .add ⟨(4468442265620429154549/4722366482869645213696:ℚ),(3970575/4194304:ℚ)⟩ node12 node1658
def node1660 : BoxExpr 3 := .sqrt ⟨(4593650181043830312061/4722366482869645213696:ℚ),(2297346175343126720321/2361183241434822606848:ℚ)⟩ node1659
def node1661 : BoxExpr 3 := .mul ⟨(5685951806938329667237/2361183241434822606848:ℚ),(11391536057283085239493/4722366482869645213696:ℚ)⟩ node11 node1660
def node1662 : BoxExpr 3 := .neg ⟨(473/2048:ℚ),(1095044845075583257805/4722366482869645213696:ℚ)⟩ node1645
def node1663 : BoxExpr 3 := .add ⟨(972604581286336108953/4722366482869645213696:ℚ),(976985683003842127463/4722366482869645213696:ℚ)⟩ node332 node1662
def node1664 : BoxExpr 3 := .mul ⟨(21701239719951374431/147573952589676412928:ℚ),(697567777664743279009/4722366482869645213696:ℚ)⟩ node1663 node335
def node1665 : BoxExpr 3 := .neg ⟨(-697567777664743279009/4722366482869645213696:ℚ),(-21701239719951374431/147573952589676412928:ℚ)⟩ node1664
def node1666 : BoxExpr 3 := .add ⟨(10674335836211916055465/4722366482869645213696:ℚ),(10697096386244641257701/4722366482869645213696:ℚ)⟩ node1661 node1665
def node1667 : BoxExpr 3 := .mul ⟨(200314752141883091189/4722366482869645213696:ℚ),(202123454047230424515/4722366482869645213696:ℚ)⟩ node1663 node1663
def node1668 : BoxExpr 3 := .mul ⟨(82729992634597716661/2361183241434822606848:ℚ),(83476986521506165325/2361183241434822606848:ℚ)⟩ node1667 node340
def node1669 : BoxExpr 3 := .add ⟨(10839795821481111488787/4722366482869645213696:ℚ),(10864050359287653588351/4722366482869645213696:ℚ)⟩ node1666 node1668
def node1670 : BoxExpr 3 := .neg ⟨(-10864050359287653588351/4722366482869645213696:ℚ),(-10839795821481111488787/4722366482869645213696:ℚ)⟩ node1669
def node1671 : BoxExpr 3 := .add ⟨(-29322961505122446057/1180591620717411303424:ℚ),(116235089827888078507/4722366482869645213696:ℚ)⟩ node1656 node1670
def node1672 : BoxExpr 3 := .var 2
def node1673 : BoxExpr 3 := .mul ⟨(-436621437932405239317/4722366482869645213696:ℚ),(-109155359483101309829/1180591620717411303424:ℚ)⟩ node51 node1672
def node1674 : BoxExpr 3 := .add ⟨(1924561803502417367531/4722366482869645213696:ℚ),(481140450875604341883/1180591620717411303424:ℚ)⟩ node1673 node301
def node1675 : BoxExpr 3 := .mul ⟨(1012866669478775904211/1180591620717411303424:ℚ),(4051466677915103616857/4722366482869645213696:ℚ)⟩ node68 node1674
def node1676 : BoxExpr 3 := .mul ⟨(2410495030544559356937/2361183241434822606848:ℚ),(1205247515272279678473/1180591620717411303424:ℚ)⟩ node1675 node349
def node1677 : BoxExpr 3 := .add ⟨(-74752548054946440807/2361183241434822606848:ℚ),(-37376274027473220403/1180591620717411303424:ℚ)⟩ node1672 node351
def node1678 : BoxExpr 3 := .mul ⟨(3231902121527014553/2361183241434822606848:ℚ),(6463804243054029107/4722366482869645213696:ℚ)⟩ node1677 node308
def node1679 : BoxExpr 3 := .mul ⟨(7050991282372183809/4722366482869645213696:ℚ),(7050991282372183811/4722366482869645213696:ℚ)⟩ node1678 node69
def node1680 : BoxExpr 3 := .add ⟨(4828041052371490897683/4722366482869645213696:ℚ),(4828041052371490897703/4722366482869645213696:ℚ)⟩ node1676 node1679
def node1681 : BoxExpr 3 := .add ⟨(15607043565287752849579/4722366482869645213696:ℚ),(3901760891321938212413/1180591620717411303424:ℚ)⟩ node1680 node358
def node1682 : BoxExpr 3 := .add ⟨(5426079465253734879381/2361183241434822606848:ℚ),(1356519866313433719855/590295810358705651712:ℚ)⟩ node1681 node361
def node1683 : BoxExpr 3 := .add ⟨(5426072381704010574913/2361183241434822606848:ℚ),(10852144763408021149905/4722366482869645213696:ℚ)⟩ node1682 node325
def node1684 : BoxExpr 3 := .mul ⟨(31613665328617352069/590295810358705651712:ℚ),(126454661314469408277/2361183241434822606848:ℚ)⟩ node1672 node1672
def node1685 : BoxExpr 3 := .neg ⟨(-126454661314469408277/2361183241434822606848:ℚ),(-31613665328617352069/590295810358705651712:ℚ)⟩ node1684
def node1686 : BoxExpr 3 := .add ⟨(2234728580120353198571/2361183241434822606848:ℚ),(558682145030088299643/590295810358705651712:ℚ)⟩ node12 node1685
def node1687 : BoxExpr 3 := .sqrt ⟨(4594171817655762966609/4722366482869645213696:ℚ),(4594171817655762966611/4722366482869645213696:ℚ)⟩ node1686
def node1688 : BoxExpr 3 := .mul ⟨(1422702315084275119743/590295810358705651712:ℚ),(11381618520674200957957/4722366482869645213696:ℚ)⟩ node50 node1687
def node1689 : BoxExpr 3 := .neg ⟨(546427147108415124275/2361183241434822606848:ℚ),(1092854294216830248551/4722366482869645213696:ℚ)⟩ node1672
def node1690 : BoxExpr 3 := .add ⟨(974795132145089118207/4722366482869645213696:ℚ),(974795132145089118209/4722366482869645213696:ℚ)⟩ node332 node1689
def node1691 : BoxExpr 3 := .mul ⟨(696003724351593630399/4722366482869645213696:ℚ),(348001862175796815201/2361183241434822606848:ℚ)⟩ node1690 node335
def node1692 : BoxExpr 3 := .neg ⟨(-348001862175796815201/2361183241434822606848:ℚ),(-696003724351593630399/4722366482869645213696:ℚ)⟩ node1691
def node1693 : BoxExpr 3 := .add ⟨(5342807398161303663771/2361183241434822606848:ℚ),(5342807398161303663779/2361183241434822606848:ℚ)⟩ node1688 node1692
def node1694 : BoxExpr 3 := .mul ⟨(201218086969890832383/4722366482869645213696:ℚ),(201218086969890832385/4722366482869645213696:ℚ)⟩ node1690 node1690
def node1695 : BoxExpr 3 := .mul ⟨(41551534959282456887/1180591620717411303424:ℚ),(166206139837129827551/4722366482869645213696:ℚ)⟩ node1694 node340
def node1696 : BoxExpr 3 := .add ⟨(5425910468079868577545/2361183241434822606848:ℚ),(10851820936159737155109/4722366482869645213696:ℚ)⟩ node1693 node1695
def node1697 : BoxExpr 3 := .neg ⟨(-10851820936159737155109/4722366482869645213696:ℚ),(-5425910468079868577545/2361183241434822606848:ℚ)⟩ node1696
def node1698 : BoxExpr 3 := .add ⟨(323827248283994717/4722366482869645213696:ℚ),(323827248283994815/4722366482869645213696:ℚ)⟩ node1683 node1697
def node1699 : BoxExpr 3 := .mul ⟨(34103562153856454589/147573952589676412928:ℚ),(545656994461703273427/2361183241434822606848:ℚ)⟩ node78 node1674
def node1700 : BoxExpr 3 := .mul ⟨(1268159064837140919/4611686018427387904:ℚ),(162324360299154037633/590295810358705651712:ℚ)⟩ node1699 node349
def node1701 : BoxExpr 3 := .add ⟨(5177826219674603288649/4722366482869645213696:ℚ),(5177826219674603289077/4722366482869645213696:ℚ)⟩ node1700 node385
def node1702 : BoxExpr 3 := .add ⟨(2823960159161849439887/4722366482869645213696:ℚ),(2823960159161849440317/4722366482869645213696:ℚ)⟩ node1701 node387
def node1703 : BoxExpr 3 := .mul ⟨(355219737359597931831/590295810358705651712:ℚ),(2841757898876783454657/4722366482869645213696:ℚ)⟩ node77 node1687
def node1704 : BoxExpr 3 := .neg ⟨(-2841757898876783454657/4722366482869645213696:ℚ),(-355219737359597931831/590295810358705651712:ℚ)⟩ node1703
def node1705 : BoxExpr 3 := .add ⟨(-8898869857467007385/2361183241434822606848:ℚ),(-17797739714934014331/4722366482869645213696:ℚ)⟩ node1702 node1704
def node1706 : BoxExpr 3 := .mul ⟨(-917769201414178590621/2361183241434822606848:ℚ),(-114721150176772323827/295147905179352825856:ℚ)⟩ node98 node1674
def node1707 : BoxExpr 3 := .mul ⟨(-1150304123457668702045/2361183241434822606848:ℚ),(-2300608246915337404081/4722366482869645213696:ℚ)⟩ node68 node1672
def node1708 : BoxExpr 3 := .add ⟨(-1034036662435923646333/1180591620717411303424:ℚ),(-4136146649743694585313/4722366482869645213696:ℚ)⟩ node1706 node1707
def node1709 : BoxExpr 3 := .mul ⟨(-4921753891823381539197/4722366482869645213696:ℚ),(-4921753891823381539171/4722366482869645213696:ℚ)⟩ node1708 node349
def node1710 : BoxExpr 3 := .mul ⟨(2291938676770226164543/2361183241434822606848:ℚ),(4583877353540452329109/4722366482869645213696:ℚ)⟩ node1675 node399
def node1711 : BoxExpr 3 := .add ⟨(-337876538282929210111/4722366482869645213696:ℚ),(-168938269141464605031/2361183241434822606848:ℚ)⟩ node1709 node1710
def node1712 : BoxExpr 3 := .mul ⟨(838024940150346861/1180591620717411303424:ℚ),(3352099760601387445/4722366482869645213696:ℚ)⟩ node1678 node103
def node1713 : BoxExpr 3 := .add ⟨(-108006528705164816089/4722366482869645213696:ℚ),(-54003264352582408043/2361183241434822606848:ℚ)⟩ node403 node1712
def node1714 : BoxExpr 3 := .add ⟨(-55735383373511753275/590295810358705651712:ℚ),(-111470766747023506537/1180591620717411303424:ℚ)⟩ node1711 node1713
def node1715 : BoxExpr 3 := .add ⟨(-61982916181712597963/2361183241434822606848:ℚ),(-61982916181712597879/2361183241434822606848:ℚ)⟩ node1714 node409
def node1716 : BoxExpr 3 := .add ⟨(-1092854294216830248551/2361183241434822606848:ℚ),(-546427147108415124275/1180591620717411303424:ℚ)⟩ node1672 node1672
def node1717 : BoxExpr 3 := .neg ⟨(546427147108415124275/1180591620717411303424:ℚ),(1092854294216830248551/2361183241434822606848:ℚ)⟩ node1716
def node1718 : BoxExpr 3 := .mul ⟨(4594171817655762966609/2361183241434822606848:ℚ),(4594171817655762966611/2361183241434822606848:ℚ)⟩ node86 node1687
def node1719 : BoxExpr 3 := .inv ⟨(1213534565295702948839/2361183241434822606848:ℚ),(151691820661962868605/295147905179352825856:ℚ)⟩ node1718
def node1720 : BoxExpr 3 := .mul ⟨(1123349037542770337113/4722366482869645213696:ℚ),(280837259385692584279/1180591620717411303424:ℚ)⟩ node1717 node1719
def node1721 : BoxExpr 3 := .mul ⟨(2782989125862149259053/4722366482869645213696:ℚ),(347873640732768657383/590295810358705651712:ℚ)⟩ node50 node1720
def node1722 : BoxExpr 3 := .add ⟨(6154758794631075941631/4722366482869645213696:ℚ),(6154758794631075941643/4722366482869645213696:ℚ)⟩ node1721 node335
def node1723 : BoxExpr 3 := .mul ⟨(-974795132145089118209/4722366482869645213696:ℚ),(-974795132145089118207/4722366482869645213696:ℚ)⟩ node422 node1690
def node1724 : BoxExpr 3 := .mul ⟨(-974795132145089118209/4722366482869645213696:ℚ),(-974795132145089118207/4722366482869645213696:ℚ)⟩ node1690 node422
def node1725 : BoxExpr 3 := .add ⟨(-974795132145089118209/2361183241434822606848:ℚ),(-974795132145089118207/2361183241434822606848:ℚ)⟩ node1723 node1724
def node1726 : BoxExpr 3 := .mul ⟨(-805180779151843611641/2361183241434822606848:ℚ),(-1610361558303687223277/4722366482869645213696:ℚ)⟩ node1725 node340
def node1727 : BoxExpr 3 := .add ⟨(4544397236327388718349/4722366482869645213696:ℚ),(2272198618163694359183/2361183241434822606848:ℚ)⟩ node1722 node1726
def node1728 : BoxExpr 3 := .neg ⟨(-2272198618163694359183/2361183241434822606848:ℚ),(-4544397236327388718349/4722366482869645213696:ℚ)⟩ node1727
def node1729 : BoxExpr 3 := .add ⟨(-40971534447754304767/4722366482869645213696:ℚ),(-40971534447754304731/4722366482869645213696:ℚ)⟩ node414 node1728
def node1730 : BoxExpr 3 := .mul ⟨(8658214945508157569347/4722366482869645213696:ℚ),(8702332514504045275139/4722366482869645213696:ℚ)⟩ node112 node1647
def node1731 : BoxExpr 3 := .mul ⟨(10283224250254841734945/4722366482869645213696:ℚ),(10375006190987523727831/4722366482869645213696:ℚ)⟩ node1730 node304
def node1732 : BoxExpr 3 := .add ⟨(5402358792279406474417/1180591620717411303424:ℚ),(1396917368864010691941/147573952589676412928:ℚ)⟩ node1731 node448
def node1733 : BoxExpr 3 := .mul ⟨(22600758890735645135339/4722366482869645213696:ℚ),(2825735795672045865995/590295810358705651712:ℚ)⟩ node111 node1660
def node1734 : BoxExpr 3 := .neg ⟨(-2825735795672045865995/590295810358705651712:ℚ),(-22600758890735645135339/4722366482869645213696:ℚ)⟩ node1733
def node1735 : BoxExpr 3 := .add ⟨(-249112799064685257573/1180591620717411303424:ℚ),(22100596912912697006773/4722366482869645213696:ℚ)⟩ node1732 node1734
def node1736 : BoxExpr 3 := .mul ⟨(-133804304566521151907/1180591620717411303424:ℚ),(-502625387024681166393/4722366482869645213696:ℚ)⟩ node131 node1647
def node1737 : BoxExpr 3 := .mul ⟨(-39772483492931265367/295147905179352825856:ℚ),(-603122597793816852369/4722366482869645213696:ℚ)⟩ node118 node1645
def node1738 : BoxExpr 3 := .add ⟨(-292894238538246213375/1180591620717411303424:ℚ),(-552873992409249009381/2361183241434822606848:ℚ)⟩ node1736 node1737
def node1739 : BoxExpr 3 := .mul ⟨(-43648923048421118375/147573952589676412928:ℚ),(-41039978230642120941/147573952589676412928:ℚ)⟩ node1738 node304
def node1740 : BoxExpr 3 := .mul ⟨(265640530755416060601/1180591620717411303424:ℚ),(1120190358580870959441/4722366482869645213696:ℚ)⟩ node118 node1647
def node1741 : BoxExpr 3 := .mul ⟨(1191652109022223073389/4722366482869645213696:ℚ),(1278611590179625850039/4722366482869645213696:ℚ)⟩ node1740 node461
def node1742 : BoxExpr 3 := .add ⟨(-205113428527252714611/4722366482869645213696:ℚ),(-34667713200922020073/4722366482869645213696:ℚ)⟩ node1739 node1741
def node1743 : BoxExpr 3 := .add ⟨(-1481207076710861778285/2361183241434822606848:ℚ),(1378906167370737752831/4722366482869645213696:ℚ)⟩ node1742 node476
def node1744 : BoxExpr 3 := .add ⟨(-1095044845075583257805/2361183241434822606848:ℚ),(-473/1024:ℚ)⟩ node1645 node1645
def node1745 : BoxExpr 3 := .neg ⟨(473/1024:ℚ),(1095044845075583257805/2361183241434822606848:ℚ)⟩ node1744
def node1746 : BoxExpr 3 := .mul ⟨(4593650181043830312061/2361183241434822606848:ℚ),(2297346175343126720321/1180591620717411303424:ℚ)⟩ node86 node1660
def node1747 : BoxExpr 3 := .inv ⟨(2426794167753128394639/4722366482869645213696:ℚ),(2427344738891627040371/4722366482869645213696:ℚ)⟩ node1746
def node1748 : BoxExpr 3 := .mul ⟨(1120970352878154033851/4722366482869645213696:ℚ),(1125728531737923517063/4722366482869645213696:ℚ)⟩ node1745 node1747
def node1749 : BoxExpr 3 := .mul ⟨(338419361025054354397/2361183241434822606848:ℚ),(178235800804266308593/1180591620717411303424:ℚ)⟩ node117 node1748
def node1750 : BoxExpr 3 := .neg ⟨(-178235800804266308593/1180591620717411303424:ℚ),(-338419361025054354397/2361183241434822606848:ℚ)⟩ node1749
def node1751 : BoxExpr 3 := .add ⟨(519987388889298741575/4722366482869645213696:ℚ),(159214106169787998233/1180591620717411303424:ℚ)⟩ node479 node1750
def node1752 : BoxExpr 3 := .add ⟨(-2962414153421723556569/4722366482869645213696:ℚ),(1378906167370737752831/4722366482869645213696:ℚ)⟩ node1742 node492
def node1753 : BoxExpr 3 := .mul ⟨(-990232519716810870821/2361183241434822606848:ℚ),(-241208345653556739797/590295810358705651712:ℚ)⟩ node175 node1647
def node1754 : BoxExpr 3 := .mul ⟨(16055368737659372231/73786976294838206464:ℚ),(1057164531179272338413/4722366482869645213696:ℚ)⟩ node148 node1645
def node1755 : BoxExpr 3 := .add ⟨(-476460720111710959429/2361183241434822606848:ℚ),(-872502234049181579963/4722366482869645213696:ℚ)⟩ node1753 node1754
def node1756 : BoxExpr 3 := .add ⟨(37311079493388951963/2361183241434822606848:ℚ),(92331148565045379225/2361183241434822606848:ℚ)⟩ node1755 node1754
def node1757 : BoxExpr 3 := .mul ⟨(88627551952531255863/4722366482869645213696:ℚ),(220156202118628968855/4722366482869645213696:ℚ)⟩ node1756 node304
def node1758 : BoxExpr 3 := .mul ⟨(-1860937215976151828743/4722366482869645213696:ℚ),(-1810293483062897950045/4722366482869645213696:ℚ)⟩ node148 node1647
def node1759 : BoxExpr 3 := .mul ⟨(-2313248894542778635407/4722366482869645213696:ℚ),(-1144021546225322771247/2361183241434822606848:ℚ)⟩ node36 node1645
def node1760 : BoxExpr 3 := .add ⟨(-2087093055259465232075/2361183241434822606848:ℚ),(-4098336575513543492539/4722366482869645213696:ℚ)⟩ node1758 node1759
def node1761 : BoxExpr 3 := .mul ⟨(-74445532566081243929/73786976294838206464:ℚ),(-4596240838893572549977/4722366482869645213696:ℚ)⟩ node1760 node461
def node1762 : BoxExpr 3 := .add ⟨(-4675886532276668355593/4722366482869645213696:ℚ),(-2188042318387471790561/2361183241434822606848:ℚ)⟩ node1757 node1761
def node1763 : BoxExpr 3 := .mul ⟨(19877330400992683964907/4722366482869645213696:ℚ),(2563680921968548901267/590295810358705651712:ℚ)⟩ node1648 node514
def node1764 : BoxExpr 3 := .add ⟨(15112816316763484353451/4722366482869645213696:ℚ),(15913206536854818660159/4722366482869645213696:ℚ)⟩ node1761 node1763
def node1765 : BoxExpr 3 := .add ⟨(5218464892243407998929/2361183241434822606848:ℚ),(11537121900079875079037/4722366482869645213696:ℚ)⟩ node1762 node1764
def node1766 : BoxExpr 3 := .mul ⟨(6233394947587851793/2361183241434822606848:ℚ),(3471515838469957613/1180591620717411303424:ℚ)⟩ node1651 node189
def node1767 : BoxExpr 3 := .add ⟨(-20445777891962448459/2361183241434822606848:ℚ),(-19320104358875477741/2361183241434822606848:ℚ)⟩ node518 node1766
def node1768 : BoxExpr 3 := .add ⟨(-47124950731512748711/2361183241434822606848:ℚ),(-11395810098672717677/590295810358705651712:ℚ)⟩ node518 node1767
def node1769 : BoxExpr 3 := .add ⟨(2585669970755947625109/1180591620717411303424:ℚ),(11445955419290493337621/4722366482869645213696:ℚ)⟩ node1765 node1768
def node1770 : BoxExpr 3 := .add ⟨(21446413161390361871959/4722366482869645213696:ℚ),(7009856614654484953041/1180591620717411303424:ℚ)⟩ node1769 node527
def node1771 : BoxExpr 3 := .mul ⟨(-2427344738891627040371/2361183241434822606848:ℚ),(-2426794167753128394639/2361183241434822606848:ℚ)⟩ node6 node1747
def node1772 : BoxExpr 3 := .mul ⟨(1120970352878154033851/2361183241434822606848:ℚ),(1125728531737923517063/2361183241434822606848:ℚ)⟩ node86 node1748
def node1773 : BoxExpr 3 := .mul ⟨(17873769062481716618191/4722366482869645213696:ℚ),(2235235011305825894401/590295810358705651712:ℚ)⟩ node1746 node1746
def node1774 : BoxExpr 3 := .inv ⟨(1247114122549384182289/4722366482869645213696:ℚ),(155960007095967220207/590295810358705651712:ℚ)⟩ node1773
def node1775 : BoxExpr 3 := .mul ⟨(592066694994837394683/4722366482869645213696:ℚ),(74356206971590796597/590295810358705651712:ℚ)⟩ node1772 node1774
def node1776 : BoxExpr 3 := .neg ⟨(-74356206971590796597/590295810358705651712:ℚ),(-592066694994837394683/4722366482869645213696:ℚ)⟩ node1775
def node1777 : BoxExpr 3 := .mul ⟨(-275873146021941166437/4722366482869645213696:ℚ),(-4273186443062714961/73786976294838206464:ℚ)⟩ node1745 node1776
def node1778 : BoxExpr 3 := .add ⟨(-5130562623805195247179/4722366482869645213696:ℚ),(-2563536133931135273391/2361183241434822606848:ℚ)⟩ node1771 node1777
def node1779 : BoxExpr 3 := .mul ⟨(-3180027337113037391151/1180591620717411303424:ℚ),(-3173106862387430069501/1180591620717411303424:ℚ)⟩ node11 node1778
def node1780 : BoxExpr 3 := .add ⟨(-4918759918751495671579/4722366482869645213696:ℚ),(-2445539009924533192489/2361183241434822606848:ℚ)⟩ node1779 node546
def node1781 : BoxExpr 3 := .neg ⟨(2445539009924533192489/2361183241434822606848:ℚ),(4918759918751495671579/4722366482869645213696:ℚ)⟩ node1780
def cert_iv9 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-9479/40960:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/40960:ℚ)],
    whole := node1671, centerValue := node1698, gradient := ![node1705, node1715, node1729],
    hessian := ![![node1735, node1743, node1751], ![node1752, node1770, node536], ![node1751, node536, node1781]] }
def node1782 : BoxExpr 3 := .var 2
def node1783 : BoxExpr 3 := .mul ⟨(-218963793970204451537/2361183241434822606848:ℚ),(-215911670106493312355/2361183241434822606848:ℚ)⟩ node13 node1782
def node1784 : BoxExpr 3 := .add ⟨(961627826747206851887/2361183241434822606848:ℚ),(964679950610917991069/2361183241434822606848:ℚ)⟩ node1783 node301
def node1785 : BoxExpr 3 := .mul ⟨(4034691571799883608483/4722366482869645213696:ℚ),(1018928512094068833105/1180591620717411303424:ℚ)⟩ node36 node1784
def node1786 : BoxExpr 3 := .mul ⟨(2395969519961849767583/2361183241434822606848:ℚ),(4859106269970951238333/4722366482869645213696:ℚ)⟩ node1785 node304
def node1787 : BoxExpr 3 := .add ⟨(-152036911734009517573/4722366482869645213696:ℚ),(-138211077050764208635/4722366482869645213696:ℚ)⟩ node1782 node306
def node1788 : BoxExpr 3 := .mul ⟨(746938874930667009/590295810358705651712:ℚ),(6573266468754793695/4722366482869645213696:ℚ)⟩ node1787 node308
def node1789 : BoxExpr 3 := .mul ⟨(6512166890664982487/4722366482869645213696:ℚ),(7177241897028599679/4722366482869645213696:ℚ)⟩ node1788 node37
def node1790 : BoxExpr 3 := .add ⟨(4798451206814364517653/4722366482869645213696:ℚ),(1216570877966994959503/1180591620717411303424:ℚ)⟩ node1786 node1789
def node1791 : BoxExpr 3 := .add ⟨(3878223865488437719365/1180591620717411303424:ℚ),(7854023754363885167627/2361183241434822606848:ℚ)⟩ node1790 node316
def node1792 : BoxExpr 3 := .add ⟨(1343868653623991190637/590295810358705651712:ℚ),(10960224472129025505989/4722366482869645213696:ℚ)⟩ node1791 node323
def node1793 : BoxExpr 3 := .add ⟨(167983360342070014315/73786976294838206464:ℚ),(5480105152514788448527/2361183241434822606848:ℚ)⟩ node1792 node325
def node1794 : BoxExpr 3 := .mul ⟨(124938416132049097195/2361183241434822606848:ℚ),(223729/4194304:ℚ)⟩ node1782 node1782
def node1795 : BoxExpr 3 := .neg ⟨(-223729/4194304:ℚ),(-124938416132049097195/2361183241434822606848:ℚ)⟩ node1794
def node1796 : BoxExpr 3 := .add ⟨(3970575/4194304:ℚ),(2236244825302773509653/2361183241434822606848:ℚ)⟩ node12 node1795
def node1797 : BoxExpr 3 := .sqrt ⟨(4594692350686253440641/4722366482869645213696:ℚ),(4595730107502071913331/4722366482869645213696:ℚ)⟩ node1796
def node1798 : BoxExpr 3 := .mul ⟨(11374483578013208164353/4722366482869645213696:ℚ),(712131809289310677297/295147905179352825856:ℚ)⟩ node11 node1797
def node1799 : BoxExpr 3 := .neg ⟨(1086282641640571220787/4722366482869645213696:ℚ),(473/2048:ℚ)⟩ node1782
def node1800 : BoxExpr 3 := .add ⟨(242055869892207522611/1180591620717411303424:ℚ),(486302290643168054477/2361183241434822606848:ℚ)⟩ node332 node1799
def node1801 : BoxExpr 3 := .mul ⟨(21603486387879521393/147573952589676412928:ℚ),(347219835519221990897/2361183241434822606848:ℚ)⟩ node1800 node335
def node1802 : BoxExpr 3 := .neg ⟨(-347219835519221990897/2361183241434822606848:ℚ),(-21603486387879521393/147573952589676412928:ℚ)⟩ node1801
def node1803 : BoxExpr 3 := .add ⟨(10680043906974764182559/4722366482869645213696:ℚ),(668924836513551634511/295147905179352825856:ℚ)⟩ node1798 node1802
def node1804 : BoxExpr 3 := .mul ⟨(198514179233863161609/4722366482869645213696:ℚ),(100157376070941545595/2361183241434822606848:ℚ)⟩ node1800 node1800
def node1805 : BoxExpr 3 := .mul ⟨(5124147251474092859/147573952589676412928:ℚ),(165459985269195433323/4722366482869645213696:ℚ)⟩ node1804 node340
def node1806 : BoxExpr 3 := .add ⟨(10844016619021935154047/4722366482869645213696:ℚ),(10868257369486021585499/4722366482869645213696:ℚ)⟩ node1803 node1805
def node1807 : BoxExpr 3 := .neg ⟨(-10868257369486021585499/4722366482869645213696:ℚ),(-10844016619021935154047/4722366482869645213696:ℚ)⟩ node1806
def node1808 : BoxExpr 3 := .add ⟨(-117322307593540669339/4722366482869645213696:ℚ),(116193686007641743007/4722366482869645213696:ℚ)⟩ node1793 node1807
def node1809 : BoxExpr 3 := .var 2
def node1810 : BoxExpr 3 := .mul ⟨(-434871082974980257875/4722366482869645213696:ℚ),(-434871082974980257873/4722366482869645213696:ℚ)⟩ node51 node1809
def node1811 : BoxExpr 3 := .add ⟨(1926312158459842348973/4722366482869645213696:ℚ),(1926312158459842348975/4722366482869645213696:ℚ)⟩ node1810 node301
def node1812 : BoxExpr 3 := .mul ⟨(4055151415277980368351/4722366482869645213696:ℚ),(4055151415277980368365/4722366482869645213696:ℚ)⟩ node68 node1811
def node1813 : BoxExpr 3 := .mul ⟨(4825374666373172042467/4722366482869645213696:ℚ),(2412687333186586021243/2361183241434822606848:ℚ)⟩ node1812 node349
def node1814 : BoxExpr 3 := .add ⟨(-145123994392386863105/4722366482869645213696:ℚ),(-145123994392386863103/4722366482869645213696:ℚ)⟩ node1809 node351
def node1815 : BoxExpr 3 := .mul ⟨(6274388734100064883/4722366482869645213696:ℚ),(1568597183525016221/1180591620717411303424:ℚ)⟩ node1814 node308
def node1816 : BoxExpr 3 := .mul ⟨(3422184413605547087/2361183241434822606848:ℚ),(213886525850346693/147573952589676412928:ℚ)⟩ node1815 node69
def node1817 : BoxExpr 3 := .add ⟨(4832219035200383136641/4722366482869645213696:ℚ),(2416109517600191568331/2361183241434822606848:ℚ)⟩ node1813 node1816
def node1818 : BoxExpr 3 := .add ⟨(15611221548116645088537/4722366482869645213696:ℚ),(15611221548116645088611/4722366482869645213696:ℚ)⟩ node1817 node358
def node1819 : BoxExpr 3 := .add ⟨(1357042114167045249715/590295810358705651712:ℚ),(10856336913336361997799/4722366482869645213696:ℚ)⟩ node1818 node361
def node1820 : BoxExpr 3 := .add ⟨(678520171639807086799/295147905179352825856:ℚ),(169630042909951771701/73786976294838206464:ℚ)⟩ node1819 node325
def node1821 : BoxExpr 3 := .mul ⟨(250885630136379884175/4722366482869645213696:ℚ),(15680351883523742761/295147905179352825856:ℚ)⟩ node1809 node1809
def node1822 : BoxExpr 3 := .neg ⟨(-15680351883523742761/295147905179352825856:ℚ),(-250885630136379884175/4722366482869645213696:ℚ)⟩ node1821
def node1823 : BoxExpr 3 := .add ⟨(279467553295829083095/295147905179352825856:ℚ),(4471480852733265329521/4722366482869645213696:ℚ)⟩ node12 node1822
def node1824 : BoxExpr 3 := .sqrt ⟨(4595211780510333802285/4722366482869645213696:ℚ),(4595211780510333802287/4722366482869645213696:ℚ)⟩ node1823
def node1825 : BoxExpr 3 := .mul ⟨(11384194928557099065291/4722366482869645213696:ℚ),(11384194928557099065305/4722366482869645213696:ℚ)⟩ node50 node1824
def node1826 : BoxExpr 3 := .neg ⟨(1088473192499324230041/4722366482869645213696:ℚ),(544236596249662115021/2361183241434822606848:ℚ)⟩ node1809
def node1827 : BoxExpr 3 := .add ⟨(485207015213791549849/2361183241434822606848:ℚ),(242603507606895774925/1180591620717411303424:ℚ)⟩ node332 node1826
def node1828 : BoxExpr 3 := .mul ⟨(2706545381739430989/18446744073709551616:ℚ),(346437808862647166593/2361183241434822606848:ℚ)⟩ node1827 node335
def node1829 : BoxExpr 3 := .neg ⟨(-346437808862647166593/2361183241434822606848:ℚ),(-2706545381739430989/18446744073709551616:ℚ)⟩ node1828
def node1830 : BoxExpr 3 := .add ⟨(10691319310831804732105/4722366482869645213696:ℚ),(10691319310831804732121/4722366482869645213696:ℚ)⟩ node1825 node1829
def node1831 : BoxExpr 3 := .mul ⟨(199413449563207200931/4722366482869645213696:ℚ),(199413449563207200933/4722366482869645213696:ℚ)⟩ node1827 node1827
def node1832 : BoxExpr 3 := .mul ⟨(2573679833425142937/73786976294838206464:ℚ),(164715509339209147971/4722366482869645213696:ℚ)⟩ node1831 node340
def node1833 : BoxExpr 3 := .add ⟨(10856034820171013880073/4722366482869645213696:ℚ),(2714008705042753470023/1180591620717411303424:ℚ)⟩ node1830 node1832
def node1834 : BoxExpr 3 := .neg ⟨(-2714008705042753470023/1180591620717411303424:ℚ),(-10856034820171013880073/4722366482869645213696:ℚ)⟩ node1833
def node1835 : BoxExpr 3 := .add ⟨(71981516474877173/1180591620717411303424:ℚ),(287926065899508791/4722366482869645213696:ℚ)⟩ node1820 node1834
def node1836 : BoxExpr 3 := .mul ⟨(273076629928791377963/1180591620717411303424:ℚ),(1092306519715165511857/4722366482869645213696:ℚ)⟩ node78 node1811
def node1837 : BoxExpr 3 := .mul ⟨(1299775931495395285909/4722366482869645213696:ℚ),(324943982873848821479/1180591620717411303424:ℚ)⟩ node1836 node349
def node1838 : BoxExpr 3 := .add ⟨(2589503634388383136751/2361183241434822606848:ℚ),(5179007268776766273929/4722366482869645213696:ℚ)⟩ node1837 node385
def node1839 : BoxExpr 3 := .add ⟨(706285302066003106185/1180591620717411303424:ℚ),(2825141208264012425169/4722366482869645213696:ℚ)⟩ node1838 node387
def node1840 : BoxExpr 3 := .mul ⟨(710600293838169471861/1180591620717411303424:ℚ),(2842401175352677887453/4722366482869645213696:ℚ)⟩ node77 node1824
def node1841 : BoxExpr 3 := .neg ⟨(-2842401175352677887453/4722366482869645213696:ℚ),(-710600293838169471861/1180591620717411303424:ℚ)⟩ node1840
def node1842 : BoxExpr 3 := .add ⟨(-17259967088665462713/4722366482869645213696:ℚ),(-17259967088665462275/4722366482869645213696:ℚ)⟩ node1839 node1841
def node1843 : BoxExpr 3 := .mul ⟨(-918603896287860393909/2361183241434822606848:ℚ),(-1837207792575720787807/4722366482869645213696:ℚ)⟩ node98 node1811
def node1844 : BoxExpr 3 := .mul ⟨(-572846356660188322397/1180591620717411303424:ℚ),(-572846356660188322395/1180591620717411303424:ℚ)⟩ node68 node1809
def node1845 : BoxExpr 3 := .add ⟨(-2064296609608237038703/2361183241434822606848:ℚ),(-4128593219216474077387/4722366482869645213696:ℚ)⟩ node1843 node1844
def node1846 : BoxExpr 3 := .mul ⟨(-4912765785442707446829/4722366482869645213696:ℚ),(-1228191446360676861701/1180591620717411303424:ℚ)⟩ node1845 node349
def node1847 : BoxExpr 3 := .mul ⟨(2294023154503130406177/2361183241434822606848:ℚ),(4588046309006260812379/4722366482869645213696:ℚ)⟩ node1812 node399
def node1848 : BoxExpr 3 := .add ⟨(-324719476436446634475/4722366482869645213696:ℚ),(-324719476436446634425/4722366482869645213696:ℚ)⟩ node1846 node1847
def node1849 : BoxExpr 3 := .mul ⟨(813467432746673693/1180591620717411303424:ℚ),(3253869730986694773/4722366482869645213696:ℚ)⟩ node1815 node103
def node1850 : BoxExpr 3 := .add ⟨(-108104758734779508761/4722366482869645213696:ℚ),(-54052379367389754379/2361183241434822606848:ℚ)⟩ node403 node1849
def node1851 : BoxExpr 3 := .add ⟨(-108206058792806535809/1180591620717411303424:ℚ),(-432824235171226143183/4722366482869645213696:ℚ)⟩ node1848 node1850
def node1852 : BoxExpr 3 := .add ⟨(-55453500273278656481/2361183241434822606848:ℚ),(-110907000546557312793/4722366482869645213696:ℚ)⟩ node1851 node409
def node1853 : BoxExpr 3 := .add ⟨(-544236596249662115021/1180591620717411303424:ℚ),(-1088473192499324230041/2361183241434822606848:ℚ)⟩ node1809 node1809
def node1854 : BoxExpr 3 := .neg ⟨(1088473192499324230041/2361183241434822606848:ℚ),(544236596249662115021/1180591620717411303424:ℚ)⟩ node1853
def node1855 : BoxExpr 3 := .mul ⟨(4595211780510333802285/2361183241434822606848:ℚ),(4595211780510333802287/2361183241434822606848:ℚ)⟩ node86 node1824
def node1856 : BoxExpr 3 := .inv ⟨(1213259924880652232911/2361183241434822606848:ℚ),(75828745305040764557/147573952589676412928:ℚ)⟩ node1855
def node1857 : BoxExpr 3 := .mul ⟨(69912029728993150213/295147905179352825856:ℚ),(1118592475663890403411/4722366482869645213696:ℚ)⟩ node1854 node1856
def node1858 : BoxExpr 3 := .mul ⟨(2771205201593723216477/4722366482869645213696:ℚ),(346400650199215402061/590295810358705651712:ℚ)⟩ node50 node1857
def node1859 : BoxExpr 3 := .add ⟨(6142974870362649899055/4722366482869645213696:ℚ),(6142974870362649899067/4722366482869645213696:ℚ)⟩ node1858 node335
def node1860 : BoxExpr 3 := .mul ⟨(-242603507606895774925/1180591620717411303424:ℚ),(-485207015213791549849/2361183241434822606848:ℚ)⟩ node422 node1827
def node1861 : BoxExpr 3 := .mul ⟨(-242603507606895774925/1180591620717411303424:ℚ),(-485207015213791549849/2361183241434822606848:ℚ)⟩ node1827 node422
def node1862 : BoxExpr 3 := .add ⟨(-242603507606895774925/590295810358705651712:ℚ),(-485207015213791549849/1180591620717411303424:ℚ)⟩ node1860 node1861
def node1863 : BoxExpr 3 := .mul ⟨(-1603123978266367280705/4722366482869645213696:ℚ),(-400780994566591820175/1180591620717411303424:ℚ)⟩ node1862 node340
def node1864 : BoxExpr 3 := .add ⟨(2269925446048141309175/2361183241434822606848:ℚ),(4539850892096282618367/4722366482869645213696:ℚ)⟩ node1859 node1863
def node1865 : BoxExpr 3 := .neg ⟨(-4539850892096282618367/4722366482869645213696:ℚ),(-2269925446048141309175/2361183241434822606848:ℚ)⟩ node1864
def node1866 : BoxExpr 3 := .add ⟨(-1138287194270256399/147573952589676412928:ℚ),(-9106297554162051183/1180591620717411303424:ℚ)⟩ node414 node1865
def node1867 : BoxExpr 3 := .mul ⟨(4333070741540948444501/2361183241434822606848:ℚ),(8710195025035042530737/4722366482869645213696:ℚ)⟩ node112 node1784
def node1868 : BoxExpr 3 := .mul ⟨(2573159618230549114857/1180591620717411303424:ℚ),(5192189976585690014115/2361183241434822606848:ℚ)⟩ node1867 node304
def node1869 : BoxExpr 3 := .add ⟨(21618849391784980622151/4722366482869645213696:ℚ),(44710729565832198442511/4722366482869645213696:ℚ)⟩ node1868 node448
def node1870 : BoxExpr 3 := .mul ⟨(22605886365376366927953/4722366482869645213696:ℚ),(11305496064455096906795/2361183241434822606848:ℚ)⟩ node111 node1797
def node1871 : BoxExpr 3 := .neg ⟨(-11305496064455096906795/2361183241434822606848:ℚ),(-22605886365376366927953/4722366482869645213696:ℚ)⟩ node1870
def node1872 : BoxExpr 3 := .add ⟨(-992142737125213191439/4722366482869645213696:ℚ),(11052421600227915757279/2361183241434822606848:ℚ)⟩ node1869 node1871
def node1873 : BoxExpr 3 := .mul ⟨(-535700784138564714039/4722366482869645213696:ℚ),(-251542768593684765163/2361183241434822606848:ℚ)⟩ node131 node1784
def node1874 : BoxExpr 3 := .mul ⟨(-158453440237157199567/1180591620717411303424:ℚ),(-600699906597604903067/4722366482869645213696:ℚ)⟩ node118 node1782
def node1875 : BoxExpr 3 := .add ⟨(-1169514545087193512307/4722366482869645213696:ℚ),(-1103785443784974433393/4722366482869645213696:ℚ)⟩ node1873 node1874
def node1876 : BoxExpr 3 := .mul ⟨(-1394306713229643023537/4722366482869645213696:ℚ),(-1310948424593746686155/4722366482869645213696:ℚ)⟩ node1875 node304
def node1877 : BoxExpr 3 := .mul ⟨(1063534891501722936917/4722366482869645213696:ℚ),(1121202444533273300929/4722366482869645213696:ℚ)⟩ node118 node1784
def node1878 : BoxExpr 3 := .mul ⟨(596371529258298930589/2361183241434822606848:ℚ),(1279766808861064086437/4722366482869645213696:ℚ)⟩ node1877 node461
def node1879 : BoxExpr 3 := .add ⟨(-201563654713045162359/4722366482869645213696:ℚ),(-15590807866341299859/2361183241434822606848:ℚ)⟩ node1876 node1878
def node1880 : BoxExpr 3 := .add ⟨(-1479432189803758002159/2361183241434822606848:ℚ),(691196132419488586593/2361183241434822606848:ℚ)⟩ node1879 node476
def node1881 : BoxExpr 3 := .add ⟨(-473/1024:ℚ),(-1086282641640571220787/2361183241434822606848:ℚ)⟩ node1782 node1782
def node1882 : BoxExpr 3 := .neg ⟨(1086282641640571220787/2361183241434822606848:ℚ),(473/1024:ℚ)⟩ node1881
def node1883 : BoxExpr 3 := .mul ⟨(4594692350686253440641/2361183241434822606848:ℚ),(4595730107502071913331/2361183241434822606848:ℚ)⟩ node86 node1797
def node1884 : BoxExpr 3 := .inv ⟨(2426246176002250062281/4722366482869645213696:ℚ),(151674635484570524665/295147905179352825856:ℚ)⟩ node1883
def node1885 : BoxExpr 3 := .mul ⟨(139526925477863770061/590295810358705651712:ℚ),(1120970352878154033853/4722366482869645213696:ℚ)⟩ node1882 node1884
def node1886 : BoxExpr 3 := .mul ⟨(673967697286874441715/4722366482869645213696:ℚ),(354964883433535907939/2361183241434822606848:ℚ)⟩ node117 node1885
def node1887 : BoxExpr 3 := .neg ⟨(-354964883433535907939/2361183241434822606848:ℚ),(-673967697286874441715/4722366482869645213696:ℚ)⟩ node1886
def node1888 : BoxExpr 3 := .add ⟨(523000825239292160069/4722366482869645213696:ℚ),(639727449442386260011/4722366482869645213696:ℚ)⟩ node479 node1887
def node1889 : BoxExpr 3 := .add ⟨(-2958864379607516004317/4722366482869645213696:ℚ),(691196132419488586593/2361183241434822606848:ℚ)⟩ node1879 node492
def node1890 : BoxExpr 3 := .mul ⟨(-991127189462127203255/2361183241434822606848:ℚ),(-482858340544734758147/1180591620717411303424:ℚ)⟩ node175 node1784
def node1891 : BoxExpr 3 := .mul ⟨(511708022820216846209/2361183241434822606848:ℚ),(1052934982623280303367/4722366482869645213696:ℚ)⟩ node148 node1782
def node1892 : BoxExpr 3 := .add ⟨(-239709583320955178523/1180591620717411303424:ℚ),(-878498379555658729221/4722366482869645213696:ℚ)⟩ node1890 node1891
def node1893 : BoxExpr 3 := .add ⟨(32288856178306489163/2361183241434822606848:ℚ),(87218301533810787073/2361183241434822606848:ℚ)⟩ node1892 node1891
def node1894 : BoxExpr 3 := .mul ⟨(76697922367475908515/4722366482869645213696:ℚ),(103982514673225419943/2361183241434822606848:ℚ)⟩ node1893 node304
def node1895 : BoxExpr 3 := .mul ⟨(-232827320340301524949/590295810358705651712:ℚ),(-452987698644025714817/1180591620717411303424:ℚ)⟩ node148 node1784
def node1896 : BoxExpr 3 := .mul ⟨(-143999621909709188059/295147905179352825856:ℚ),(-1139426110838793990559/2361183241434822606848:ℚ)⟩ node36 node1782
def node1897 : BoxExpr 3 := .add ⟨(-520826564159719901067/590295810358705651712:ℚ),(-2045401508126845420193/2361183241434822606848:ℚ)⟩ node1895 node1896
def node1898 : BoxExpr 3 := .mul ⟨(-148620918825729637311/147573952589676412928:ℚ),(-4587792032385283082355/4722366482869645213696:ℚ)⟩ node1897 node461
def node1899 : BoxExpr 3 := .add ⟨(-4679171480055872485437/4722366482869645213696:ℚ),(-4379827003038832242469/4722366482869645213696:ℚ)⟩ node1894 node1898
def node1900 : BoxExpr 3 := .mul ⟨(19895527963340202254419/4722366482869645213696:ℚ),(20527977550929354848787/4722366482869645213696:ℚ)⟩ node1785 node514
def node1901 : BoxExpr 3 := .add ⟨(15139658560916853860467/4722366482869645213696:ℚ),(498130797454502242701/147573952589676412928:ℚ)⟩ node1898 node1900
def node1902 : BoxExpr 3 := .add ⟨(5230243540430490687515/2361183241434822606848:ℚ),(11560358515505239523963/4722366482869645213696:ℚ)⟩ node1899 node1901
def node1903 : BoxExpr 3 := .mul ⟨(12083751532950364817/4722366482869645213696:ℚ),(13497129530551754773/4722366482869645213696:ℚ)⟩ node1788 node189
def node1904 : BoxExpr 3 := .add ⟨(-41274594146150235687/4722366482869645213696:ℚ),(-39029142541079031161/4722366482869645213696:ℚ)⟩ node518 node1903
def node1905 : BoxExpr 3 := .add ⟨(-94632939825250836191/4722366482869645213696:ℚ),(-91555414612709817095/4722366482869645213696:ℚ)⟩ node518 node1904
def node1906 : BoxExpr 3 := .add ⟨(10365854141035730538839/4722366482869645213696:ℚ),(2867200775223132426717/1180591620717411303424:ℚ)⟩ node1902 node1905
def node1907 : BoxExpr 3 := .add ⟨(10734793709701150955181/2361183241434822606848:ℚ),(28062274140219976181411/4722366482869645213696:ℚ)⟩ node1906 node527
def node1908 : BoxExpr 3 := .mul ⟨(-151674635484570524665/147573952589676412928:ℚ),(-2426246176002250062281/2361183241434822606848:ℚ)⟩ node6 node1884
def node1909 : BoxExpr 3 := .mul ⟨(139526925477863770061/295147905179352825856:ℚ),(1120970352878154033853/2361183241434822606848:ℚ)⟩ node86 node1885
def node1910 : BoxExpr 3 := .mul ⟨(17881880090446607155199/4722366482869645213696:ℚ),(17889958602422188077225/4722366482869645213696:ℚ)⟩ node1883 node1883
def node1911 : BoxExpr 3 := .inv ⟨(623275483586396959331/2361183241434822606848:ℚ),(1247114122549384182291/4722366482869645213696:ℚ)⟩ node1910
def node1912 : BoxExpr 3 := .mul ⟨(36830564618819412423/295147905179352825856:ℚ),(296033347497418697343/2361183241434822606848:ℚ)⟩ node1909 node1911
def node1913 : BoxExpr 3 := .neg ⟨(-296033347497418697343/2361183241434822606848:ℚ),(-36830564618819412423/295147905179352825856:ℚ)⟩ node1912
def node1914 : BoxExpr 3 := .mul ⟨(-273483932356013757507/4722366482869645213696:ℚ),(-33888435531105127329/590295810358705651712:ℚ)⟩ node1882 node1913
def node1915 : BoxExpr 3 := .add ⟨(-5127072267862270546787/4722366482869645213696:ℚ),(-2561799918126670571597/2361183241434822606848:ℚ)⟩ node1908 node1914
def node1916 : BoxExpr 3 := .mul ⟨(-6355727886647942322457/2361183241434822606848:ℚ),(-12683831201249082199647/4722366482869645213696:ℚ)⟩ node11 node1915
def node1917 : BoxExpr 3 := .add ⟨(-4910106343595230751889/4722366482869645213696:ℚ),(-4882481771548428306621/4722366482869645213696:ℚ)⟩ node1916 node546
def node1918 : BoxExpr 3 := .neg ⟨(4882481771548428306621/4722366482869645213696:ℚ),(4910106343595230751889/4722366482869645213696:ℚ)⟩ node1917
def cert_iv10 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-9441/40960:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/40960:ℚ)],
    whole := node1808, centerValue := node1835, gradient := ![node1842, node1852, node1866],
    hessian := ![![node1872, node1880, node1888], ![node1889, node1907, node536], ![node1888, node536, node1918]] }
def node1919 : BoxExpr 3 := .var 2
def node1920 : BoxExpr 3 := .mul ⟨(-436168470779548909595/4722366482869645213696:ℚ),(-430081747458996655305/4722366482869645213696:ℚ)⟩ node13 node1919
def node1921 : BoxExpr 3 := .add ⟨(1925014770655273697253/4722366482869645213696:ℚ),(1931101493975825951543/4722366482869645213696:ℚ)⟩ node1920 node301
def node1922 : BoxExpr 3 := .mul ⟨(504797740789253729071/590295810358705651712:ℚ),(4079393110043044728229/4722366482869645213696:ℚ)⟩ node36 node1921
def node1923 : BoxExpr 3 := .mul ⟨(4796322015314209274213/4722366482869645213696:ℚ),(4863492483380533039721/4722366482869645213696:ℚ)⟩ node1922 node304
def node1924 : BoxExpr 3 := .add ⟨(-147655810016503499065/4722366482869645213696:ℚ),(-66914987666629095063/2361183241434822606848:ℚ)⟩ node1919 node306
def node1925 : BoxExpr 3 := .mul ⟨(5786095490491371849/4722366482869645213696:ℚ),(199495342493775921/147573952589676412928:ℚ)⟩ node1924 node308
def node1926 : BoxExpr 3 := .mul ⟨(1576435031368088869/1180591620717411303424:ℚ),(3485211104012064023/2361183241434822606848:ℚ)⟩ node1925 node37
def node1927 : BoxExpr 3 := .add ⟨(4802627755439681629689/4722366482869645213696:ℚ),(4870462905588557167767/4722366482869645213696:ℚ)⟩ node1923 node1926
def node1928 : BoxExpr 3 := .add ⟨(1939634001322383498687/590295810358705651712:ℚ),(15712226902448347665009/4722366482869645213696:ℚ)⟩ node1927 node316
def node1929 : BoxExpr 3 := .add ⟨(2688781444404311659283/1180591620717411303424:ℚ),(342637620807800088617/147573952589676412928:ℚ)⟩ node1928 node323
def node1930 : BoxExpr 3 := .add ⟨(2688777902629449507049/1180591620717411303424:ℚ),(10964389698750154226809/4722366482869645213696:ℚ)⟩ node1929 node325
def node1931 : BoxExpr 3 := .mul ⟨(247865333267530367631/4722366482869645213696:ℚ),(31234604033012274299/590295810358705651712:ℚ)⟩ node1919 node1919
def node1932 : BoxExpr 3 := .neg ⟨(-31234604033012274299/590295810358705651712:ℚ),(-247865333267530367631/4722366482869645213696:ℚ)⟩ node1931
def node1933 : BoxExpr 3 := .add ⟨(559061206325693377413/590295810358705651712:ℚ),(4474501149602114846065/4722366482869645213696:ℚ)⟩ node12 node1932
def node1934 : BoxExpr 3 := .sqrt ⟨(4595730107502071913329/4722366482869645213696:ℚ),(1149190863619995112369/1180591620717411303424:ℚ)⟩ node1933
def node1935 : BoxExpr 3 := .mul ⟨(11377052617887604865283/4722366482869645213696:ℚ),(5698335453372503464421/2361183241434822606848:ℚ)⟩ node11 node1934
def node1936 : BoxExpr 3 := .neg ⟨(540950769961532601139/2361183241434822606848:ℚ),(271570660410142805197/1180591620717411303424:ℚ)⟩ node1919
def node1937 : BoxExpr 3 := .add ⟨(963842377851324071935/4722366482869645213696:ℚ),(484111739784415045223/2361183241434822606848:ℚ)⟩ node332 node1936
def node1938 : BoxExpr 3 := .mul ⟨(688183457785845387361/4722366482869645213696:ℚ),(691311564412144684579/4722366482869645213696:ℚ)⟩ node1937 node335
def node1939 : BoxExpr 3 := .neg ⟨(-691311564412144684579/4722366482869645213696:ℚ),(-688183457785845387361/4722366482869645213696:ℚ)⟩ node1938
def node1940 : BoxExpr 3 := .add ⟨(333929407921108130647/147573952589676412928:ℚ),(10708487448959161541481/4722366482869645213696:ℚ)⟩ node1935 node1939
def node1941 : BoxExpr 3 := .mul ⟨(196721735323170635775/4722366482869645213696:ℚ),(198514179233863161611/4722366482869645213696:ℚ)⟩ node1937 node1937
def node1942 : BoxExpr 3 := .mul ⟨(81246076688469472575/2361183241434822606848:ℚ),(163972712047170971491/4722366482869645213696:ℚ)⟩ node1941 node340
def node1943 : BoxExpr 3 := .add ⟨(5424116603426199562927/2361183241434822606848:ℚ),(2718115040251583128243/1180591620717411303424:ℚ)⟩ node1940 node1942
def node1944 : BoxExpr 3 := .neg ⟨(-2718115040251583128243/1180591620717411303424:ℚ),(-5424116603426199562927/2361183241434822606848:ℚ)⟩ node1943
def node1945 : BoxExpr 3 := .add ⟨(-14668568811066810597/590295810358705651712:ℚ),(116156491897755100955/4722366482869645213696:ℚ)⟩ node1930 node1944
def node1946 : BoxExpr 3 := .var 2
def node1947 : BoxExpr 3 := .mul ⟨(-27070045501097204777/295147905179352825856:ℚ),(-216560364008777638215/2361183241434822606848:ℚ)⟩ node51 node1946
def node1948 : BoxExpr 3 := .add ⟨(120503907088579208151/295147905179352825856:ℚ),(964031256708633665209/2361183241434822606848:ℚ)⟩ node1947 node301
def node1949 : BoxExpr 3 := .mul ⟨(4058836152640857119859/4722366482869645213696:ℚ),(2029418076320428559937/2361183241434822606848:ℚ)⟩ node68 node1948
def node1950 : BoxExpr 3 := .mul ⟨(1207439817914306342765/1180591620717411303424:ℚ),(4829759271657225371081/4722366482869645213696:ℚ)⟩ node1949 node349
def node1951 : BoxExpr 3 := .add ⟨(-35185723168720211149/1180591620717411303424:ℚ),(-70371446337440422297/2361183241434822606848:ℚ)⟩ node1946 node351
def node1952 : BoxExpr 3 := .mul ⟨(1521243306286525165/1180591620717411303424:ℚ),(6084973225146100661/4722366482869645213696:ℚ)⟩ node1951 node308
def node1953 : BoxExpr 3 := .mul ⟨(3318873186025002269/2361183241434822606848:ℚ),(1659436593012501135/1180591620717411303424:ℚ)⟩ node1952 node69
def node1954 : BoxExpr 3 := .add ⟨(2418198509014637687799/2361183241434822606848:ℚ),(4836397018029275375621/4722366482869645213696:ℚ)⟩ node1950 node1953
def node1955 : BoxExpr 3 := .add ⟨(7807699765472768663747/2361183241434822606848:ℚ),(7807699765472768663785/2361183241434822606848:ℚ)⟩ node1954 node358
def node1956 : BoxExpr 3 := .add ⟨(10860514896165254236677/4722366482869645213696:ℚ),(5430257448082627118379/2361183241434822606848:ℚ)⟩ node1955 node361
def node1957 : BoxExpr 3 := .add ⟨(10860500729065805627741/4722366482869645213696:ℚ),(10860500729065805627823/4722366482869645213696:ℚ)⟩ node1956 node325
def node1958 : BoxExpr 3 := .mul ⟨(124435033320574177771/2361183241434822606848:ℚ),(31108758330143544443/590295810358705651712:ℚ)⟩ node1946 node1946
def node1959 : BoxExpr 3 := .neg ⟨(-31108758330143544443/590295810358705651712:ℚ),(-124435033320574177771/2361183241434822606848:ℚ)⟩ node1958
def node1960 : BoxExpr 3 := .add ⟨(559187052028562107269/590295810358705651712:ℚ),(2236748208114248429077/2361183241434822606848:ℚ)⟩ node12 node1959
def node1961 : BoxExpr 3 := .sqrt ⟨(4596247332034572871745/4722366482869645213696:ℚ),(4596247332034572871747/4722366482869645213696:ℚ)⟩ node1960
def node1962 : BoxExpr 3 := .mul ⟨(5693380203896830274607/2361183241434822606848:ℚ),(2846690101948415137307/1180591620717411303424:ℚ)⟩ node50 node1961
def node1963 : BoxExpr 3 := .neg ⟨(271023022695454552883/1180591620717411303424:ℚ),(1084092090781818211533/4722366482869645213696:ℚ)⟩ node1946
def node1964 : BoxExpr 3 := .add ⟨(966032928710077081189/4722366482869645213696:ℚ),(966032928710077081191/4722366482869645213696:ℚ)⟩ node332 node1963
def node1965 : BoxExpr 3 := .mul ⟨(10777304860921797437/73786976294838206464:ℚ),(689747511098995035971/4722366482869645213696:ℚ)⟩ node1964 node335
def node1966 : BoxExpr 3 := .neg ⟨(-689747511098995035971/4722366482869645213696:ℚ),(-10777304860921797437/73786976294838206464:ℚ)⟩ node1965
def node1967 : BoxExpr 3 := .add ⟨(10697012896694665513243/4722366482869645213696:ℚ),(2674253224173666378315/1180591620717411303424:ℚ)⟩ node1962 node1966
def node1968 : BoxExpr 3 := .mul ⟨(24702117644231371653/590295810358705651712:ℚ),(98808470576925486613/2361183241434822606848:ℚ)⟩ node1964 node1964
def node1969 : BoxExpr 3 := .mul ⟨(81615796696540451941/2361183241434822606848:ℚ),(163231593393080903885/4722366482869645213696:ℚ)⟩ node1968 node340
def node1970 : BoxExpr 3 := .add ⟨(10860244490087746417125/4722366482869645213696:ℚ),(10860244490087746417145/4722366482869645213696:ℚ)⟩ node1967 node1969
def node1971 : BoxExpr 3 := .neg ⟨(-10860244490087746417145/4722366482869645213696:ℚ),(-10860244490087746417125/4722366482869645213696:ℚ)⟩ node1970
def node1972 : BoxExpr 3 := .add ⟨(64059744514802649/1180591620717411303424:ℚ),(128119489029605349/2361183241434822606848:ℚ)⟩ node1957 node1971
def node1973 : BoxExpr 3 := .mul ⟨(1093299050506924476855/4722366482869645213696:ℚ),(1093299050506924476861/4722366482869645213696:ℚ)⟩ node78 node1948
def node1974 : BoxExpr 3 := .mul ⟨(162619622574694783845/590295810358705651712:ℚ),(1300956980597558270769/4722366482869645213696:ℚ)⟩ node1973 node349
def node1975 : BoxExpr 3 := .add ⟨(5180188317878929258353/4722366482869645213696:ℚ),(2590094158939464629391/2361183241434822606848:ℚ)⟩ node1974 node385
def node1976 : BoxExpr 3 := .add ⟨(2826322257366175409591/4722366482869645213696:ℚ),(1413161128683087705011/2361183241434822606848:ℚ)⟩ node1975 node387
def node1977 : BoxExpr 3 := .mul ⟨(2843041723168584751901/4722366482869645213696:ℚ),(1421520861584292375955/2361183241434822606848:ℚ)⟩ node77 node1961
def node1978 : BoxExpr 3 := .neg ⟨(-1421520861584292375955/2361183241434822606848:ℚ),(-2843041723168584751901/4722366482869645213696:ℚ)⟩ node1977
def node1979 : BoxExpr 3 := .add ⟨(-16719465802409342319/4722366482869645213696:ℚ),(-16719465802409341879/4722366482869645213696:ℚ)⟩ node1976 node1978
def node1980 : BoxExpr 3 := .mul ⟨(-1838877182323084394395/4722366482869645213696:ℚ),(-1838877182323084394383/4722366482869645213696:ℚ)⟩ node98 node1948
def node1981 : BoxExpr 3 := .mul ⟨(-2282162606366169175087/4722366482869645213696:ℚ),(-1141081303183084587539/2361183241434822606848:ℚ)⟩ node68 node1946
def node1982 : BoxExpr 3 := .add ⟨(-2060519894344626784741/2361183241434822606848:ℚ),(-4121039788689253569461/4722366482869645213696:ℚ)⟩ node1980 node1981
def node1983 : BoxExpr 3 := .mul ⟨(-153243052470688542327/147573952589676412928:ℚ),(-4903777679062033354437/4722366482869645213696:ℚ)⟩ node1982 node349
def node1984 : BoxExpr 3 := .mul ⟨(574026908059008661953/590295810358705651712:ℚ),(2296107632236034647825/2361183241434822606848:ℚ)⟩ node1949 node399
def node1985 : BoxExpr 3 := .add ⟨(-38945301823745507355/590295810358705651712:ℚ),(-311562414589964058787/4722366482869645213696:ℚ)⟩ node1983 node1984
def node1986 : BoxExpr 3 := .mul ⟨(3155639701372002099/4722366482869645213696:ℚ),(3155639701372002101/4722366482869645213696:ℚ)⟩ node1952 node103
def node1987 : BoxExpr 3 := .add ⟨(-54101494382197100717/2361183241434822606848:ℚ),(-54101494382197100715/2361183241434822606848:ℚ)⟩ node403 node1986
def node1988 : BoxExpr 3 := .add ⟨(-209882701677179130137/2361183241434822606848:ℚ),(-419765403354358260217/4722366482869645213696:ℚ)⟩ node1985 node1987
def node1989 : BoxExpr 3 := .add ⟨(-6115510545605589375/295147905179352825856:ℚ),(-97848168729689429827/4722366482869645213696:ℚ)⟩ node1988 node409
def node1990 : BoxExpr 3 := .add ⟨(-1084092090781818211533/2361183241434822606848:ℚ),(-271023022695454552883/590295810358705651712:ℚ)⟩ node1946 node1946
def node1991 : BoxExpr 3 := .neg ⟨(271023022695454552883/590295810358705651712:ℚ),(1084092090781818211533/2361183241434822606848:ℚ)⟩ node1990
def node1992 : BoxExpr 3 := .mul ⟨(4596247332034572871745/2361183241434822606848:ℚ),(4596247332034572871747/2361183241434822606848:ℚ)⟩ node86 node1961
def node1993 : BoxExpr 3 := .inv ⟨(2425973145864083084625/4722366482869645213696:ℚ),(2425973145864083084627/4722366482869645213696:ℚ)⟩ node1992
def node1994 : BoxExpr 3 := .mul ⟨(1113839135281248693589/4722366482869645213696:ℚ),(139229891910156086699/590295810358705651712:ℚ)⟩ node1991 node1993
def node1995 : BoxExpr 3 := .mul ⟨(2759429258272180427493/4722366482869645213696:ℚ),(2759429258272180427503/4722366482869645213696:ℚ)⟩ node50 node1994
def node1996 : BoxExpr 3 := .add ⟨(6131198927041107110071/4722366482869645213696:ℚ),(3065599463520553555041/2361183241434822606848:ℚ)⟩ node1995 node335
def node1997 : BoxExpr 3 := .mul ⟨(-966032928710077081191/4722366482869645213696:ℚ),(-966032928710077081189/4722366482869645213696:ℚ)⟩ node422 node1964
def node1998 : BoxExpr 3 := .mul ⟨(-966032928710077081191/4722366482869645213696:ℚ),(-966032928710077081189/4722366482869645213696:ℚ)⟩ node1964 node422
def node1999 : BoxExpr 3 := .add ⟨(-966032928710077081191/2361183241434822606848:ℚ),(-966032928710077081189/2361183241434822606848:ℚ)⟩ node1997 node1998
def node2000 : BoxExpr 3 := .mul ⟨(-99742899889315458633/295147905179352825856:ℚ),(-1595886398229047338123/4722366482869645213696:ℚ)⟩ node1999 node340
def node2001 : BoxExpr 3 := .add ⟨(4535312528812059771943/4722366482869645213696:ℚ),(4535312528812059771959/4722366482869645213696:ℚ)⟩ node1996 node2000
def node2002 : BoxExpr 3 := .neg ⟨(-4535312528812059771959/4722366482869645213696:ℚ),(-4535312528812059771943/4722366482869645213696:ℚ)⟩ node2001
def node2003 : BoxExpr 3 := .add ⟨(-3985853366553169795/590295810358705651712:ℚ),(-31886826932425358325/4722366482869645213696:ℚ)⟩ node414 node2002
def node2004 : BoxExpr 3 := .mul ⟨(8674068020655636208653/4722366482869645213696:ℚ),(4359028767783019893165/2361183241434822606848:ℚ)⟩ node112 node1921
def node2005 : BoxExpr 3 := .mul ⟨(5151026347794775591953/2361183241434822606848:ℚ),(649609607209702270539/295147905179352825856:ℚ)⟩ node2004 node304
def node2006 : BoxExpr 3 := .add ⟨(21628263614452335346629/4722366482869645213696:ℚ),(44720103328016054742905/4722366482869645213696:ℚ)⟩ node2005 node448
def node2007 : BoxExpr 3 := .mul ⟨(11305496064455096906789/2361183241434822606848:ℚ),(22616076196041503811423/4722366482869645213696:ℚ)⟩ node111 node1934
def node2008 : BoxExpr 3 := .neg ⟨(-22616076196041503811423/4722366482869645213696:ℚ),(-11305496064455096906789/2361183241434822606848:ℚ)⟩ node2007
def node2009 : BoxExpr 3 := .add ⟨(-493906290794584232397/2361183241434822606848:ℚ),(22109111199105860929327/4722366482869645213696:ℚ)⟩ node2006 node2008
def node2010 : BoxExpr 3 := .mul ⟨(-536184350011044820451/4722366482869645213696:ℚ),(-503545687350057894259/4722366482869645213696:ℚ)⟩ node131 node1921
def node2011 : BoxExpr 3 := .mul ⟨(-78908473251294668833/590295810358705651712:ℚ),(-299138607700696476883/2361183241434822606848:ℚ)⟩ node118 node1919
def node2012 : BoxExpr 3 := .add ⟨(-1167452136021402171115/4722366482869645213696:ℚ),(-1101822902751450848025/4722366482869645213696:ℚ)⟩ node2010 node2011
def node2013 : BoxExpr 3 := .mul ⟨(-695923944454905129537/2361183241434822606848:ℚ),(-163577193225868187775/590295810358705651712:ℚ)⟩ node2012 node304
def node2014 : BoxExpr 3 := .mul ⟨(1064507659981781631429/4722366482869645213696:ℚ),(70138408155354727651/295147905179352825856:ℚ)⟩ node118 node1921
def node2015 : BoxExpr 3 := .mul ⟨(1193834008010972648967/4722366482869645213696:ℚ),(1280922027542502322833/4722366482869645213696:ℚ)⟩ node2014 node461
def node2016 : BoxExpr 3 := .add ⟨(-198013880898837610107/4722366482869645213696:ℚ),(-27695518264443179367/4722366482869645213696:ℚ)⟩ node2013 node2015
def node2017 : BoxExpr 3 := .add ⟨(-1477657302896654226033/2361183241434822606848:ℚ),(1385878362307216593537/4722366482869645213696:ℚ)⟩ node2016 node476
def node2018 : BoxExpr 3 := .add ⟨(-271570660410142805197/590295810358705651712:ℚ),(-540950769961532601139/1180591620717411303424:ℚ)⟩ node1919 node1919
def node2019 : BoxExpr 3 := .neg ⟨(540950769961532601139/1180591620717411303424:ℚ),(271570660410142805197/590295810358705651712:ℚ)⟩ node2018
def node2020 : BoxExpr 3 := .mul ⟨(4595730107502071913329/2361183241434822606848:ℚ),(1149190863619995112369/590295810358705651712:ℚ)⟩ node86 node1934
def node2021 : BoxExpr 3 := .inv ⟨(2425700758736719331369/4722366482869645213696:ℚ),(2426246176002250062283/4722366482869645213696:ℚ)⟩ node2020
def node2022 : BoxExpr 3 := .mul ⟨(138932958496004481235/590295810358705651712:ℚ),(1116215403822910160491/4722366482869645213696:ℚ)⟩ node2019 node2021
def node2023 : BoxExpr 3 := .mul ⟨(83887326580614571079/590295810358705651712:ℚ),(353459188003863374829/2361183241434822606848:ℚ)⟩ node117 node2022
def node2024 : BoxExpr 3 := .neg ⟨(-353459188003863374829/2361183241434822606848:ℚ),(-83887326580614571079/590295810358705651712:ℚ)⟩ node2023
def node2025 : BoxExpr 3 := .add ⟨(526012216098637226289/4722366482869645213696:ℚ),(321298267042172066547/2361183241434822606848:ℚ)⟩ node479 node2024
def node2026 : BoxExpr 3 := .add ⟨(-2955314605793308452065/4722366482869645213696:ℚ),(1385878362307216593537/4722366482869645213696:ℚ)⟩ node2016 node492
def node2027 : BoxExpr 3 := .mul ⟨(-1984043718414887071377/4722366482869645213696:ℚ),(-966599979564712073399/2361183241434822606848:ℚ)⟩ node175 node1921
def node2028 : BoxExpr 3 := .mul ⟨(1019288492070667562051/4722366482869645213696:ℚ),(1048705434067288268323/4722366482869645213696:ℚ)⟩ node148 node1919
def node2029 : BoxExpr 3 := .add ⟨(-482377613172109754663/2361183241434822606848:ℚ),(-884494525062135878475/4722366482869645213696:ℚ)⟩ node2027 node2028
def node2030 : BoxExpr 3 := .add ⟨(54533265726448052725/4722366482869645213696:ℚ),(20526363625644048731/590295810358705651712:ℚ)⟩ node2029 node2028
def node2031 : BoxExpr 3 := .mul ⟨(32384146391210280583/2361183241434822606848:ℚ),(48943464143568177731/1180591620717411303424:ℚ)⟩ node2030 node304
def node2032 : BoxExpr 3 := .mul ⟨(-1864299909468672570441/4722366482869645213696:ℚ),(-1813608106089307768491/4722366482869645213696:ℚ)⟩ node148 node1921
def node2033 : BoxExpr 3 := .mul ⟨(-2294739006567915382483/4722366482869645213696:ℚ),(-2269661350904530419741/4722366482869645213696:ℚ)⟩ node36 node1919
def node2034 : BoxExpr 3 := .add ⟨(-1039759729009146988231/1180591620717411303424:ℚ),(-510408682124229773529/590295810358705651712:ℚ)⟩ node2032 node2033
def node2035 : BoxExpr 3 := .mul ⟨(-2373612360308748588225/2361183241434822606848:ℚ),(-4579343225876993614731/4722366482869645213696:ℚ)⟩ node2034 node461
def node2036 : BoxExpr 3 := .add ⟨(-1170614106958769153821/1180591620717411303424:ℚ),(-4383569369302720903807/4722366482869645213696:ℚ)⟩ node2031 node2035
def node2037 : BoxExpr 3 := .mul ⟨(9956862762843860271963/2361183241434822606848:ℚ),(160519591610236863183/36893488147419103232:ℚ)⟩ node1922 node514
def node2038 : BoxExpr 3 := .add ⟨(3791625201267555841869/1180591620717411303424:ℚ),(15967164500233324872693/4722366482869645213696:ℚ)⟩ node2035 node2037
def node2039 : BoxExpr 3 := .add ⟨(163813193394299168003/73786976294838206464:ℚ),(5791797565465301984443/2361183241434822606848:ℚ)⟩ node2036 node2038
def node2040 : BoxExpr 3 := .mul ⟨(45705910823144633/18446744073709551616:ℚ),(3277048926805919773/1180591620717411303424:ℚ)⟩ node1925 node189
def node2041 : BoxExpr 3 := .add ⟨(-5207204063546946807/590295810358705651712:ℚ),(-19709038182203553421/2361183241434822606848:ℚ)⟩ node518 node2040
def node2042 : BoxExpr 3 := .add ⟨(-5938498636717260935/295147905179352825856:ℚ),(-11493043554504736597/590295810358705651712:ℚ)⟩ node518 node2041
def node2043 : BoxExpr 3 := .add ⟨(649314274940479411077/295147905179352825856:ℚ),(5745825391247283038055/2361183241434822606848:ℚ)⟩ node2039 node2042
def node2044 : BoxExpr 3 := .add ⟨(21492761677414241948755/4722366482869645213696:ℚ),(28085121821822012550653/4722366482869645213696:ℚ)⟩ node2043 node527
def node2045 : BoxExpr 3 := .mul ⟨(-2426246176002250062283/2361183241434822606848:ℚ),(-2425700758736719331369/2361183241434822606848:ℚ)⟩ node6 node2021
def node2046 : BoxExpr 3 := .mul ⟨(138932958496004481235/295147905179352825856:ℚ),(1116215403822910160491/2361183241434822606848:ℚ)⟩ node86 node2022
def node2047 : BoxExpr 3 := .mul ⟨(17889958602422188077209/4722366482869645213696:ℚ),(8949002299204229692131/2361183241434822606848:ℚ)⟩ node2020 node2020
def node2048 : BoxExpr 3 := .inv ⟨(1245990583805843236987/4722366482869645213696:ℚ),(155818870896599239833/590295810358705651712:ℚ)⟩ node2047
def node2049 : BoxExpr 3 := .mul ⟨(586516641414467077765/4722366482869645213696:ℚ),(147322258475277649693/1180591620717411303424:ℚ)⟩ node2046 node2048
def node2050 : BoxExpr 3 := .neg ⟨(-147322258475277649693/1180591620717411303424:ℚ),(-586516641414467077765/4722366482869645213696:ℚ)⟩ node2049
def node2051 : BoxExpr 3 := .mul ⟨(-271107484248841018635/4722366482869645213696:ℚ),(-268743757960613235241/4722366482869645213696:ℚ)⟩ node2019 node2050
def node2052 : BoxExpr 3 := .add ⟨(-5123599836253341143201/4722366482869645213696:ℚ),(-5120145275434051897979/4722366482869645213696:ℚ)⟩ node2045 node2051
def node2053 : BoxExpr 3 := .mul ⟨(-12702846637610519166795/4722366482869645213696:ℚ),(-12675279193343180833065/4722366482869645213696:ℚ)⟩ node11 node2052
def node2054 : BoxExpr 3 := .add ⟨(-2450748603954932636885/2361183241434822606848:ℚ),(-4873929763642526940039/4722366482869645213696:ℚ)⟩ node2053 node546
def node2055 : BoxExpr 3 := .neg ⟨(4873929763642526940039/4722366482869645213696:ℚ),(2450748603954932636885/2361183241434822606848:ℚ)⟩ node2054
def cert_iv11 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-9403/40960:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/40960:ℚ)],
    whole := node1945, centerValue := node1972, gradient := ![node1979, node1989, node2003],
    hessian := ![![node2009, node2017, node2025], ![node2026, node2044, node536], ![node2025, node536, node2055]] }

end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part3
end

section
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646CheckB4Part3
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part3

theorem cert_iv8_check : cert_iv8.check = true := by decide +kernel

theorem cert_iv8_lower_pos : 0 < cert_iv8.lower := by decide +kernel

theorem positive_iv8 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(149/640:ℝ)) ≤ r) (hrhi : r ≤ (-(4749/20480:ℝ))) :
    0 < node1534.eval ![A,ρ,r] := by
  apply cert_iv8.positive_sound cert_iv8_check cert_iv8_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv8,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv8,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv8,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv9_check : cert_iv9.check = true := by decide +kernel

theorem cert_iv9_lower_pos : 0 < cert_iv9.lower := by decide +kernel

theorem positive_iv9 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(4749/20480:ℝ)) ≤ r) (hrhi : r ≤ (-(473/2048:ℝ))) :
    0 < node1671.eval ![A,ρ,r] := by
  apply cert_iv9.positive_sound cert_iv9_check cert_iv9_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv9,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv9,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv9,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv10_check : cert_iv10.check = true := by decide +kernel

theorem cert_iv10_lower_pos : 0 < cert_iv10.lower := by decide +kernel

theorem positive_iv10 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(473/2048:ℝ)) ≤ r) (hrhi : r ≤ (-(4711/20480:ℝ))) :
    0 < node1808.eval ![A,ρ,r] := by
  apply cert_iv10.positive_sound cert_iv10_check cert_iv10_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv10,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv10,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv10,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv11_check : cert_iv11.check = true := by decide +kernel

theorem cert_iv11_lower_pos : 0 < cert_iv11.lower := by decide +kernel

theorem positive_iv11 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(4711/20480:ℝ)) ≤ r) (hrhi : r ≤ (-(1173/5120:ℝ))) :
    0 < node1945.eval ![A,ρ,r] := by
  apply cert_iv11.positive_sound cert_iv11_check cert_iv11_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv11,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv11,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv11,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part3
end

section
-- Source module: Solutions.GaussLocalMaxCapacity

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem capacity_le_add_two (D ρ : ℝ) : capacity D ρ ≤ D+2 := by
  unfold capacity
  split
  · exact min_le_left _ _
  · split
    · exact min_le_left _ _
    · linarith

theorem capacity_ge_add_one (D ρ : ℝ) (hD : 0 ≤ D) (hρ : ρ∈Set.Icc (-(1/2):ℝ) 1) :
    D+1 ≤ capacity D ρ := by
  have hDD : 0 ≤ D*(D+1) := by positivity
  have hroot (r : ℝ) (hr : 2/3 ≤ r) : D+1 ≤ (1+Real.sqrt (1+6*D*(D+1)*r))/2 := by
    have hrad : (2*D+1)^2 ≤ 1+6*D*(D+1)*r := by
      have h := mul_nonneg hDD (sub_nonneg.mpr hr)
      nlinarith only [h]
    have hnon : 0 ≤ 1+6*D*(D+1)*r := (sq_nonneg _).trans hrad
    have hsq := Real.sq_sqrt hnon
    have hn := Real.sqrt_nonneg (1+6*D*(D+1)*r)
    nlinarith only [hrad,hsq,hn,hD]
  unfold capacity
  split
  · rename_i hρ0
    apply le_min (by linarith)
    apply hroot
    apply (le_div_iff₀ (show 0<1-4*ρ by linarith)).mpr
    nlinarith only [hρ.1]
  · rename_i hρ0
    split
    · rename_i hρ4
      have hρp : 0<ρ := lt_of_not_ge hρ0
      apply le_min (by linarith)
      have h := hroot (1/(1+2*ρ)) (by
        apply (le_div_iff₀ (show 0<1+2*ρ by linarith)).mpr
        nlinarith only [hρ4])
      simpa only [div_eq_mul_inv,one_mul] using h
    · exact le_rfl

theorem capacity_D5_ge (ρ : ℝ) (hρ : ρ∈Set.Icc (-(1/2):ℝ) 1) : D5+1 ≤ capacity D5 ρ := by
  apply capacity_ge_add_one _ _ _ hρ
  norm_num [D5,beta5]

end
end GaussLocalMaxColoring.Main
end

section
-- Source module: Solutions.GaussLocalMaxCertificateSubstitution

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace GaussLocalMaxColoring.Certificate.CertificateFormula

def subst {m n : ℕ} (s : Fin m → CertificateFormula n) :
    CertificateFormula m → CertificateFormula n
  | .lit q => .lit q
  | .var i => s i
  | .add a b => .add (a.subst s) (b.subst s)
  | .mul a b => .mul (a.subst s) (b.subst s)
  | .neg a => .neg (a.subst s)
  | .inv a => .inv (a.subst s)
  | .sqrt a => .sqrt (a.subst s)

theorem subst_eval {m n : ℕ} (s : Fin m → CertificateFormula n)
    (e : CertificateFormula m) (x : Fin n → ℝ) :
    (e.subst s).eval x = e.eval (fun i => (s i).eval x) := by
  induction e <;> simp_all only [subst,eval]

theorem normalize_subst_eval {m n : ℕ} (s : Fin m → CertificateFormula n)
    (e : CertificateFormula m) (x : Fin n → ℝ) :
    (e.subst s).normalize.eval x = e.eval (fun i => (s i).eval x) := by
  rw [normalize_eval,subst_eval]

end GaussLocalMaxColoring.Certificate.CertificateFormula
end

section
-- Source module: Solutions.GaussLocalMaxCase1Patterns

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace GaussLocalMaxColoring.Certificate
open GaussLocalMaxColoring.Main

/-- The four exact zeta branches, without unnecessary outer domain bounds. -/
def sourceFADomain (j : ℕ) (r : ℝ) : Prop :=
  (j = 0 ∧ r ≤ -(1/40)) ∨
  (j = 1 ∧ -(1/40) ≤ r ∧ r ≤ 1/50) ∨
  (j = 2 ∧ 1/50 ≤ r ∧ r ≤ 1/4) ∨
  (j = 3 ∧ 1/4 ≤ r)

/-- Exact syntax of the supplementary source fA expression before substitution.
    A and r can themselves be arbitrary expressions in any number of variables. -/
def sourceFAPattern {m : ℕ} (A r : CertificateFormula m) (j : ℕ) : CertificateFormula m :=
  let d := .add A (.neg (.lit 2))
  let f := .mul
    (.add (.add (.mul A (.lit (13/25))) (.lit (713/500)))
      (.mul (.mul d d) (.lit (123/50))))
    (.sqrt (.add (.lit 1) (.neg (.mul r r))))
  let z1 := .add (.lit (-(1/40))) (.neg r)
  let z2 := .add r (.neg (.lit (1/50)))
  let z3 := .add r (.neg (.lit (1/4)))
  let f2 := .add f (.add (.mul z2 (.lit (-(4/5))))
    (.mul (.mul z2 z2) (.lit (9/20))))
  if j = 0 then .add (.add f (.neg (.mul z1 (.lit (357/500)))))
    (.mul (.mul z1 z1) (.lit (413/500)))
  else if j = 1 then f
  else if j = 2 then f2
  else .add f2 (.add (.mul z3 (.lit (39/100))) (.mul (.mul z3 z3) (.lit (13/20))))

theorem sourceFAPattern_subst {m n : ℕ} (s : Fin m → CertificateFormula n)
    (A r : CertificateFormula m) (j : ℕ) :
    (sourceFAPattern A r j).subst s = sourceFAPattern (A.subst s) (r.subst s) j := by
  unfold sourceFAPattern
  split_ifs <;> rfl

theorem sourceFAPattern_eval {m : ℕ} (A r : CertificateFormula m) (j : ℕ)
    (x : Fin m → ℝ) (hj : sourceFADomain j (r.eval x)) :
    (sourceFAPattern A r j).eval x = fA (A.eval x) (r.eval x) := by
  rcases hj with ⟨rfl,hhi⟩ | ⟨rfl,hlo,hhi⟩ | ⟨rfl,hlo,hhi⟩ | ⟨rfl,hlo⟩
  · have h1 : max (-(1/40:ℝ)-r.eval x) 0 = -(1/40)-r.eval x := max_eq_left (by linarith)
    have h2 : max (r.eval x-(1/50:ℝ)) 0 = 0 := max_eq_right (by linarith)
    have h3 : max (r.eval x-(1/4:ℝ)) 0 = 0 := max_eq_right (by linarith)
    simp only [fA,h1,h2,h3]
    norm_num [sourceFAPattern,CertificateFormula.eval,ftilde,pow_two,sub_eq_add_neg] <;> ring_nf <;> simp
  · have h1 : max (-(1/40:ℝ)-r.eval x) 0 = 0 := max_eq_right (by linarith)
    have h2 : max (r.eval x-(1/50:ℝ)) 0 = 0 := max_eq_right (by linarith)
    have h3 : max (r.eval x-(1/4:ℝ)) 0 = 0 := max_eq_right (by linarith)
    simp only [fA,h1,h2,h3]
    norm_num [sourceFAPattern,CertificateFormula.eval,ftilde,pow_two,sub_eq_add_neg] <;> ring_nf <;> simp
  · have h1 : max (-(1/40:ℝ)-r.eval x) 0 = 0 := max_eq_right (by linarith)
    have h2 : max (r.eval x-(1/50:ℝ)) 0 = r.eval x-1/50 := max_eq_left (by linarith)
    have h3 : max (r.eval x-(1/4:ℝ)) 0 = 0 := max_eq_right (by linarith)
    simp only [fA,h1,h2,h3]
    norm_num [sourceFAPattern,CertificateFormula.eval,ftilde,pow_two,sub_eq_add_neg] <;> ring_nf <;> simp
  · have h1 : max (-(1/40:ℝ)-r.eval x) 0 = 0 := max_eq_right (by linarith)
    have h2 : max (r.eval x-(1/50:ℝ)) 0 = r.eval x-1/50 := max_eq_left (by linarith)
    have h3 : max (r.eval x-(1/4:ℝ)) 0 = r.eval x-1/4 := max_eq_left (by linarith)
    simp only [fA,h1,h2,h3]
    norm_num [sourceFAPattern,CertificateFormula.eval,ftilde,pow_two,sub_eq_add_neg] <;> ring_nf <;> simp

theorem sourceFAPattern_normalize_subst_eval {m n : ℕ}
    (s : Fin m → CertificateFormula n) (A r : CertificateFormula m) (j : ℕ)
    (x : Fin n → ℝ) (hj : sourceFADomain j (r.eval (fun i => (s i).eval x))) :
    ((sourceFAPattern A r j).subst s).normalize.eval x =
      fA (A.eval (fun i => (s i).eval x)) (r.eval (fun i => (s i).eval x)) := by
  rw [CertificateFormula.normalize_subst_eval]
  exact sourceFAPattern_eval A r j _ hj

noncomputable def case1ScaledLhs (A ρ r θ sa sb sc σ : ℝ) : ℝ :=
  fA A ρ*(1/2+ρ*r)/(1-ρ^2) + (-sb+σ*sc)*(r+ρ/2)/Real.sqrt (1-ρ^2) +
    3/2*sa-Real.sqrt 3/2*θ*A

def sourceValuePattern {m : ℕ} (A ρ r θ sa sb sc σ : CertificateFormula m)
    (j : ℕ) : CertificateFormula m :=
  let base := .add (.lit 1) (.neg (.mul ρ ρ))
  let num := .add (.mul ρ r) (.lit (1/2))
  let comp := .add r (.mul ρ (.inv (.lit 2)))
  let coeff := .add (.neg sb) (.mul σ sc)
  let first := .mul (.mul (sourceFAPattern A ρ j) num) (.inv base)
  let second := .mul (.mul comp coeff) (.inv (.sqrt base))
  let loss := .mul (.mul (.mul (.sqrt (.lit 3)) (.inv (.lit 2))) θ) A
  .add (.add (.add (.add first second) (.mul sa (.lit (3/2)))) (.neg loss))
    (.neg (.lit (3/1000000)))

theorem sourceValuePattern_eval {m : ℕ} (A ρ r θ sa sb sc σ : CertificateFormula m)
    (j : ℕ) (x : Fin m → ℝ) (hj : sourceFADomain j (ρ.eval x)) :
    (sourceValuePattern A ρ r θ sa sb sc σ j).eval x =
      case1ScaledLhs (A.eval x) (ρ.eval x) (r.eval x) (θ.eval x)
        (sa.eval x) (sb.eval x) (sc.eval x) (σ.eval x)-3/10^6 := by
  have hf := sourceFAPattern_eval A ρ j x hj
  simp only [sourceValuePattern,CertificateFormula.eval,hf]
  unfold case1ScaledLhs
  norm_num [pow_two,div_eq_mul_inv,sub_eq_add_neg]
  ring

theorem sourceValuePattern_normalize_subst_eval {m n : ℕ}
    (s : Fin m → CertificateFormula n) (A ρ r θ sa sb sc σ : CertificateFormula m)
    (j : ℕ) (x : Fin n → ℝ)
    (hj : sourceFADomain j (ρ.eval (fun i => (s i).eval x))) :
    ((sourceValuePattern A ρ r θ sa sb sc σ j).subst s).normalize.eval x =
      case1ScaledLhs (A.eval (fun i => (s i).eval x)) (ρ.eval (fun i => (s i).eval x))
        (r.eval (fun i => (s i).eval x)) (θ.eval (fun i => (s i).eval x))
        (sa.eval (fun i => (s i).eval x)) (sb.eval (fun i => (s i).eval x))
        (sc.eval (fun i => (s i).eval x)) (σ.eval (fun i => (s i).eval x))-3/10^6 := by
  rw [CertificateFormula.normalize_subst_eval]
  exact sourceValuePattern_eval A ρ r θ sa sb sc σ j _ hj

theorem case1ScaledLhs_public_difference (A ρ r a b c θ σ : ℝ) (hbase : 0 < 1-ρ^2) :
    case1ScaledLhs A ρ r θ ((1+θ)*a) ((1+θ)*b) (θ*c) σ =
      l40Lhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) a b c θ r -
        θ*c*(|r+ρ/2|-σ*(r+ρ/2))/Real.sqrt (1-ρ^2) := by
  have hs := Real.sq_sqrt hbase.le
  have hg : l40Lhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) a b c θ r -
        θ*c*(|r+ρ/2|-σ*(r+ρ/2))/Real.sqrt (1-ρ^2) =
      fA A ρ*(1/2+ρ*r)/(Real.sqrt (1-ρ^2))^2 +
        (-((1+θ)*b)+σ*(θ*c))*(r+ρ/2)/Real.sqrt (1-ρ^2) +
        3/2*((1+θ)*a)-Real.sqrt 3/2*θ*A := by
    unfold l40Lhs
    simp only [div_eq_mul_inv,inv_pow]
    ring
  rw [hs] at hg
  exact hg.symm


end GaussLocalMaxColoring.Certificate
end

section
-- Source module: Solutions.GaussLocalMaxCase1CapacityCore


set_option autoImplicit false

set_option maxHeartbeats 3000000

namespace GaussLocalMaxColoring.Certificate.CapacityCore

open GaussLocalMaxColoring.Main

noncomputable section



def thresholdCapacity (j : ℕ) (ρ : ℝ) : ℝ :=
  if j = 1 then (1 + Real.sqrt (1+6*Da*(Da+1)*((1-2*ρ)/(1-4*ρ))))/2
  else if j = 2 then Da+2
  else if j = 3 then (1 + Real.sqrt (1+6*Da*(Da+1)/(1+2*ρ)))/2
  else Da+1

def thresholdCapacityDomain (j : ℕ) (ρ : ℝ) : Prop :=
  (j = 1 ∧ ρ ≤ 0) ∨ (j = 2) ∨
  (j = 3 ∧ 0 ≤ ρ ∧ ρ ≤ 1/4) ∨ (j = 4 ∧ 1/4 ≤ ρ)

theorem capacity_le_at_quarter (D : ℝ) (hD : 0 ≤ D) : capacity D (1/4) ≤ D+1 := by
  have hrad : 1+6*D*(D+1)/(1+2*(1/4:ℝ)) = (2*D+1)^2 := by ring
  have hroot : (1+Real.sqrt (1+6*D*(D+1)/(1+2*(1/4:ℝ))))/2 = D+1 := by
    rw [hrad, Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith)]
    ring
  unfold capacity
  norm_num only [show ¬ ((1/4:ℝ) ≤ 0) by norm_num, if_false, le_refl, if_true]
  norm_num at hroot
  rw [hroot]
  exact min_le_right _ _

theorem thresholdCapacity_upper (j : ℕ) (ρ : ℝ)
    (hj : thresholdCapacityDomain j ρ) : capacity Da ρ ≤ thresholdCapacity j ρ := by
  rcases hj with ⟨rfl, hρ⟩ | rfl | ⟨rfl, hlo, hhi⟩ | ⟨rfl, hρ⟩
  · change capacity Da ρ ≤ (1 + Real.sqrt (1+6*Da*(Da+1)*((1-2*ρ)/(1-4*ρ))))/2
    simp only [capacity, if_pos hρ]
    exact min_le_right _ _
  · exact capacity_le_add_two Da ρ
  · change capacity Da ρ ≤ (1 + Real.sqrt (1+6*Da*(Da+1)/(1+2*ρ)))/2
    by_cases hz : ρ = 0
    · subst ρ
      simpa [capacity] using min_le_right (Da+2) ((1+Real.sqrt (1+6*Da*(Da+1)))/2)
    · have hp : 0 < ρ := lt_of_le_of_ne hlo (Ne.symm hz)
      simp only [capacity, if_neg (not_le.mpr hp), if_pos hhi]
      exact min_le_right _ _
  · change capacity Da ρ ≤ Da+1
    by_cases hz : ρ = 1/4
    · subst ρ
      exact capacity_le_at_quarter Da (by norm_num [Da, D5, beta5, eta5])
    · have hp : 1/4 < ρ := lt_of_le_of_ne hρ (Ne.symm hz)
      simp only [capacity,
        if_neg (show ¬ ρ ≤ 0 by linarith), if_neg (not_le.mpr hp), le_refl]

def sourceCapacityKQ : ℚ := 7033791386230630914920427/47247072600500000000000
def sourceCapacity2Q : ℚ := 2000000922197/307399000000
def sourceCapacity4Q : ℚ := 1692601922197/307399000000

theorem sourceCapacityKQ_cast : (sourceCapacityKQ:ℝ) = 6*Da*(Da+1) := by
  norm_num [sourceCapacityKQ,Da,D5,beta5,eta5]
theorem sourceCapacity2Q_cast : (sourceCapacity2Q:ℝ) = Da+2 := by
  norm_num [sourceCapacity2Q,Da,D5,beta5,eta5]
theorem sourceCapacity4Q_cast : (sourceCapacity4Q:ℝ) = Da+1 := by
  norm_num [sourceCapacity4Q,Da,D5,beta5,eta5]

def sourceCapacityPattern {m : ℕ} (r : CertificateFormula m) (j : ℕ) :
    CertificateFormula m :=
  let numerator := .add (.lit 1) (.neg (.mul r (.lit 2)))
  let denominator := .add (.lit 1) (.neg (.mul r (.lit 4)))
  let ratio := .mul (.mul numerator (.lit sourceCapacityKQ)) (.inv denominator)
  let rad3 := .mul (.lit sourceCapacityKQ) (.inv (.add (.lit 1) (.mul r (.lit 2))))
  if j = 1 then .mul (.add (.lit 1) (.sqrt (.add (.lit 1) ratio))) (.inv (.lit 2))
  else if j = 2 then .lit sourceCapacity2Q
  else if j = 3 then .mul (.add (.lit 1) (.sqrt (.add (.lit 1) rad3))) (.inv (.lit 2))
  else .lit sourceCapacity4Q

theorem sourceCapacityPattern_eval {m : ℕ} (r : CertificateFormula m) (j : ℕ)
    (x : Fin m → ℝ) :
    (sourceCapacityPattern r j).eval x = thresholdCapacity j (r.eval x) := by
  by_cases h1 : j = 1
  · subst j
    simp only [sourceCapacityPattern,ite_true,CertificateFormula.eval]
    rw [sourceCapacityKQ_cast]
    norm_num only [Rat.cast_one,Rat.cast_ofNat]
    simp only [thresholdCapacity,ite_true]
    congr 2 <;> ring
  by_cases h2 : j = 2
  · subst j
    simpa [sourceCapacityPattern,thresholdCapacity,CertificateFormula.eval] using sourceCapacity2Q_cast
  by_cases h3 : j = 3
  · subst j
    simp only [sourceCapacityPattern,show ¬ (3:ℕ)=1 by decide,
      show ¬ (3:ℕ)=2 by decide,ite_false,ite_true,CertificateFormula.eval]
    rw [sourceCapacityKQ_cast]
    norm_num only [Rat.cast_one,Rat.cast_ofNat]
    simp only [thresholdCapacity,show ¬ (3:ℕ)=1 by decide,
      show ¬ (3:ℕ)=2 by decide,ite_false,ite_true]
    congr 2 <;> ring
  simpa [sourceCapacityPattern,thresholdCapacity,h1,h2,h3,CertificateFormula.eval]
    using sourceCapacity4Q_cast

theorem sourceCapacityPattern_subst {m n : ℕ} (s : Fin m → CertificateFormula n)
    (r : CertificateFormula m) (j : ℕ) :
    (sourceCapacityPattern r j).subst s = sourceCapacityPattern (r.subst s) j := by
  unfold sourceCapacityPattern
  split_ifs <;> rfl

theorem case1_qc_of_squared_capacity_gap (r v : ℝ) (j : ℕ)
    (hrlo : -(1/2:ℝ) ≤ r) (hrhi : r ≤ 1)
    (hdom : thresholdCapacityDomain j r) (hv : 0 < v)
    (hgap : 0 < v^2-(1-r^2)*(thresholdCapacity j r+1/4)) : qc r < v := by
  have hbase : 0 ≤ 1-r^2 := by nlinarith
  have hDa : 0 ≤ Da := by norm_num [Da,D5,beta5,eta5]
  have hcap := capacity_ge_add_one Da r hDa ⟨hrlo,hrhi⟩
  have hrad : 0 ≤ (1-r^2)*(capacity Da r+1/4) := by
    apply mul_nonneg hbase
    linarith
  have hupper := mul_le_mul_of_nonneg_left
    (add_le_add_right (thresholdCapacity_upper j r hdom) (1/4)) hbase
  have hqc : (qc r)^2 = (1-r^2)*(capacity Da r+1/4) := Real.sq_sqrt hrad
  have hqc0 : 0 ≤ qc r := Real.sqrt_nonneg _
  nlinarith



end

end GaussLocalMaxColoring.Certificate.CapacityCore

end

section
-- Source module: Solutions.GaussLocalMaxCase2Semantics

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace GaussLocalMaxColoring.Certificate
open GaussLocalMaxColoring.Main

lemma l40Lhs_monotone_threshold (A ρ a b c θ ρ' : ℝ) {L L' : ℝ}
    (hL : L ≤ L') (hfactor : 0 ≤ 1 / 2 + ρ * ρ') :
    l40Lhs A ρ L a b c θ ρ' ≤ l40Lhs A ρ L' a b c θ ρ' := by
  unfold l40Lhs
  gcongr

lemma l40Lhs_antitone_parameter (ρ L a b c θ ρ' : ℝ) {A A' : ℝ}
    (hθ : 0 ≤ θ) (hA : A ≤ A') :
    l40Lhs A' ρ L a b c θ ρ' ≤ l40Lhs A ρ L a b c θ ρ' := by
  unfold l40Lhs
  gcongr

/-- Exact lower-envelope transfer used by the source's case2_A0 row:
    only the positive L term uses A_lo, while the negative term uses A_hi. -/
theorem case2_lower_envelope (Alo Ahi A a b c θ ρ' : ℝ)
    (hlo : Alo ≤ A) (hhi : A ≤ Ahi) (hθ : 0 ≤ θ) (hr : ρ' ≤ 1) :
    l40Lhs Ahi (-(1/2)) Alo a b c θ ρ' ≤
      l40Lhs A (-(1/2)) A a b c θ ρ' := by
  calc
    _ ≤ l40Lhs Ahi (-(1/2)) A a b c θ ρ' :=
      l40Lhs_monotone_threshold Ahi (-(1/2)) a b c θ ρ' hlo (by nlinarith)
    _ ≤ _ := l40Lhs_antitone_parameter (-(1/2)) A a b c θ ρ' hθ hhi

/-- The two algebraic norm constraints use the public margins exactly. -/
def Case2Static (a b μ c κ θ : ℝ) : Prop :=
  (0 ≤ a ∧ 0 ≤ μ ∧ 0 ≤ c ∧ 0 ≤ κ ∧ 0 < θ ∧ θ < 14) ∧
  (a ^ 2 + b ^ 2 + μ ^ 2 ≤ 1 - 1 / 10 ^ 12 ∧
    c ^ 2 + κ ^ 2 ≤ 1 / 4 - 1 / 10 ^ 20)

/-- Assembly of a case2_A0 certificate on the whole A-interval. The certificate
    inequalities remain explicit obligations, not assumed for the target theorem. -/
theorem case2_of_lower_envelope (Alo Ahi A a b μ c κ θ : ℝ)
    (hlo0 : 0 ≤ Alo) (hlo : Alo ≤ A) (hhi : A ≤ Ahi)
    (hstatic : Case2Static a b μ c κ θ)
    (hiii : Da + 1 / 4 + 1 / 10 ^ 18 ≤
      Alo ^ 2 + (3999/1000) * (μ + θ * (μ + κ)) ^ 2)
    (hiv : ∀ ρ' : ℝ, -(1/2) ≤ ρ' → ρ' ≤ 1 →
      qc ρ' + 3 / 10 ^ 6 ≤ l40Lhs Ahi (-(1/2)) Alo a b c θ ρ') :
    L40Case2 A a b μ c κ θ := by
  refine ⟨hstatic.1, hstatic.2, ?_, ?_⟩
  · have hsq : Alo ^ 2 ≤ A ^ 2 := by nlinarith
    exact hiii.trans (by linarith)
  · intro ρ' hrlo hrhi _
    have hr1 : ρ' ≤ 1 := by linarith
    have hbound := (hiv ρ' hrlo hr1).trans
      (case2_lower_envelope Alo Ahi A a b c θ ρ' hlo hhi hstatic.1.2.2.2.2.1.le hr1)
    exact (add_le_add (min_le_left (qc ρ') (fA A ρ')) le_rfl).trans hbound

def l40SignedLhs (A ρ L a b c θ σ ρ' : ℝ) : ℝ :=
  (L * (1 / 2 + ρ * ρ') - (1 + θ) * b * (ρ' + ρ / 2) +
      θ * c * (σ * (ρ' + ρ / 2))) / Real.sqrt (1 - ρ ^ 2)
    + 3 / 2 * (1 + θ) * a - Real.sqrt 3 / 2 * θ * A

/-- Every source sign choice gives a valid lower bound, including at zero. -/
theorem l40SignedLhs_le (A ρ L a b c θ σ ρ' : ℝ)
    (hθ : 0 ≤ θ) (hc : 0 ≤ c) (hσ : σ = -1 ∨ σ = 1) :
    l40SignedLhs A ρ L a b c θ σ ρ' ≤ l40Lhs A ρ L a b c θ ρ' := by
  have hs : σ * (ρ' + ρ / 2) ≤ |ρ' + ρ / 2| := by
    rcases hσ with rfl | rfl
    · simpa using neg_le_abs (ρ' + ρ / 2)
    · simpa using le_abs_self (ρ' + ρ / 2)
  have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hθ hc)
  have hdiv := div_le_div_of_nonneg_right
    (add_le_add (le_refl (L * (1 / 2 + ρ * ρ') - (1 + θ) * b * (ρ' + ρ / 2))) hm)
    (Real.sqrt_nonneg (1 - ρ ^ 2))
  exact sub_le_sub_right (add_le_add hdiv (le_refl (3 / 2 * (1 + θ) * a))) _

/-- Convexity in A removes the parameter direction from every Case2 child. -/
theorem fA_le_chord (A B r t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    fA ((1-t)*A+t*B) r ≤ (1-t)*fA A r+t*fA B r := by
  have hpos : 0 ≤ (246/100:ℝ) * Real.sqrt (1-r^2) * t * (1-t) * (A-B)^2 := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) ht0)
        (by linarith)) (sq_nonneg _)
  have hid : (1-t)*fA A r+t*fA B r-fA ((1-t)*A+t*B) r =
      (246/100:ℝ)*Real.sqrt (1-r^2)*t*(1-t)*(A-B)^2 := by
    unfold fA ftilde
    ring
  linarith only [hid, hpos]

theorem case2Signed_chord (A B a b c θ σ r t : ℝ) :
    l40SignedLhs ((1-t)*A+t*B) (-(1/2)) ((1-t)*A+t*B) a b c θ σ r =
      (1-t)*l40SignedLhs A (-(1/2)) A a b c θ σ r +
        t*l40SignedLhs B (-(1/2)) B a b c θ σ r := by
  unfold l40SignedLhs
  ring

/-- For fixed correlation, endpoint checks against f_A extend to every convex combination. -/
theorem case2Signed_fA_of_endpoints (A B a b c θ σ r t margin : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hA : fA A r+margin ≤ l40SignedLhs A (-(1/2)) A a b c θ σ r)
    (hB : fA B r+margin ≤ l40SignedLhs B (-(1/2)) B a b c θ σ r) :
    fA ((1-t)*A+t*B) r+margin ≤
      l40SignedLhs ((1-t)*A+t*B) (-(1/2)) ((1-t)*A+t*B) a b c θ σ r := by
  have hc := fA_le_chord A B r t ht0 ht1
  have ha := mul_le_mul_of_nonneg_left hA (show 0 ≤ 1-t by linarith)
  have hb := mul_le_mul_of_nonneg_left hB ht0
  rw [case2Signed_chord]
  nlinarith only [hc, ha, hb]

/-- The q_c branch is independent of A, so affine interpolation suffices. -/
theorem case2Signed_qc_of_endpoints (A B a b c θ σ r t margin : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hA : qc r+margin ≤ l40SignedLhs A (-(1/2)) A a b c θ σ r)
    (hB : qc r+margin ≤ l40SignedLhs B (-(1/2)) B a b c θ σ r) :
    qc r+margin ≤
      l40SignedLhs ((1-t)*A+t*B) (-(1/2)) ((1-t)*A+t*B) a b c θ σ r := by
  have ha := mul_le_mul_of_nonneg_left hA (show 0 ≤ 1-t by linarith)
  have hb := mul_le_mul_of_nonneg_left hB ht0
  rw [case2Signed_chord]
  nlinarith only [ha, hb]

theorem exists_unit_interpolation (Alo Ahi A : ℝ) (hlo : Alo ≤ A) (hhi : A ≤ Ahi) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ A = (1-t)*Alo+t*Ahi := by
  by_cases hlt : Alo < Ahi
  · have hp : 0 < Ahi-Alo := sub_pos.mpr hlt
    refine ⟨(A-Alo)/(Ahi-Alo), div_nonneg (sub_nonneg.mpr hlo) hp.le, ?_, ?_⟩
    · exact (div_le_one hp).mpr (by linarith)
    · field_simp
      ring
  · refine ⟨0, by norm_num, by norm_num, ?_⟩
    have he : A = Alo := by linarith
    simpa using he

theorem case2Lhs_chord (A B a b c θ r t : ℝ) :
    l40Lhs ((1-t)*A+t*B) (-(1/2)) ((1-t)*A+t*B) a b c θ r =
      (1-t)*l40Lhs A (-(1/2)) A a b c θ r +
        t*l40Lhs B (-(1/2)) B a b c θ r := by
  unfold l40Lhs
  ring

/-- Complete Case2 assembly from per-child checks at the two A endpoints.
    Each child may use either f_A or q_c, as in the original JSON. -/
theorem case2_of_endpoint_branches (Alo Ahi A a b μ c κ θ : ℝ)
    (hlo0 : 0 ≤ Alo) (hlo : Alo ≤ A) (hhi : A ≤ Ahi)
    (hstatic : Case2Static a b μ c κ θ)
    (hiii : Da+1/4+1/10^18 ≤ Alo^2+(3999/1000)*(μ+θ*(μ+κ))^2)
    (hchildren : ∀ r : ℝ, -(1/2) ≤ r → r ≤ 1 →
      (fA Alo r+3/10^6 ≤ l40Lhs Alo (-(1/2)) Alo a b c θ r ∧
       fA Ahi r+3/10^6 ≤ l40Lhs Ahi (-(1/2)) Ahi a b c θ r) ∨
      (qc r+3/10^6 ≤ l40Lhs Alo (-(1/2)) Alo a b c θ r ∧
       qc r+3/10^6 ≤ l40Lhs Ahi (-(1/2)) Ahi a b c θ r)) :
    L40Case2 A a b μ c κ θ := by
  obtain ⟨t,ht0,ht1,he⟩ := exists_unit_interpolation Alo Ahi A hlo hhi
  have ht' : 0 ≤ 1-t := by linarith
  refine ⟨hstatic.1,hstatic.2,?_,?_⟩
  · nlinarith only [hiii,hlo,hlo0,sq_nonneg (A-Alo)]
  · intro r hrlo hrhi _
    have hr1 : r ≤ 1 := by linarith
    have hL := case2Lhs_chord Alo Ahi a b c θ r t
    rw [←he] at hL
    rcases hchildren r hrlo hr1 with h | h
    · have hfa := fA_le_chord Alo Ahi r t ht0 ht1
      rw [←he] at hfa
      have ha := mul_le_mul_of_nonneg_left h.1 ht'
      have hb := mul_le_mul_of_nonneg_left h.2 ht0
      have hh : fA A r+3/10^6 ≤ l40Lhs A (-(1/2)) A a b c θ r := by
        nlinarith only [ha,hb,hfa,hL]
      exact (add_le_add (min_le_right (qc r) (fA A r)) le_rfl).trans hh
    · have ha := mul_le_mul_of_nonneg_left h.1 ht'
      have hb := mul_le_mul_of_nonneg_left h.2 ht0
      have hh : qc r+3/10^6 ≤ l40Lhs A (-(1/2)) A a b c θ r := by
        nlinarith only [ha,hb,hL]
      exact (add_le_add (min_le_left (qc r) (fA A r)) le_rfl).trans hh

end GaussLocalMaxColoring.Certificate
end

section
-- Source module: Solutions.GaussLocalMaxCase1ConstructiveParameters

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace GaussLocalMaxColoring.Certificate
open GaussLocalMaxColoring.Main
noncomputable section

def constructedKappa (c : ℝ) : ℝ := Real.sqrt (1/4-c^2-1/10^20)
def constructedMass (L J : ℝ) : ℝ := Real.sqrt (J-L^2+1/10^18)
def constructedMu (L J c θ : ℝ) : ℝ :=
  (constructedMass L J-θ*constructedKappa c)/(1+θ)
def constructedA (b μ : ℝ) : ℝ := Real.sqrt (1-1/10^12-b^2-μ^2)

theorem constructedMu_nonneg (L J c θ : ℝ) (hθ : 0 < θ)
    (hM : θ*constructedKappa c ≤ constructedMass L J) :
    0 ≤ constructedMu L J c θ := by
  unfold constructedMu
  exact div_nonneg (sub_nonneg.mpr hM) (by linarith)

theorem constructedMu_mass (L J c θ : ℝ) (hθ : 0 < θ) :
    constructedMu L J c θ+θ*(constructedMu L J c θ+constructedKappa c) =
      constructedMass L J := by
  unfold constructedMu
  have hd : 1+θ ≠ 0 := ne_of_gt (by linarith)
  field_simp
  <;> ring

/-- A parameter family satisfying the original static conditions exactly.
    The remaining hypotheses are explicit inequalities on its free controls. -/
theorem constructed_static (L J b c θ : ℝ) (hc : 0 ≤ c)
    (hθ : 0 < θ) (hθ14 : θ < 14)
    (hk : 0 ≤ 1/4-c^2-1/10^20)
    (hM : θ*constructedKappa c ≤ constructedMass L J)
    (ha : 0 ≤ 1-1/10^12-b^2-(constructedMu L J c θ)^2) :
    Case2Static (constructedA b (constructedMu L J c θ)) b
      (constructedMu L J c θ) c (constructedKappa c) θ := by
  refine ⟨⟨Real.sqrt_nonneg _,constructedMu_nonneg L J c θ hθ hM,hc,
    Real.sqrt_nonneg _,hθ,hθ14⟩,?_,?_⟩
  · have hs := Real.sq_sqrt ha
    change (constructedA b (constructedMu L J c θ))^2+b^2+
      (constructedMu L J c θ)^2 ≤ 1-1/10^12
    unfold constructedA
    linarith only [hs]
  · have hs := Real.sq_sqrt hk
    change c^2+(constructedKappa c)^2 ≤ 1/4-1/10^20
    unfold constructedKappa
    linarith only [hs]

theorem constructed_iii_eq (L J c θ : ℝ) (hθ : 0 < θ)
    (hrad : 0 ≤ J-L^2+1/10^18) :
    L^2+(constructedMu L J c θ+
      θ*(constructedMu L J c θ+constructedKappa c))^2 = J+1/10^18 := by
  rw [constructedMu_mass L J c θ hθ]
  have hs := Real.sq_sqrt hrad
  unfold constructedMass
  linarith only [hs]

/-- Using an upper bound for capacity preserves the exact public margin. -/
theorem constructed_iii_of_upper (L J Jactual c θ : ℝ) (hθ : 0 < θ)
    (hrad : 0 ≤ J-L^2+1/10^18) (hJ : Jactual ≤ J) :
    Jactual+1/10^18 ≤ L^2+(constructedMu L J c θ+
      θ*(constructedMu L J c θ+constructedKappa c))^2 := by
  rw [constructed_iii_eq L J c θ hθ hrad]
  linarith only [hJ]


end
end GaussLocalMaxColoring.Certificate
end

section
-- Source module: Solutions.GaussLocalMaxCase1ConstructiveThinSyntax

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace GaussLocalMaxColoring.Certificate.ThinConstructiveSyntax
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate.CapacityCore
noncomputable section

def point (A ρ r : ℝ) : Fin 3 → ℝ := ![A,ρ,r]
def kappaQ (c : ℚ) : ℚ := 1/4-c*c-1/10^20
def normQ (b : ℚ) : ℚ := 1-1/10^12-b*b
def kappa (c : ℚ) : CertificateFormula 3 := .sqrt (.lit (kappaQ c))
def level (fj : ℕ) : CertificateFormula 3 :=
  .mul (sourceFAPattern (.var 0) (.var 1) fj)
    (.inv (.sqrt (.add (.lit 1) (.neg (.mul (.var 1) (.var 1))))))
def capacity (cj : ℕ) : CertificateFormula 3 :=
  .add (sourceCapacityPattern (.var 1) cj) (.lit (1/4))
def massRad (fj cj : ℕ) : CertificateFormula 3 :=
  .add (.add (capacity cj) (.neg (.mul (level fj) (level fj)))) (.lit (1/10^18))
def muNumer (fj cj : ℕ) (c θ : ℚ) : CertificateFormula 3 :=
  .add (.sqrt (massRad fj cj)) (.neg (.mul (kappa c) (.lit θ)))
def mu (fj cj : ℕ) (c θ : ℚ) : CertificateFormula 3 :=
  .mul (muNumer fj cj c θ) (.inv (.lit (1+θ)))
def aRad (fj cj : ℕ) (b c θ : ℚ) : CertificateFormula 3 :=
  .add (.lit (normQ b)) (.neg (.mul (mu fj cj c θ) (mu fj cj c θ)))
def a (fj cj : ℕ) (b c θ : ℚ) : CertificateFormula 3 := .sqrt (aRad fj cj b c θ)
def value (fj cj : ℕ) (b c θ σ : ℚ) : CertificateFormula 3 :=
  sourceValuePattern (.var 0) (.var 1) (.var 2) (.lit θ)
    (.mul (a fj cj b c θ) (.lit (1+θ))) (.lit ((1+θ)*b)) (.lit (θ*c)) (.lit σ) fj
def gap (fj cj fk : ℕ) (b c θ σ : ℚ) : CertificateFormula 3 :=
  .add (value fj cj b c θ σ) (.neg (sourceFAPattern (.var 0) (.var 2) fk))

theorem kappaQ_cast (c : ℚ) : (kappaQ c:ℝ) = 1/4-(c:ℝ)^2-1/10^20 := by
  norm_num [kappaQ,Rat.cast_sub,Rat.cast_mul,Rat.cast_div]
  <;> ring
theorem normQ_cast (b : ℚ) : (normQ b:ℝ) = 1-1/10^12-(b:ℝ)^2 := by
  norm_num [normQ,Rat.cast_sub,Rat.cast_mul,Rat.cast_div]
  <;> ring

theorem kappa_eval (c : ℚ) (A ρ r : ℝ) :
    (kappa c).eval (point A ρ r) = constructedKappa (c:ℝ) := by
  change Real.sqrt (kappaQ c:ℝ) = _
  rw [kappaQ_cast]
  rfl

theorem level_eval (fj : ℕ) (A ρ r : ℝ) (hf : sourceFADomain fj ρ) :
    (level fj).eval (point A ρ r) = fA A ρ/Real.sqrt (1-ρ^2) := by
  have h := sourceFAPattern_eval (.var 0 : CertificateFormula 3) (.var 1) fj (point A ρ r) hf
  change (sourceFAPattern (.var 0) (.var 1) fj).eval (point A ρ r) = fA A ρ at h
  change (sourceFAPattern (.var 0) (.var 1) fj).eval (point A ρ r)*
    (Real.sqrt (((1:ℚ):ℝ) + -(ρ*ρ)))⁻¹ = _
  rw [h]
  norm_num only [Rat.cast_one]
  simp only [pow_two,sub_eq_add_neg,div_eq_mul_inv]

theorem capacity_eval (cj : ℕ) (A ρ r : ℝ) :
    (capacity cj).eval (point A ρ r) = thresholdCapacity cj ρ+1/4 := by
  have h := sourceCapacityPattern_eval (.var 1 : CertificateFormula 3) cj (point A ρ r)
  change (sourceCapacityPattern (.var 1) cj).eval (point A ρ r) = thresholdCapacity cj ρ at h
  change (sourceCapacityPattern (.var 1) cj).eval (point A ρ r)+((1/4:ℚ):ℝ) = _
  rw [h]
  norm_num

theorem massRad_eval (fj cj : ℕ) (A ρ r : ℝ) (hf : sourceFADomain fj ρ) :
    (massRad fj cj).eval (point A ρ r) =
      thresholdCapacity cj ρ+1/4-(fA A ρ/Real.sqrt (1-ρ^2))^2+1/10^18 := by
  change (capacity cj).eval (point A ρ r) + -((level fj).eval (point A ρ r)*
    (level fj).eval (point A ρ r)) + ((1/10^18:ℚ):ℝ) = _
  rw [capacity_eval,level_eval fj A ρ r hf]
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  ring

theorem muNumer_eval (fj cj : ℕ) (c θ : ℚ) (A ρ r : ℝ) (hf : sourceFADomain fj ρ) :
    (muNumer fj cj c θ).eval (point A ρ r) =
      constructedMass (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity cj ρ+1/4)-
        (θ:ℝ)*constructedKappa (c:ℝ) := by
  change Real.sqrt ((massRad fj cj).eval (point A ρ r)) +
    -((kappa c).eval (point A ρ r)*(θ:ℝ)) = _
  rw [massRad_eval fj cj A ρ r hf,kappa_eval]
  unfold constructedMass
  ring

theorem mu_eval (fj cj : ℕ) (c θ : ℚ) (A ρ r : ℝ) (hf : sourceFADomain fj ρ) :
    (mu fj cj c θ).eval (point A ρ r) =
      constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity cj ρ+1/4) (c:ℝ) (θ:ℝ) := by
  change (muNumer fj cj c θ).eval (point A ρ r)*(((1+θ:ℚ):ℝ))⁻¹ = _
  rw [muNumer_eval fj cj c θ A ρ r hf]
  simp only [Rat.cast_add,Rat.cast_one,constructedMu,div_eq_mul_inv]

theorem aRad_eval (fj cj : ℕ) (b c θ : ℚ) (A ρ r : ℝ) (hf : sourceFADomain fj ρ) :
    (aRad fj cj b c θ).eval (point A ρ r) = 1-1/10^12-(b:ℝ)^2-
      (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity cj ρ+1/4) (c:ℝ) (θ:ℝ))^2 := by
  change (normQ b:ℝ) + -((mu fj cj c θ).eval (point A ρ r)*
    (mu fj cj c θ).eval (point A ρ r)) = _
  rw [normQ_cast,mu_eval fj cj c θ A ρ r hf]
  ring

theorem a_eval (fj cj : ℕ) (b c θ : ℚ) (A ρ r : ℝ) (hf : sourceFADomain fj ρ) :
    (a fj cj b c θ).eval (point A ρ r) =
      constructedA (b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2))
        (thresholdCapacity cj ρ+1/4) (c:ℝ) (θ:ℝ)) := by
  change Real.sqrt ((aRad fj cj b c θ).eval (point A ρ r)) = _
  rw [aRad_eval fj cj b c θ A ρ r hf]
  rfl


end
end GaussLocalMaxColoring.Certificate.ThinConstructiveSyntax
end

section
-- Source module: Solutions.GaussLocalMaxCertificateCanonical

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace GaussLocalMaxColoring.Certificate.CertificateFormula

def canonicalAdd {m : ℕ} (a b : CertificateFormula m) : CertificateFormula m :=
  match a,b with
  | .lit x,.lit y => .lit (x+y)
  | .lit x,b => if x=0 then b else .add b (.lit x)
  | a,.lit y => if y=0 then a else .add a (.lit y)
  | a,b => .add a b

def canonicalMul {m : ℕ} (a b : CertificateFormula m) : CertificateFormula m :=
  match a,b with
  | .lit x,.lit y => .lit (x*y)
  | .lit x,b => if x=0 then .lit 0 else if x=1 then b else .mul b (.lit x)
  | a,.lit y => if y=0 then .lit 0 else if y=1 then a else .mul a (.lit y)
  | a,b => .mul a b

def canonicalize {m : ℕ} : CertificateFormula m → CertificateFormula m
  | .lit q => .lit q
  | .var i => .var i
  | .add a b => canonicalAdd a.canonicalize b.canonicalize
  | .mul a b => canonicalMul a.canonicalize b.canonicalize
  | .neg a => smartNeg a.canonicalize
  | .inv a => smartInv a.canonicalize
  | .sqrt a => .sqrt a.canonicalize

theorem canonicalAdd_eval {m : ℕ} (a b : CertificateFormula m) (x : Fin m → ℝ) :
    (canonicalAdd a b).eval x = a.eval x+b.eval x := by
  cases a <;> cases b <;> simp only [canonicalAdd,eval]
  all_goals first | rfl | push_cast
  all_goals try rfl
  all_goals split <;> simp_all [eval,add_comm,mul_comm]

theorem canonicalMul_eval {m : ℕ} (a b : CertificateFormula m) (x : Fin m → ℝ) :
    (canonicalMul a b).eval x = a.eval x*b.eval x := by
  cases a <;> cases b <;> simp only [canonicalMul,eval]
  all_goals first | rfl | push_cast
  all_goals try rfl
  all_goals repeat' first | split | simp_all [eval,add_comm,mul_comm]

theorem canonicalize_eval {m : ℕ} (a : CertificateFormula m) (x : Fin m → ℝ) :
    a.canonicalize.eval x = a.eval x := by
  induction a with
  | lit q => rfl
  | var i => rfl
  | add a b ha hb => simpa only [canonicalize,canonicalAdd_eval,ha,hb,eval]
  | mul a b ha hb => simpa only [canonicalize,canonicalMul_eval,ha,hb,eval]
  | neg a ha => simpa only [canonicalize,smartNeg_eval,ha,eval]
  | inv a ha => simpa only [canonicalize,smartInv_eval,ha,eval]
  | sqrt a ha => simp only [canonicalize,eval,ha]

theorem eval_eq_of_canonicalize_eq {m : ℕ} (e f : CertificateFormula m)
    (h : e.canonicalize = f.canonicalize) (x : Fin m → ℝ) : e.eval x = f.eval x := by
  calc
    e.eval x = e.canonicalize.eval x := (canonicalize_eval e x).symm
    _ = f.canonicalize.eval x := congrArg (fun a => a.eval x) h
    _ = f.eval x := canonicalize_eval f x

theorem canonicalize_subst_eval {m n : ℕ} (s : Fin m → CertificateFormula n)
    (e : CertificateFormula m) (x : Fin n → ℝ) :
    (e.subst s).canonicalize.eval x = e.eval (fun i => (s i).eval x) := by
  rw [canonicalize_eval,subst_eval]

end GaussLocalMaxColoring.Certificate.CertificateFormula
end

section
-- Source module: Solutions.GaussLocalMaxCase1ConstructiveThinReflection

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace GaussLocalMaxColoring.Certificate.ThinConstructiveSyntax
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate.CapacityCore
noncomputable section

theorem signed_bridge (A ρ r a b c θ σ : ℝ) (hbase : 0 < 1-ρ^2) :
    case1ScaledLhs A ρ r θ ((1+θ)*a) ((1+θ)*b) (θ*c) σ =
      l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) a b c θ σ r := by
  rw [case1ScaledLhs_public_difference A ρ r a b c θ σ hbase]
  unfold l40Lhs l40SignedLhs
  ring

theorem value_eval (fj cj : ℕ) (b c θ σ : ℚ) (A ρ r : ℝ)
    (hf : sourceFADomain fj ρ) (hbase : 0 < 1-ρ^2) :
    (value fj cj b c θ σ).eval (point A ρ r) =
      l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2))
        (constructedA (b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2))
          (thresholdCapacity cj ρ+1/4) (c:ℝ) (θ:ℝ))) (b:ℝ) (c:ℝ) (θ:ℝ) (σ:ℝ) r-3/10^6 := by
  have h := sourceValuePattern_eval (.var 0 : CertificateFormula 3) (.var 1) (.var 2)
    (.lit θ) (.mul (a fj cj b c θ) (.lit (1+θ))) (.lit ((1+θ)*b))
    (.lit (θ*c)) (.lit σ) fj (point A ρ r) hf
  change (value fj cj b c θ σ).eval (point A ρ r) =
    case1ScaledLhs A ρ r (θ:ℝ) ((a fj cj b c θ).eval (point A ρ r)*((1+θ:ℚ):ℝ))
      (((1+θ)*b:ℚ):ℝ) ((θ*c:ℚ):ℝ) (σ:ℝ)-3/10^6 at h
  rw [a_eval fj cj b c θ A ρ r hf] at h
  simp only [Rat.cast_mul,Rat.cast_add,Rat.cast_one] at h
  rw [mul_comm (constructedA (b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2))
    (thresholdCapacity cj ρ+1/4) (c:ℝ) (θ:ℝ))) (1+(θ:ℝ))] at h
  rw [signed_bridge _ _ _ _ _ _ _ _ hbase] at h
  exact h

theorem gap_eval (fj cj fk : ℕ) (b c θ σ : ℚ) (A ρ r : ℝ)
    (hf : sourceFADomain fj ρ) (hk : sourceFADomain fk r) (hbase : 0 < 1-ρ^2) :
    (gap fj cj fk b c θ σ).eval (point A ρ r) =
      l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2))
        (constructedA (b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2))
          (thresholdCapacity cj ρ+1/4) (c:ℝ) (θ:ℝ))) (b:ℝ) (c:ℝ) (θ:ℝ) (σ:ℝ) r-
            3/10^6-fA A r := by
  have h := sourceFAPattern_eval (.var 0 : CertificateFormula 3) (.var 2) fk (point A ρ r) hk
  change (sourceFAPattern (.var 0) (.var 2) fk).eval (point A ρ r) = fA A r at h
  change (value fj cj b c θ σ).eval (point A ρ r) +
    -((sourceFAPattern (.var 0) (.var 2) fk).eval (point A ρ r)) = _
  rw [value_eval fj cj b c θ σ A ρ r hf hbase,h]
  rfl

theorem reflect_gap (n : BoxExpr 3) (fj cj fk : ℕ) (b c θ σ : ℚ)
    (hform : n.formula.canonicalize = (gap fj cj fk b c θ σ).canonicalize)
    (A ρ r : ℝ) (hf : sourceFADomain fj ρ) (hk : sourceFADomain fk r) (hbase : 0 < 1-ρ^2) :
    n.eval (point A ρ r) =
      l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2))
        (constructedA (b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2))
          (thresholdCapacity cj ρ+1/4) (c:ℝ) (θ:ℝ))) (b:ℝ) (c:ℝ) (θ:ℝ) (σ:ℝ) r-
            3/10^6-fA A r := by
  have h := CertificateFormula.eval_eq_of_canonicalize_eq _ _ hform (point A ρ r)
  rw [gap_eval fj cj fk b c θ σ A ρ r hf hk hbase] at h
  simpa only [BoxExpr.formula_eval] using h

theorem reflect_massRad (n : BoxExpr 3) (fj cj : ℕ)
    (hform : n.formula.canonicalize = (massRad fj cj).canonicalize)
    (A ρ r : ℝ) (hf : sourceFADomain fj ρ) :
    n.eval (point A ρ r) =
      thresholdCapacity cj ρ+1/4-(fA A ρ/Real.sqrt (1-ρ^2))^2+1/10^18 := by
  have h := CertificateFormula.eval_eq_of_canonicalize_eq _ _ hform (point A ρ r)
  rw [massRad_eval fj cj A ρ r hf] at h
  simpa only [BoxExpr.formula_eval] using h

theorem reflect_muNumer (n : BoxExpr 3) (fj cj : ℕ) (c θ : ℚ)
    (hform : n.formula.canonicalize = (muNumer fj cj c θ).canonicalize)
    (A ρ r : ℝ) (hf : sourceFADomain fj ρ) :
    n.eval (point A ρ r) =
      constructedMass (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity cj ρ+1/4)-
        (θ:ℝ)*constructedKappa (c:ℝ) := by
  have h := CertificateFormula.eval_eq_of_canonicalize_eq _ _ hform (point A ρ r)
  rw [muNumer_eval fj cj c θ A ρ r hf] at h
  simpa only [BoxExpr.formula_eval] using h

theorem reflect_aRad (n : BoxExpr 3) (fj cj : ℕ) (b c θ : ℚ)
    (hform : n.formula.canonicalize = (aRad fj cj b c θ).canonicalize)
    (A ρ r : ℝ) (hf : sourceFADomain fj ρ) :
    n.eval (point A ρ r) = 1-1/10^12-(b:ℝ)^2-
      (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity cj ρ+1/4) (c:ℝ) (θ:ℝ))^2 := by
  have h := CertificateFormula.eval_eq_of_canonicalize_eq _ _ hform (point A ρ r)
  rw [aRad_eval fj cj b c θ A ρ r hf] at h
  simpa only [BoxExpr.formula_eval] using h


end
end GaussLocalMaxColoring.Certificate.ThinConstructiveSyntax
end

section
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646BoundB4Part3
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part3
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate.CapacityCore
noncomputable section
namespace Parameters
def b : ℚ := (103531361122339324647880530522418473224550678173/6474633415922124204664207433178390079472570088576:ℚ)
def c : ℚ := (148022665013912365111/4722366482869645213696:ℚ)
def theta : ℚ := (105113898053531722649817636563532003778556764000751/182628568201966125342452015454275643968150995402752:ℚ)
end Parameters

theorem iv_shape8 : SplitDataB4Part3.node1534.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound8 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(149/640:ℝ)) ≤ r) (hrhi : r ≤ (-(4749/20480:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part3.node1534 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape8 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part3.positive_iv8 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part3.node1534.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape9 : SplitDataB4Part3.node1671.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound9 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(4749/20480:ℝ)) ≤ r) (hrhi : r ≤ (-(473/2048:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part3.node1671 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape9 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part3.positive_iv9 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part3.node1671.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape10 : SplitDataB4Part3.node1808.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound10 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(473/2048:ℝ)) ≤ r) (hrhi : r ≤ (-(4711/20480:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part3.node1808 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape10 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part3.positive_iv10 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part3.node1808.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape11 : SplitDataB4Part3.node1945.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound11 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(4711/20480:ℝ)) ≤ r) (hrhi : r ≤ (-(1173/5120:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part3.node1945 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape11 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part3.positive_iv11 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part3.node1945.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem actual_bound (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (r : ℝ)
    (hrlo : (-(149/640:ℝ)) ≤ r) (hrhi : r ≤ (-(1173/5120:ℝ))) : fA A r+3/10^6 ≤ l40Lhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) r := by
  have hc : 0 ≤ (Parameters.c:ℝ) := by norm_num [Parameters.c]
  have hθ : 0 ≤ (Parameters.theta:ℝ) := by norm_num [Parameters.theta]
  by_cases h0 : r ≤ (-(4749/20480:ℝ))
  · have h := iv_bound8 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  by_cases h1 : r ≤ (-(473/2048:ℝ))
  · have h := iv_bound9 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  by_cases h2 : r ≤ (-(4711/20480:ℝ))
  · have h := iv_bound10 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  have h := iv_bound11 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
  exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
    (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
end
end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part3
end

section
-- Source module: Solutions.Sol_GaussLocalMaxCase1FamilyAdaptive0Seed25646B4Part3
set_option autoImplicit false
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate
open GaussLocalMaxColoring.Certificate.CapacityCore
theorem solution (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (r : ℝ)
    (hrlo : (-(149/640:ℝ)) ≤ r) (hrhi : r ≤ (-(1173/5120:ℝ))) :
    let bv : ℝ := (103531361122339324647880530522418473224550678173/6474633415922124204664207433178390079472570088576:ℚ)
    let cv : ℝ := (148022665013912365111/4722366482869645213696:ℚ)
    let θv : ℝ := (105113898053531722649817636563532003778556764000751/182628568201966125342452015454275643968150995402752:ℚ)
    let Lv : ℝ := fA A ρ/Real.sqrt (1-ρ^2)
    let Jv : ℝ := Da+1+1/4
    let κv : ℝ := Real.sqrt (1/4-cv^2-1/10^20)
    let Mv : ℝ := Real.sqrt (Jv-Lv^2+1/10^18)
    let μv : ℝ := (Mv-θv*κv)/(1+θv)
    let av : ℝ := Real.sqrt (1-1/10^12-bv^2-μv^2)
    fA A r+3/10^6 ≤ l40Lhs A ρ Lv av bv cv θv r := by
  dsimp only
  have h := GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part3.actual_bound A ρ hAlo hAhi hρlo hρhi r hrlo hrhi
  simpa only [Case2Static,constructedA,constructedMu,constructedMass,constructedKappa,thresholdCapacity,
    GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part3.Parameters.b,GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part3.Parameters.c,GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part3.Parameters.theta,
    show ¬ (4:ℕ)=1 by decide,show ¬ (4:ℕ)=2 by decide,show ¬ (4:ℕ)=3 by decide,ite_false,and_assoc] using h
end

#print axioms solution
