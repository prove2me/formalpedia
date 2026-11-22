-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_40_adaptive0seed25646_b4_part_2
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T14:29:05.649351+00:00
-- url     : https://prove2.me/submissions/63ffa868-e326-47c3-b008-cf50abde62c4

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
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646DefsB4Part2
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part2

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
def node960 : BoxExpr 3 := .var 2
def node961 : BoxExpr 3 := .mul ⟨(-469591696835888785707/4722366482869645213696:ℚ),(-450980860506876288171/4722366482869645213696:ℚ)⟩ node13 node960
def node962 : BoxExpr 3 := .add ⟨(1891591544598933821141/4722366482869645213696:ℚ),(1910202380927946318677/4722366482869645213696:ℚ)⟩ node961 node301
def node963 : BoxExpr 3 := .mul ⟨(3968265190545251574935/4722366482869645213696:ℚ),(1008811092510452994625/1180591620717411303424:ℚ)⟩ node36 node962
def node964 : BoxExpr 3 := .mul ⟨(4713045482894524232303/4722366482869645213696:ℚ),(4810857922465551423031/4722366482869645213696:ℚ)⟩ node963 node304
def node965 : BoxExpr 3 := .add ⟨(-57724185662279462683/1180591620717411303424:ℚ),(-23300399492916301529/590295810358705651712:ℚ)⟩ node960 node306
def node966 : BoxExpr 3 := .mul ⟨(2014770399484735631/1180591620717411303424:ℚ),(9982745629926149707/4722366482869645213696:ℚ)⟩ node965 node308
def node967 : BoxExpr 3 := .mul ⟨(1097857663472984951/590295810358705651712:ℚ),(5449998149554544541/2361183241434822606848:ℚ)⟩ node966 node37
def node968 : BoxExpr 3 := .add ⟨(4721828344202308111911/4722366482869645213696:ℚ),(4821757918764660512113/4722366482869645213696:ℚ)⟩ node964 node967
def node969 : BoxExpr 3 := .add ⟨(7718136299670847235859/2361183241434822606848:ℚ),(15663521915624451009355/4722366482869645213696:ℚ)⟩ node968 node316
def node970 : BoxExpr 3 := .add ⟨(5337163183189936559677/2361183241434822606848:ℚ),(5457849439512853090045/2361183241434822606848:ℚ)⟩ node969 node323
def node971 : BoxExpr 3 := .add ⟨(5337156099640212255209/2361183241434822606848:ℚ),(10915684711926257571155/4722366482869645213696:ℚ)⟩ node970 node325
def node972 : BoxExpr 3 := .mul ⟨(15129/262144:ℚ),(289639822691093614429/4722366482869645213696:ℚ)⟩ node960 node960
def node973 : BoxExpr 3 := .neg ⟨(-289639822691093614429/4722366482869645213696:ℚ),(-15129/262144:ℚ)⟩ node972
def node974 : BoxExpr 3 := .add ⟨(4432726660178551599267/4722366482869645213696:ℚ),(247015/262144:ℚ)⟩ node12 node973
def node975 : BoxExpr 3 := .sqrt ⟨(571906895391279681677/590295810358705651712:ℚ),(4584071576256625559073/4722366482869645213696:ℚ)⟩ node974
def node976 : BoxExpr 3 := .mul ⟨(5663182727617472630965/2361183241434822606848:ℚ),(1420650520874766720729/590295810358705651712:ℚ)⟩ node11 node975
def node977 : BoxExpr 3 := .neg ⟨(123/512:ℚ),(1169523574273185572455/4722366482869645213696:ℚ)⟩ node960
def node978 : BoxExpr 3 := .add ⟨(1016415598461396294041/4722366482869645213696:ℚ),(1051464412201444442113/4722366482869645213696:ℚ)⟩ node332 node977
def node979 : BoxExpr 3 := .mul ⟨(725720737301436953945/4722366482869645213696:ℚ),(750745590311831331669/4722366482869645213696:ℚ)⟩ node978 node335
def node980 : BoxExpr 3 := .neg ⟨(-750745590311831331669/4722366482869645213696:ℚ),(-725720737301436953945/4722366482869645213696:ℚ)⟩ node979
def node981 : BoxExpr 3 := .add ⟨(10575619864923113930261/4722366482869645213696:ℚ),(10639483429696696811887/4722366482869645213696:ℚ)⟩ node976 node980
def node982 : BoxExpr 3 := .mul ⟨(218767576075089592975/4722366482869645213696:ℚ),(234115123029227864065/4722366482869645213696:ℚ)⟩ node978 node978
def node983 : BoxExpr 3 := .mul ⟨(180702017838024003797/4722366482869645213696:ℚ),(96689545811071107859/2361183241434822606848:ℚ)⟩ node982 node340
def node984 : BoxExpr 3 := .add ⟨(5378160941380568967029/2361183241434822606848:ℚ),(10832862521318839027605/4722366482869645213696:ℚ)⟩ node981 node983
def node985 : BoxExpr 3 := .neg ⟨(-10832862521318839027605/4722366482869645213696:ℚ),(-5378160941380568967029/2361183241434822606848:ℚ)⟩ node984
def node986 : BoxExpr 3 := .add ⟨(-158550322038414517187/4722366482869645213696:ℚ),(159362829165119637097/4722366482869645213696:ℚ)⟩ node971 node985
def node987 : BoxExpr 3 := .var 2
def node988 : BoxExpr 3 := .mul ⟨(-57531403732205311099/590295810358705651712:ℚ),(-230125614928821244395/2361183241434822606848:ℚ)⟩ node51 node987
def node989 : BoxExpr 3 := .add ⟨(237616501447147514757/590295810358705651712:ℚ),(950466005788590059029/2361183241434822606848:ℚ)⟩ node988 node301
def node990 : BoxExpr 3 := .mul ⟨(4001722723516267471491/4722366482869645213696:ℚ),(4001722723516267471505/4722366482869645213696:ℚ)⟩ node68 node989
def node991 : BoxExpr 3 := .mul ⟨(4761797889754398777863/4722366482869645213696:ℚ),(2380898944877199388941/2361183241434822606848:ℚ)⟩ node990 node349
def node992 : BoxExpr 3 := .add ⟨(-208649969296224131483/4722366482869645213696:ℚ),(-208649969296224131481/4722366482869645213696:ℚ)⟩ node987 node351
def node993 : BoxExpr 3 := .mul ⟨(9020913613932546115/4722366482869645213696:ℚ),(2255228403483136529/1180591620717411303424:ℚ)⟩ node992 node308
def node994 : BoxExpr 3 := .mul ⟨(153756162922607717/73786976294838206464:ℚ),(4920197213523446945/2361183241434822606848:ℚ)⟩ node993 node69
def node995 : BoxExpr 3 := .add ⟨(4771638284181445671751/4722366482869645213696:ℚ),(1192909571045361417943/1180591620717411303424:ℚ)⟩ node991 node994
def node996 : BoxExpr 3 := .add ⟨(15550640797097707623647/4722366482869645213696:ℚ),(15550640797097707623721/4722366482869645213696:ℚ)⟩ node995 node358
def node997 : BoxExpr 3 := .add ⟨(5397878081158712266415/2361183241434822606848:ℚ),(10795756162317424532909/4722366482869645213696:ℚ)⟩ node996 node361
def node998 : BoxExpr 3 := .add ⟨(5397870997608987961947/2361183241434822606848:ℚ),(5397870997608987961987/2361183241434822606848:ℚ)⟩ node997 node325
def node999 : BoxExpr 3 := .mul ⟨(281024796891904045219/4722366482869645213696:ℚ),(281024796891904045221/4722366482869645213696:ℚ)⟩ node987 node987
def node1000 : BoxExpr 3 := .neg ⟨(-281024796891904045221/4722366482869645213696:ℚ),(-281024796891904045219/4722366482869645213696:ℚ)⟩ node999
def node1001 : BoxExpr 3 := .add ⟨(4441341685977741168475/4722366482869645213696:ℚ),(4441341685977741168477/4722366482869645213696:ℚ)⟩ node12 node1000
def node1002 : BoxExpr 3 := .sqrt ⟨(572462377541543197193/590295810358705651712:ℚ),(2289849510166172788773/2361183241434822606848:ℚ)⟩ node1001
def node1003 : BoxExpr 3 := .mul ⟨(2836440889553259979743/1180591620717411303424:ℚ),(5672881779106519959493/2361183241434822606848:ℚ)⟩ node50 node1002
def node1004 : BoxExpr 3 := .neg ⟨(1151999167403161498419/4722366482869645213696:ℚ),(287999791850790374605/1180591620717411303424:ℚ)⟩ node987
def node1005 : BoxExpr 3 := .add ⟨(258485001332855092019/1180591620717411303424:ℚ),(516970002665710184039/2361183241434822606848:ℚ)⟩ node332 node1004
def node1006 : BoxExpr 3 := .mul ⟨(369116581903317071403/2361183241434822606848:ℚ),(92279145475829267851/590295810358705651712:ℚ)⟩ node1005 node335
def node1007 : BoxExpr 3 := .neg ⟨(-92279145475829267851/590295810358705651712:ℚ),(-369116581903317071403/2361183241434822606848:ℚ)⟩ node1006
def node1008 : BoxExpr 3 := .add ⟨(2651882598601601444041/1180591620717411303424:ℚ),(2651882598601601444045/1180591620717411303424:ℚ)⟩ node1003 node1007
def node1009 : BoxExpr 3 := .mul ⟨(226376317573539498557/4722366482869645213696:ℚ),(113188158786769749279/2361183241434822606848:ℚ)⟩ node1005 node1005
def node1010 : BoxExpr 3 := .mul ⟨(11686677394733976613/295147905179352825856:ℚ),(186986838315743625809/4722366482869645213696:ℚ)⟩ node1009 node340
def node1011 : BoxExpr 3 := .add ⟨(2698629308180537350493/1180591620717411303424:ℚ),(10794517232722149401989/4722366482869645213696:ℚ)⟩ node1008 node1010
def node1012 : BoxExpr 3 := .neg ⟨(-10794517232722149401989/4722366482869645213696:ℚ),(-2698629308180537350493/1180591620717411303424:ℚ)⟩ node1011
def node1013 : BoxExpr 3 := .add ⟨(1224762495826521905/4722366482869645213696:ℚ),(612381247913261001/2361183241434822606848:ℚ)⟩ node998 node1012
def node1014 : BoxExpr 3 := .mul ⟨(1077914823234660519303/4722366482869645213696:ℚ),(269478705808665129827/1180591620717411303424:ℚ)⟩ node78 node989
def node1015 : BoxExpr 3 := .mul ⟨(80165669969627000347/295147905179352825856:ℚ),(1282650719514032005559/4722366482869645213696:ℚ)⟩ node1014 node349
def node1016 : BoxExpr 3 := .add ⟨(5161882056795402993145/4722366482869645213696:ℚ),(1290470514198850748393/1180591620717411303424:ℚ)⟩ node1015 node385
def node1017 : BoxExpr 3 := .add ⟨(2808015996282649144383/4722366482869645213696:ℚ),(702003999070662286203/1180591620717411303424:ℚ)⟩ node1016 node387
def node1018 : BoxExpr 3 := .mul ⟨(2832805646382741919913/4722366482869645213696:ℚ),(1416402823191370959961/2361183241434822606848:ℚ)⟩ node77 node1002
def node1019 : BoxExpr 3 := .neg ⟨(-1416402823191370959961/2361183241434822606848:ℚ),(-2832805646382741919913/4722366482869645213696:ℚ)⟩ node1018
def node1020 : BoxExpr 3 := .add ⟨(-24789650100092775539/4722366482869645213696:ℚ),(-24789650100092775101/4722366482869645213696:ℚ)⟩ node1017 node1019
def node1021 : BoxExpr 3 := .mul ⟨(-1813001641238948492467/4722366482869645213696:ℚ),(-226625205154868561557/590295810358705651712:ℚ)⟩ node98 node989
def node1022 : BoxExpr 3 := .mul ⟨(-1212558160311111474927/2361183241434822606848:ℚ),(-2425116320622222949845/4722366482869645213696:ℚ)⟩ node68 node987
def node1023 : BoxExpr 3 := .add ⟨(-4238117961861171442321/4722366482869645213696:ℚ),(-4238117961861171442301/4722366482869645213696:ℚ)⟩ node1021 node1022
def node1024 : BoxExpr 3 := .mul ⟨(-1260773331990620446535/1180591620717411303424:ℚ),(-5043093327962481786113/4722366482869645213696:ℚ)⟩ node1023 node349
def node1025 : BoxExpr 3 := .mul ⟨(2263798227376018902473/2361183241434822606848:ℚ),(4527596454752037804971/4722366482869645213696:ℚ)⟩ node990 node399
def node1026 : BoxExpr 3 := .add ⟨(-257748436605221990597/2361183241434822606848:ℚ),(-257748436605221990571/2361183241434822606848:ℚ)⟩ node1024 node1025
def node1027 : BoxExpr 3 := .mul ⟨(4678205160399738521/4722366482869645213696:ℚ),(2339102580199869261/2361183241434822606848:ℚ)⟩ node993 node103
def node1028 : BoxExpr 3 := .add ⟨(-26670105826341616253/1180591620717411303424:ℚ),(-106680423305366465009/4722366482869645213696:ℚ)⟩ node403 node1027
def node1029 : BoxExpr 3 := .add ⟨(-311088648257905223103/2361183241434822606848:ℚ),(-622177296515810446151/4722366482869645213696:ℚ)⟩ node1026 node1028
def node1030 : BoxExpr 3 := .add ⟨(-75065015472785403983/1180591620717411303424:ℚ),(-300260061891141615761/4722366482869645213696:ℚ)⟩ node1029 node409
def node1031 : BoxExpr 3 := .add ⟨(-287999791850790374605/590295810358705651712:ℚ),(-1151999167403161498419/2361183241434822606848:ℚ)⟩ node987 node987
def node1032 : BoxExpr 3 := .neg ⟨(1151999167403161498419/2361183241434822606848:ℚ),(287999791850790374605/590295810358705651712:ℚ)⟩ node1031
def node1033 : BoxExpr 3 := .mul ⟨(572462377541543197193/295147905179352825856:ℚ),(2289849510166172788773/1180591620717411303424:ℚ)⟩ node86 node1002
def node1034 : BoxExpr 3 := .inv ⟨(1217369585835374043269/2361183241434822606848:ℚ),(608684792917687021635/1180591620717411303424:ℚ)⟩ node1033
def node1035 : BoxExpr 3 := .mul ⟨(593943208089211789079/2361183241434822606848:ℚ),(1187886416178423578161/4722366482869645213696:ℚ)⟩ node1032 node1034
def node1036 : BoxExpr 3 := .mul ⟨(2942874270151359386899/4722366482869645213696:ℚ),(2942874270151359386909/4722366482869645213696:ℚ)⟩ node50 node1035
def node1037 : BoxExpr 3 := .add ⟨(6314643938920286069477/4722366482869645213696:ℚ),(394665246182517879343/295147905179352825856:ℚ)⟩ node1036 node335
def node1038 : BoxExpr 3 := .mul ⟨(-516970002665710184039/2361183241434822606848:ℚ),(-258485001332855092019/1180591620717411303424:ℚ)⟩ node422 node1005
def node1039 : BoxExpr 3 := .mul ⟨(-516970002665710184039/2361183241434822606848:ℚ),(-258485001332855092019/1180591620717411303424:ℚ)⟩ node1005 node422
def node1040 : BoxExpr 3 := .add ⟨(-516970002665710184039/1180591620717411303424:ℚ),(-258485001332855092019/590295810358705651712:ℚ)⟩ node1038 node1039
def node1041 : BoxExpr 3 := .mul ⟨(-1708068888807506448065/4722366482869645213696:ℚ),(-1708068888807506448061/4722366482869645213696:ℚ)⟩ node1040 node340
def node1042 : BoxExpr 3 := .add ⟨(1151643762528194905353/1180591620717411303424:ℚ),(4606575050112779621427/4722366482869645213696:ℚ)⟩ node1037 node1041
def node1043 : BoxExpr 3 := .neg ⟨(-4606575050112779621427/4722366482869645213696:ℚ),(-1151643762528194905353/1180591620717411303424:ℚ)⟩ node1042
def node1044 : BoxExpr 3 := .add ⟨(-25787337058286301957/1180591620717411303424:ℚ),(-51574674116572603897/2361183241434822606848:ℚ)⟩ node414 node1043
def node1045 : BoxExpr 3 := .mul ⟨(4261731903377294567621/2361183241434822606848:ℚ),(8623707409194072719181/4722366482869645213696:ℚ)⟩ node112 node962
def node1046 : BoxExpr 3 := .mul ⟨(10123182464909811418771/4722366482869645213696:ℚ),(10281268569148960723859/4722366482869645213696:ℚ)⟩ node1045 node304
def node1047 : BoxExpr 3 := .add ⟨(10724696691886297790747/2361183241434822606848:ℚ),(11151904545452444784535/1180591620717411303424:ℚ)⟩ node1046 node448
def node1048 : BoxExpr 3 := .mul ⟨(11255127701300384135403/2361183241434822606848:ℚ),(1409602009698912359415/295147905179352825856:ℚ)⟩ node111 node975
def node1049 : BoxExpr 3 := .neg ⟨(-1409602009698912359415/295147905179352825856:ℚ),(-11255127701300384135403/2361183241434822606848:ℚ)⟩ node1048
def node1050 : BoxExpr 3 := .add ⟨(-552119385705001084573/2361183241434822606848:ℚ),(11048681389604505433667/2361183241434822606848:ℚ)⟩ node1047 node1049
def node1051 : BoxExpr 3 := .mul ⟨(-265190779770641771757/2361183241434822606848:ℚ),(-123700708564744744883/1180591620717411303424:ℚ)⟩ node131 node962
def node1052 : BoxExpr 3 := .mul ⟨(-679641309837514855141/4722366482869645213696:ℚ),(-627349509755936345381/4722366482869645213696:ℚ)⟩ node118 node960
def node1053 : BoxExpr 3 := .add ⟨(-1210022869378798398655/4722366482869645213696:ℚ),(-1122152344014915324913/4722366482869645213696:ℚ)⟩ node1051 node1052
def node1054 : BoxExpr 3 := .mul ⟨(-90162570926515742777/295147905179352825856:ℚ),(-1332762500016363075927/4722366482869645213696:ℚ)⟩ node1053 node304
def node1055 : BoxExpr 3 := .mul ⟨(1046025058860666435693/4722366482869645213696:ℚ),(1110069499056847544567/4722366482869645213696:ℚ)⟩ node118 node962
def node1056 : BoxExpr 3 := .mul ⟨(293276491904462920245/1180591620717411303424:ℚ),(1267059403365243486067/4722366482869645213696:ℚ)⟩ node1055 node461
def node1057 : BoxExpr 3 := .add ⟨(-67373791801600050863/1180591620717411303424:ℚ),(-16425774162779897465/1180591620717411303424:ℚ)⟩ node1054 node1056
def node1058 : BoxExpr 3 := .add ⟨(-3026795892100871045411/4722366482869645213696:ℚ),(336967695980135045761/1180591620717411303424:ℚ)⟩ node1057 node476
def node1059 : BoxExpr 3 := .add ⟨(-1169523574273185572455/2361183241434822606848:ℚ),(-123/256:ℚ)⟩ node960 node960
def node1060 : BoxExpr 3 := .neg ⟨(123/256:ℚ),(1169523574273185572455/2361183241434822606848:ℚ)⟩ node1059
def node1061 : BoxExpr 3 := .mul ⟨(571906895391279681677/295147905179352825856:ℚ),(4584071576256625559073/2361183241434822606848:ℚ)⟩ node86 node975
def node1062 : BoxExpr 3 := .inv ⟨(608104193716078401391/1180591620717411303424:ℚ),(2437103986925310061401/4722366482869645213696:ℚ)⟩ node1061
def node1063 : BoxExpr 3 := .mul ⟨(1168700247298088177673/4722366482869645213696:ℚ),(1207128068523942639789/4722366482869645213696:ℚ)⟩ node1060 node1062
def node1064 : BoxExpr 3 := .mul ⟨(705657897026350333649/4722366482869645213696:ℚ),(382247463577233390511/2361183241434822606848:ℚ)⟩ node117 node1063
def node1065 : BoxExpr 3 := .neg ⟨(-382247463577233390511/2361183241434822606848:ℚ),(-705657897026350333649/4722366482869645213696:ℚ)⟩ node1064
def node1066 : BoxExpr 3 := .add ⟨(468435664951897194925/4722366482869645213696:ℚ),(608037249702910368077/4722366482869645213696:ℚ)⟩ node479 node1065
def node1067 : BoxExpr 3 := .add ⟨(-1513397946050435522705/2361183241434822606848:ℚ),(336967695980135045761/1180591620717411303424:ℚ)⟩ node1057 node492
def node1068 : BoxExpr 3 := .mul ⟨(-1962571644527295092967/4722366482869645213696:ℚ),(-118727163566887936049/295147905179352825856:ℚ)⟩ node175 node962
def node1069 : BoxExpr 3 := .mul ⟨(66801195931741320403/295147905179352825856:ℚ),(564533428315568467091/2361183241434822606848:ℚ)⟩ node148 node960
def node1070 : BoxExpr 3 := .add ⟨(-893752509619433966519/4722366482869645213696:ℚ),(-385283880219535021301/2361183241434822606848:ℚ)⟩ node1068 node1069
def node1071 : BoxExpr 3 := .add ⟨(175066625288427159929/4722366482869645213696:ℚ),(89624774048016722895/1180591620717411303424:ℚ)⟩ node1070 node1069
def node1072 : BoxExpr 3 := .mul ⟨(207923847803084729349/4722366482869645213696:ℚ),(213703069622828580639/2361183241434822606848:ℚ)⟩ node1071 node304
def node1073 : BoxExpr 3 := .mul ⟨(-922061874256774060125/2361183241434822606848:ℚ),(-1782119187338414493251/4722366482869645213696:ℚ)⟩ node148 node962
def node1074 : BoxExpr 3 := .mul ⟨(-2470582942329116285279/4722366482869645213696:ℚ),(-2379951800181221156251/4722366482869645213696:ℚ)⟩ node36 node960
def node1075 : BoxExpr 3 := .add ⟨(-4314706690842664405529/4722366482869645213696:ℚ),(-2081035493759817824751/2361183241434822606848:ℚ)⟩ node1073 node1074
def node1076 : BoxExpr 3 := .mul ⟨(-4924907575642848591433/4722366482869645213696:ℚ),(-2333859151723620176911/2361183241434822606848:ℚ)⟩ node1075 node461
def node1077 : BoxExpr 3 := .add ⟨(-1179245931959940965521/1180591620717411303424:ℚ),(-132509755131299474767/147573952589676412928:ℚ)⟩ node1072 node1076
def node1078 : BoxExpr 3 := .mul ⟨(76437390004237785325/18446744073709551616:ℚ),(10162072811969377411841/2361183241434822606848:ℚ)⟩ node963 node514
def node1079 : BoxExpr 3 := .add ⟨(14643064265442024451767/4722366482869645213696:ℚ),(3914106830122878617465/1180591620717411303424:ℚ)⟩ node1076 node1078
def node1080 : BoxExpr 3 := .add ⟨(9926080537602260589683/4722366482869645213696:ℚ),(2854028789072482819329/1180591620717411303424:ℚ)⟩ node1077 node1079
def node1081 : BoxExpr 3 := .mul ⟨(16297173517429091279/4722366482869645213696:ℚ),(20497938350457117031/4722366482869645213696:ℚ)⟩ node966 node189
def node1082 : BoxExpr 3 := .add ⟨(-37061172161671509225/4722366482869645213696:ℚ),(-32028333721173668903/4722366482869645213696:ℚ)⟩ node518 node1081
def node1083 : BoxExpr 3 := .add ⟨(-90419517840772109729/4722366482869645213696:ℚ),(-84554605792804454837/4722366482869645213696:ℚ)⟩ node518 node1082
def node1084 : BoxExpr 3 := .add ⟨(4917830509880744239977/2361183241434822606848:ℚ),(11331560550497126822479/4722366482869645213696:ℚ)⟩ node1080 node1083
def node1085 : BoxExpr 3 := .add ⟨(20939394298128059851477/4722366482869645213696:ℚ),(13962515794912286648511/2361183241434822606848:ℚ)⟩ node1084 node527
def node1086 : BoxExpr 3 := .mul ⟨(-2437103986925310061401/2361183241434822606848:ℚ),(-608104193716078401391/590295810358705651712:ℚ)⟩ node6 node1062
def node1087 : BoxExpr 3 := .mul ⟨(1168700247298088177673/2361183241434822606848:ℚ),(1207128068523942639789/2361183241434822606848:ℚ)⟩ node86 node1063
def node1088 : BoxExpr 3 := .mul ⟨(17730906640714206397067/4722366482869645213696:ℚ),(17799306591278769111047/4722366482869645213696:ℚ)⟩ node1061 node1061
def node1089 : BoxExpr 3 := .inv ⟨(626449830620296477389/2361183241434822606848:ℚ),(628866466064488348003/2361183241434822606848:ℚ)⟩ node1088
def node1090 : BoxExpr 3 := .mul ⟨(620139986696577186097/4722366482869645213696:ℚ),(643001652068821804719/4722366482869645213696:ℚ)⟩ node1087 node1089
def node1091 : BoxExpr 3 := .neg ⟨(-643001652068821804719/4722366482869645213696:ℚ),(-620139986696577186097/4722366482869645213696:ℚ)⟩ node1090
def node1092 : BoxExpr 3 := .mul ⟨(-318486755790338300151/4722366482869645213696:ℚ),(-148978942116560534941/2361183241434822606848:ℚ)⟩ node1060 node1091
def node1093 : BoxExpr 3 := .add ⟨(-5192694729640958422953/4722366482869645213696:ℚ),(-2581395716980874140505/2361183241434822606848:ℚ)⟩ node1086 node1092
def node1094 : BoxExpr 3 := .mul ⟨(-3218538083313341340265/1180591620717411303424:ℚ),(-12780852753620003333585/4722366482869645213696:ℚ)⟩ node11 node1093
def node1095 : BoxExpr 3 := .add ⟨(-5072802903552711468035/4722366482869645213696:ℚ),(-4979503323919349440559/4722366482869645213696:ℚ)⟩ node1094 node546
def node1096 : BoxExpr 3 := .neg ⟨(4979503323919349440559/4722366482869645213696:ℚ),(5072802903552711468035/4722366482869645213696:ℚ)⟩ node1095
def cert_iv4 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-1249/5120:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/5120:ℚ)],
    whole := node986, centerValue := node1013, gradient := ![node1020, node1030, node1044],
    hessian := ![![node1050, node1058, node1066], ![node1067, node1085, node536], ![node1066, node536, node1096]] }
def node1097 : BoxExpr 3 := .var 2
def node1098 : BoxExpr 3 := .mul ⟨(-227759379774504418935/2361183241434822606848:ℚ),(-444014489490916410549/4722366482869645213696:ℚ)⟩ node13 node1097
def node1099 : BoxExpr 3 := .add ⟨(952832240942906884489/2361183241434822606848:ℚ),(1917168751943906196299/4722366482869645213696:ℚ)⟩ node1098 node301
def node1100 : BoxExpr 3 := .mul ⟨(3997788026658421367623/4722366482869645213696:ℚ),(4049960616708889561743/4722366482869645213696:ℚ)⟩ node36 node1099
def node1101 : BoxExpr 3 := .mul ⟨(4748109286018602144687/4722366482869645213696:ℚ),(4828402776103878628595/4722366482869645213696:ℚ)⟩ node1100 node304
def node1102 : BoxExpr 3 := .add ⟨(-195847928909069702661/4722366482869645213696:ℚ),(-42219697268326584549/1180591620717411303424:ℚ)⟩ node1097 node306
def node1103 : BoxExpr 3 := .mul ⟨(114084680658173213/73786976294838206464:ℚ),(8467421558294435923/4722366482869645213696:ℚ)⟩ node1102 node308
def node1104 : BoxExpr 3 := .mul ⟨(1989288561753342891/1180591620717411303424:ℚ),(9245438787073316013/4722366482869645213696:ℚ)⟩ node1103 node37
def node1105 : BoxExpr 3 := .add ⟨(4756066440265615516251/4722366482869645213696:ℚ),(151176506715342248269/147573952589676412928:ℚ)⟩ node1101 node1104
def node1106 : BoxExpr 3 := .add ⟨(7735255347702500938029/2361183241434822606848:ℚ),(7839706105875371220925/2361183241434822606848:ℚ)⟩ node1105 node316
def node1107 : BoxExpr 3 := .add ⟨(5354282231221590261847/2361183241434822606848:ℚ),(10931589175151997612585/4722366482869645213696:ℚ)⟩ node1106 node323
def node1108 : BoxExpr 3 := .add ⟨(5354275147671865957379/2361183241434822606848:ℚ),(5465787504026274501825/2361183241434822606848:ℚ)⟩ node1107 node325
def node1109 : BoxExpr 3 := .mul ⟨(16511558572827517911/295147905179352825856:ℚ),(15129/262144:ℚ)⟩ node1097 node1097
def node1110 : BoxExpr 3 := .neg ⟨(-15129/262144:ℚ),(-16511558572827517911/295147905179352825856:ℚ)⟩ node1109
def node1111 : BoxExpr 3 := .add ⟨(247015/262144:ℚ),(278636346606525307945/295147905179352825856:ℚ)⟩ node12 node1110
def node1112 : BoxExpr 3 := .sqrt ⟨(143252236758019548721/147573952589676412928:ℚ),(4588373034745809456133/4722366482869645213696:ℚ)⟩ node1111
def node1113 : BoxExpr 3 := .mul ⟨(11348191105065037513391/4722366482869645213696:ℚ),(5687934346873689366519/2361183241434822606848:ℚ)⟩ node11 node1112
def node1114 : BoxExpr 3 := .neg ⟨(279237588415778337587/1180591620717411303424:ℚ),(123/512:ℚ)⟩ node1097
def node1115 : BoxExpr 3 := .add ⟨(998891191591372220005/4722366482869645213696:ℚ),(508207799230698147021/2361183241434822606848:ℚ)⟩ node332 node1114
def node1116 : BoxExpr 3 := .mul ⟨(713208310796239765083/4722366482869645213696:ℚ),(725720737301436953947/4722366482869645213696:ℚ)⟩ node1115 node335
def node1117 : BoxExpr 3 := .neg ⟨(-725720737301436953947/4722366482869645213696:ℚ),(-713208310796239765083/4722366482869645213696:ℚ)⟩ node1116
def node1118 : BoxExpr 3 := .add ⟨(2655617591940900139861/1180591620717411303424:ℚ),(10662660382951138967955/4722366482869645213696:ℚ)⟩ node1113 node1117
def node1119 : BoxExpr 3 := .mul ⟨(211288898533878147317/4722366482869645213696:ℚ),(13672973504693099561/295147905179352825856:ℚ)⟩ node1115 node1115
def node1120 : BoxExpr 3 := .mul ⟨(174524630188983349683/4722366482869645213696:ℚ),(180702017838024003799/4722366482869645213696:ℚ)⟩ node1119 node340
def node1121 : BoxExpr 3 := .add ⟨(10796994997952583909127/4722366482869645213696:ℚ),(5421681200394581485877/2361183241434822606848:ℚ)⟩ node1118 node1120
def node1122 : BoxExpr 3 := .neg ⟨(-5421681200394581485877/2361183241434822606848:ℚ),(-10796994997952583909127/4722366482869645213696:ℚ)⟩ node1121
def node1123 : BoxExpr 3 := .add ⟨(-33703026361357764249/1180591620717411303424:ℚ),(134580010099965094523/4722366482869645213696:ℚ)⟩ node1108 node1122
def node1124 : BoxExpr 3 := .var 2
def node1125 : BoxExpr 3 := .mul ⟨(-449749100113092600137/4722366482869645213696:ℚ),(-449749100113092600135/4722366482869645213696:ℚ)⟩ node51 node1124
def node1126 : BoxExpr 3 := .add ⟨(1911434141321730006711/4722366482869645213696:ℚ),(1911434141321730006713/4722366482869645213696:ℚ)⟩ node1125 node301
def node1127 : BoxExpr 3 := .mul ⟨(502978893461690997567/590295810358705651712:ℚ),(2011915573846763990275/2361183241434822606848:ℚ)⟩ node68 node1126
def node1128 : BoxExpr 3 := .mul ⟨(2394052760729359374711/2361183241434822606848:ℚ),(2394052760729359374721/2361183241434822606848:ℚ)⟩ node1127 node349
def node1129 : BoxExpr 3 := .add ⟨(-91181679495594010215/2361183241434822606848:ℚ),(-45590839747797005107/1180591620717411303424:ℚ)⟩ node1124 node351
def node1130 : BoxExpr 3 := .mul ⟨(7884420560208760777/4722366482869645213696:ℚ),(3942210280104380389/2361183241434822606848:ℚ)⟩ node1129 node308
def node1131 : BoxExpr 3 := .mul ⟨(4300329848040178037/2361183241434822606848:ℚ),(8600659696080356077/4722366482869645213696:ℚ)⟩ node1130 node69
def node1132 : BoxExpr 3 := .add ⟨(599588272644349888187/590295810358705651712:ℚ),(4796706181154799105519/4722366482869645213696:ℚ)⟩ node1128 node1131
def node1133 : BoxExpr 3 := .add ⟨(973481793379441316087/295147905179352825856:ℚ),(3893927173517765264367/1180591620717411303424:ℚ)⟩ node1132 node358
def node1134 : BoxExpr 3 := .add ⟨(10820824059290777966575/4722366482869645213696:ℚ),(169075375926418405729/73786976294838206464:ℚ)⟩ node1133 node361
def node1135 : BoxExpr 3 := .add ⟨(10820809892191329357639/4722366482869645213696:ℚ),(10820809892191329357721/4722366482869645213696:ℚ)⟩ node1134 node325
def node1136 : BoxExpr 3 := .mul ⟨(268346128112941803765/4722366482869645213696:ℚ),(268346128112941803767/4722366482869645213696:ℚ)⟩ node1124 node1124
def node1137 : BoxExpr 3 := .neg ⟨(-268346128112941803767/4722366482869645213696:ℚ),(-268346128112941803765/4722366482869645213696:ℚ)⟩ node1136
def node1138 : BoxExpr 3 := .add ⟨(4454020354756703409929/4722366482869645213696:ℚ),(4454020354756703409931/4722366482869645213696:ℚ)⟩ node12 node1137
def node1139 : BoxExpr 3 := .sqrt ⟨(4586231180100085505401/4722366482869645213696:ℚ),(4586231180100085505403/4722366482869645213696:ℚ)⟩ node1138
def node1140 : BoxExpr 3 := .mul ⟨(5680973177680991207951/2361183241434822606848:ℚ),(11361946355361982415915/4722366482869645213696:ℚ)⟩ node50 node1139
def node1141 : BoxExpr 3 := .neg ⟨(562856278549062693683/2361183241434822606848:ℚ),(1125712557098125387367/4722366482869645213696:ℚ)⟩ node1124
def node1142 : BoxExpr 3 := .add ⟨(1007653395026384257023/4722366482869645213696:ℚ),(1007653395026384257025/4722366482869645213696:ℚ)⟩ node332 node1141
def node1143 : BoxExpr 3 := .mul ⟨(359732262024419179757/2361183241434822606848:ℚ),(179866131012209589879/1180591620717411303424:ℚ)⟩ node1142 node335
def node1144 : BoxExpr 3 := .neg ⟨(-179866131012209589879/1180591620717411303424:ℚ),(-359732262024419179757/2361183241434822606848:ℚ)⟩ node1143
def node1145 : BoxExpr 3 := .add ⟨(5321240915656572028193/2361183241434822606848:ℚ),(10642481831313144056401/4722366482869645213696:ℚ)⟩ node1140 node1144
def node1146 : BoxExpr 3 := .mul ⟨(215011979309829062655/4722366482869645213696:ℚ),(215011979309829062657/4722366482869645213696:ℚ)⟩ node1142 node1142
def node1147 : BoxExpr 3 := .mul ⟨(22199986863739850719/590295810358705651712:ℚ),(177599894909918805755/4722366482869645213696:ℚ)⟩ node1146 node340
def node1148 : BoxExpr 3 := .add ⟨(5410040863111531431069/2361183241434822606848:ℚ),(2705020431555765715539/1180591620717411303424:ℚ)⟩ node1145 node1147
def node1149 : BoxExpr 3 := .neg ⟨(-2705020431555765715539/1180591620717411303424:ℚ),(-5410040863111531431069/2361183241434822606848:ℚ)⟩ node1148
def node1150 : BoxExpr 3 := .add ⟨(728165968266495483/4722366482869645213696:ℚ),(728165968266495583/4722366482869645213696:ℚ)⟩ node1135 node1149
def node1151 : BoxExpr 3 := .mul ⟨(1083870007985214309323/4722366482869645213696:ℚ),(67741875499075894333/295147905179352825856:ℚ)⟩ node78 node1126
def node1152 : BoxExpr 3 := .mul ⟨(1289737014127009914665/4722366482869645213696:ℚ),(80608563382938119667/295147905179352825856:ℚ)⟩ node1151 node349
def node1153 : BoxExpr 3 := .add ⟨(2584484175704190451129/2361183241434822606848:ℚ),(5168968351408380902685/4722366482869645213696:ℚ)⟩ node1152 node385
def node1154 : BoxExpr 3 := .add ⟨(351887786361953381687/590295810358705651712:ℚ),(2815102290895627053925/4722366482869645213696:ℚ)⟩ node1153 node387
def node1155 : BoxExpr 3 := .mul ⟨(2836846160615440338733/4722366482869645213696:ℚ),(1418423080307720169371/2361183241434822606848:ℚ)⟩ node77 node1139
def node1156 : BoxExpr 3 := .neg ⟨(-1418423080307720169371/2361183241434822606848:ℚ),(-2836846160615440338733/4722366482869645213696:ℚ)⟩ node1155
def node1157 : BoxExpr 3 := .add ⟨(-10871934859906642623/2361183241434822606848:ℚ),(-2717983714976660601/590295810358705651712:ℚ)⟩ node1154 node1156
def node1158 : BoxExpr 3 := .mul ⟨(-911508989861565065961/2361183241434822606848:ℚ),(-1823017979723130131911/4722366482869645213696:ℚ)⟩ node98 node1126
def node1159 : BoxExpr 3 := .mul ⟨(-2369779398974718262847/4722366482869645213696:ℚ),(-2369779398974718262839/4722366482869645213696:ℚ)⟩ node68 node1124
def node1160 : BoxExpr 3 := .add ⟨(-4192797378697848394769/4722366482869645213696:ℚ),(-2096398689348924197375/2361183241434822606848:ℚ)⟩ node1158 node1159
def node1161 : BoxExpr 3 := .mul ⟨(-4989164689678437231941/4722366482869645213696:ℚ),(-1247291172419609307979/1180591620717411303424:ℚ)⟩ node1160 node349
def node1162 : BoxExpr 3 := .mul ⟨(4552610187546888704563/4722366482869645213696:ℚ),(4552610187546888704587/4722366482869645213696:ℚ)⟩ node1127 node399
def node1163 : BoxExpr 3 := .add ⟨(-218277251065774263689/2361183241434822606848:ℚ),(-436554502131548527329/4722366482869645213696:ℚ)⟩ node1161 node1162
def node1164 : BoxExpr 3 := .mul ⟨(2044412491355791243/2361183241434822606848:ℚ),(511103122838947811/590295810358705651712:ℚ)⟩ node1130 node103
def node1165 : BoxExpr 3 := .add ⟨(-107269803483054621047/4722366482869645213696:ℚ),(-107269803483054621043/4722366482869645213696:ℚ)⟩ node403 node1164
def node1166 : BoxExpr 3 := .add ⟨(-543824305614603148425/4722366482869645213696:ℚ),(-135956076403650787093/1180591620717411303424:ℚ)⟩ node1163 node1165
def node1167 : BoxExpr 3 := .add ⟨(-221907070989934318151/4722366482869645213696:ℚ),(-110953535494967158991/2361183241434822606848:ℚ)⟩ node1166 node409
def node1168 : BoxExpr 3 := .add ⟨(-1125712557098125387367/2361183241434822606848:ℚ),(-562856278549062693683/1180591620717411303424:ℚ)⟩ node1124 node1124
def node1169 : BoxExpr 3 := .neg ⟨(562856278549062693683/1180591620717411303424:ℚ),(1125712557098125387367/2361183241434822606848:ℚ)⟩ node1168
def node1170 : BoxExpr 3 := .mul ⟨(4586231180100085505401/2361183241434822606848:ℚ),(4586231180100085505403/2361183241434822606848:ℚ)⟩ node86 node1139
def node1171 : BoxExpr 3 := .inv ⟨(2431271377606825425265/4722366482869645213696:ℚ),(2431271377606825425267/4722366482869645213696:ℚ)⟩ node1170
def node1172 : BoxExpr 3 := .mul ⟨(579563811790845787409/2361183241434822606848:ℚ),(1159127623581691574821/4722366482869645213696:ℚ)⟩ node1169 node1171
def node1173 : BoxExpr 3 := .mul ⟨(358953391166218647699/590295810358705651712:ℚ),(1435813564664874590801/2361183241434822606848:ℚ)⟩ node50 node1172
def node1174 : BoxExpr 3 := .add ⟨(3121698399049337932085/2361183241434822606848:ℚ),(6243396798098675864181/4722366482869645213696:ℚ)⟩ node1173 node335
def node1175 : BoxExpr 3 := .mul ⟨(-1007653395026384257025/4722366482869645213696:ℚ),(-1007653395026384257023/4722366482869645213696:ℚ)⟩ node422 node1142
def node1176 : BoxExpr 3 := .mul ⟨(-1007653395026384257025/4722366482869645213696:ℚ),(-1007653395026384257023/4722366482869645213696:ℚ)⟩ node1142 node422
def node1177 : BoxExpr 3 := .add ⟨(-1007653395026384257025/2361183241434822606848:ℚ),(-1007653395026384257023/2361183241434822606848:ℚ)⟩ node1175 node1176
def node1178 : BoxExpr 3 := .mul ⟨(-832321704291793396303/2361183241434822606848:ℚ),(-1664643408583586792601/4722366482869645213696:ℚ)⟩ node1177 node340
def node1179 : BoxExpr 3 := .add ⟨(1144688347378772267891/1180591620717411303424:ℚ),(1144688347378772267895/1180591620717411303424:ℚ)⟩ node1174 node1178
def node1180 : BoxExpr 3 := .neg ⟨(-1144688347378772267895/1180591620717411303424:ℚ),(-1144688347378772267891/1180591620717411303424:ℚ)⟩ node1179
def node1181 : BoxExpr 3 := .add ⟨(-75327687635454657981/4722366482869645213696:ℚ),(-37663843817727328973/2361183241434822606848:ℚ)⟩ node414 node1180
def node1182 : BoxExpr 3 := .mul ⟨(8586876107344503692469/4722366482869645213696:ℚ),(2163789362829515435391/1180591620717411303424:ℚ)⟩ node112 node1099
def node1183 : BoxExpr 3 := .mul ⟨(10198496246248649214619/4722366482869645213696:ℚ),(10318763617884385925447/4722366482869645213696:ℚ)⟩ node1182 node304
def node1184 : BoxExpr 3 := .add ⟨(10762353582555716688671/2361183241434822606848:ℚ),(2790319576909075271233/295147905179352825856:ℚ)⟩ node1183 node448
def node1185 : BoxExpr 3 := .mul ⟨(22553632155182597750633/4722366482869645213696:ℚ),(1410924708184336407761/295147905179352825856:ℚ)⟩ node111 node1112
def node1186 : BoxExpr 3 := .neg ⟨(-1410924708184336407761/295147905179352825856:ℚ),(-22553632155182597750633/4722366482869645213696:ℚ)⟩ node1185
def node1187 : BoxExpr 3 := .add ⟨(-525044082918974573417/2361183241434822606848:ℚ),(22091481075362606589095/4722366482869645213696:ℚ)⟩ node1184 node1186
def node1188 : BoxExpr 3 := .mul ⟨(-532315823031203969159/4722366482869645213696:ℚ),(-124621008890121472749/1180591620717411303424:ℚ)⟩ node131 node1099
def node1189 : BoxExpr 3 := .mul ⟨(-164818377582835818577/1180591620717411303424:ℚ),(-38603671560693034261/295147905179352825856:ℚ)⟩ node118 node1097
def node1190 : BoxExpr 3 := .add ⟨(-1191589333362547243467/4722366482869645213696:ℚ),(-279035695132893609793/1180591620717411303424:ℚ)⟩ node1188 node1189
def node1191 : BoxExpr 3 := .mul ⟨(-1420624492358378854121/4722366482869645213696:ℚ),(-1325625037001842130813/4722366482869645213696:ℚ)⟩ node1190 node304
def node1192 : BoxExpr 3 := .mul ⟨(1053807206701135991793/4722366482869645213696:ℚ),(1114117842866456910517/4722366482869645213696:ℚ)⟩ node118 node1099
def node1193 : BoxExpr 3 := .mul ⟨(1181833563572849983291/4722366482869645213696:ℚ),(158960034761374553957/590295810358705651712:ℚ)⟩ node1192 node461
def node1194 : BoxExpr 3 := .add ⟨(-119395464392764435415/2361183241434822606848:ℚ),(-53944758910845699157/4722366482869645213696:ℚ)⟩ node1191 node1193
def node1195 : BoxExpr 3 := .add ⟨(-2996091653679999712789/4722366482869645213696:ℚ),(1359629121660814073747/4722366482869645213696:ℚ)⟩ node1194 node476
def node1196 : BoxExpr 3 := .add ⟨(-123/256:ℚ),(-279237588415778337587/590295810358705651712:ℚ)⟩ node1097 node1097
def node1197 : BoxExpr 3 := .neg ⟨(279237588415778337587/590295810358705651712:ℚ),(123/256:ℚ)⟩ node1196
def node1198 : BoxExpr 3 := .mul ⟨(143252236758019548721/73786976294838206464:ℚ),(4588373034745809456133/2361183241434822606848:ℚ)⟩ node86 node1112
def node1199 : BoxExpr 3 := .inv ⟨(2430136459008073932453/4722366482869645213696:ℚ),(1216208387432156802783/2361183241434822606848:ℚ)⟩ node1198
def node1200 : BoxExpr 3 := .mul ⟨(1149568457757334973515/4722366482869645213696:ℚ),(1168700247298088177675/4722366482869645213696:ℚ)⟩ node1197 node1199
def node1201 : BoxExpr 3 := .mul ⟨(347053088362169654277/2361183241434822606848:ℚ),(740157928326589896659/4722366482869645213696:ℚ)⟩ node117 node1200
def node1202 : BoxExpr 3 := .neg ⟨(-740157928326589896659/4722366482869645213696:ℚ),(-347053088362169654277/2361183241434822606848:ℚ)⟩ node1201
def node1203 : BoxExpr 3 := .add ⟨(61596582972471759911/590295810358705651712:ℚ),(154897242501230348293/1180591620717411303424:ℚ)⟩ node479 node1202
def node1204 : BoxExpr 3 := .add ⟨(-749022913419999928197/1180591620717411303424:ℚ),(1359629121660814073747/4722366482869645213696:ℚ)⟩ node1194 node492
def node1205 : BoxExpr 3 := .mul ⟨(-1969729002489825752437/4722366482869645213696:ℚ),(-1913767392674087890475/4722366482869645213696:ℚ)⟩ node175 node1099
def node1206 : BoxExpr 3 := .mul ⟨(526154460314398302491/2361183241434822606848:ℚ),(273807617045800163455/1180591620717411303424:ℚ)⟩ node148 node1097
def node1207 : BoxExpr 3 := .add ⟨(-917420081861029147455/4722366482869645213696:ℚ),(-818536924490887236655/4722366482869645213696:ℚ)⟩ node1205 node1206
def node1208 : BoxExpr 3 := .add ⟨(134888838767767457527/4722366482869645213696:ℚ),(276693543692313417165/4722366482869645213696:ℚ)⟩ node1207 node1206
def node1209 : BoxExpr 3 := .mul ⟨(80102664731431669977/2361183241434822606848:ℚ),(82469189267058032387/1180591620717411303424:ℚ)⟩ node1208 node304
def node1210 : BoxExpr 3 := .mul ⟨(-1850849135498589603647/4722366482869645213696:ℚ),(-1795377679444053767037/4722366482869645213696:ℚ)⟩ node148 node1099
def node1211 : BoxExpr 3 := .mul ⟨(-1198271695214831636787/2361183241434822606848:ℚ),(-2343188317088990910747/4722366482869645213696:ℚ)⟩ node36 node1097
def node1212 : BoxExpr 3 := .add ⟨(-4247392525928252877221/4722366482869645213696:ℚ),(-517320749566630584723/590295810358705651712:ℚ)⟩ node1210 node1211
def node1213 : BoxExpr 3 := .mul ⟨(-4848073606502222690023/4722366482869645213696:ℚ),(-4641357706287926410405/4722366482869645213696:ℚ)⟩ node1212 node461
def node1214 : BoxExpr 3 := .add ⟨(-4687868277039359350069/4722366482869645213696:ℚ),(-4311480949219694280857/4722366482869645213696:ℚ)⟩ node1209 node1213
def node1215 : BoxExpr 3 := .mul ⟨(19713552339865019359297/4722366482869645213696:ℚ),(20398266324662609378263/4722366482869645213696:ℚ)⟩ node1100 node514
def node1216 : BoxExpr 3 := .add ⟨(7432739366681398334637/2361183241434822606848:ℚ),(7878454309187341483929/2361183241434822606848:ℚ)⟩ node1213 node1215
def node1217 : BoxExpr 3 := .add ⟨(10177610456323437319205/4722366482869645213696:ℚ),(11445427669154988687001/4722366482869645213696:ℚ)⟩ node1214 node1216
def node1218 : BoxExpr 3 := .mul ⟨(14765020068527736201/4722366482869645213696:ℚ),(17386467763832511581/4722366482869645213696:ℚ)⟩ node1103 node189
def node1219 : BoxExpr 3 := .add ⟨(-38593325610572864303/4722366482869645213696:ℚ),(-35139804307798274353/4722366482869645213696:ℚ)⟩ node518 node1218
def node1220 : BoxExpr 3 := .add ⟨(-91951671289673464807/4722366482869645213696:ℚ),(-87666076379429060287/4722366482869645213696:ℚ)⟩ node518 node1219
def node1221 : BoxExpr 3 := .add ⟨(5042829392516881927199/2361183241434822606848:ℚ),(5678880796387779813357/2361183241434822606848:ℚ)⟩ node1217 node1220
def node1222 : BoxExpr 3 := .add ⟨(21189392063400335225921/4722366482869645213696:ℚ),(27951232632103006101257/4722366482869645213696:ℚ)⟩ node1221 node527
def node1223 : BoxExpr 3 := .mul ⟨(-1216208387432156802783/1180591620717411303424:ℚ),(-2430136459008073932453/2361183241434822606848:ℚ)⟩ node6 node1199
def node1224 : BoxExpr 3 := .mul ⟨(1149568457757334973515/2361183241434822606848:ℚ),(1168700247298088177675/2361183241434822606848:ℚ)⟩ node86 node1200
def node1225 : BoxExpr 3 := .mul ⟨(8899653295639384555519/2361183241434822606848:ℚ),(17832726182817619708485/4722366482869645213696:ℚ)⟩ node1198 node1198
def node1226 : BoxExpr 3 := .inv ⟨(78159478288357829757/295147905179352825856:ℚ),(313224915310148238695/1180591620717411303424:ℚ)⟩ node1225
def node1227 : BoxExpr 3 := .mul ⟨(608845052520134794777/4722366482869645213696:ℚ),(155034996674144296525/1180591620717411303424:ℚ)⟩ node1224 node1226
def node1228 : BoxExpr 3 := .neg ⟨(-155034996674144296525/1180591620717411303424:ℚ),(-608845052520134794777/4722366482869645213696:ℚ)⟩ node1227
def node1229 : BoxExpr 3 := .mul ⟨(-74489471058280267471/1180591620717411303424:ℚ),(-288012249453860639247/4722366482869645213696:ℚ)⟩ node1197 node1228
def node1230 : BoxExpr 3 := .add ⟨(-645348929245218535127/590295810358705651712:ℚ),(-5148285167470008504153/4722366482869645213696:ℚ)⟩ node1223 node1229
def node1231 : BoxExpr 3 := .mul ⟨(-12800013643443058064249/4722366482869645213696:ℚ),(-12744941472212025468595/4722366482869645213696:ℚ)⟩ node11 node1230
def node1232 : BoxExpr 3 := .add ⟨(-624833026717800521403/590295810358705651712:ℚ),(-4943592042511371575569/4722366482869645213696:ℚ)⟩ node1231 node546
def node1233 : BoxExpr 3 := .neg ⟨(4943592042511371575569/4722366482869645213696:ℚ),(624833026717800521403/590295810358705651712:ℚ)⟩ node1232
def cert_iv5 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-2441/10240:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/10240:ℚ)],
    whole := node1123, centerValue := node1150, gradient := ![node1157, node1167, node1181],
    hessian := ![![node1187, node1195, node1203], ![node1204, node1222, node536], ![node1203, node536, node1233]] }
def node1234 : BoxExpr 3 := .var 2
def node1235 : BoxExpr 3 := .mul ⟨(-28030143181598053997/295147905179352825856:ℚ),(-220265651991468235869/2361183241434822606848:ℚ)⟩ node13 node1234
def node1236 : BoxExpr 3 := .add ⟨(119543809408078358931/295147905179352825856:ℚ),(960325968725943067555/2361183241434822606848:ℚ)⟩ node1235 node301
def node1237 : BoxExpr 3 := .mul ⟨(2006274722357503131983/2361183241434822606848:ℚ),(4057318740042428353365/4722366482869645213696:ℚ)⟩ node36 node1236
def node1238 : BoxExpr 3 := .mul ⟨(4765641187580641100877/4722366482869645213696:ℚ),(4837175202923042231377/4722366482869645213696:ℚ)⟩ node1237 node304
def node1239 : BoxExpr 3 := .add ⟨(-89161761019522814313/2361183241434822606848:ℚ),(-160116585638294301179/4722366482869645213696:ℚ)⟩ node1234 node306
def node1240 : BoxExpr 3 := .mul ⟨(6922588544215157187/4722366482869645213696:ℚ),(963719940309822379/590295810358705651712:ℚ)⟩ node1239 node308
def node1241 : BoxExpr 3 := .mul ⟨(3772150358314058771/2361183241434822606848:ℚ),(1052270003881928685/590295810358705651712:ℚ)⟩ node1240 node37
def node1242 : BoxExpr 3 := .add ⟨(4773185488297269218419/4722366482869645213696:ℚ),(4845593362954097660857/4722366482869645213696:ℚ)⟩ node1238 node1241
def node1243 : BoxExpr 3 := .add ⟨(7743814871718327789113/2361183241434822606848:ℚ),(15687357359813888158099/4722366482869645213696:ℚ)⟩ node1242 node316
def node1244 : BoxExpr 3 := .add ⟨(5362841755237417112931/2361183241434822606848:ℚ),(5469767161607571664417/2361183241434822606848:ℚ)⟩ node1243 node323
def node1245 : BoxExpr 3 := .add ⟨(5362834671687692808463/2361183241434822606848:ℚ),(10939520156115694719899/4722366482869645213696:ℚ)⟩ node1244 node325
def node1246 : BoxExpr 3 := .mul ⟨(16253516387928024023/295147905179352825856:ℚ),(264184937165240286577/4722366482869645213696:ℚ)⟩ node1234 node1234
def node1247 : BoxExpr 3 := .neg ⟨(-264184937165240286577/4722366482869645213696:ℚ),(-16253516387928024023/295147905179352825856:ℚ)⟩ node1246
def node1248 : BoxExpr 3 := .add ⟨(4458181545704404927119/4722366482869645213696:ℚ),(278894388791424801833/295147905179352825856:ℚ)⟩ node12 node1247
def node1249 : BoxExpr 3 := .sqrt ⟨(4588373034745809456131/4722366482869645213696:ℚ),(35863259101861695765/36893488147419103232:ℚ)⟩ node1248
def node1250 : BoxExpr 3 := .mul ⟨(11358839667626450385657/4722366482869645213696:ℚ),(11381135010830311555231/4722366482869645213696:ℚ)⟩ node11 node1249
def node1251 : BoxExpr 3 := .neg ⟨(1108188150228101313331/4722366482869645213696:ℚ),(1116950353663113350349/4722366482869645213696:ℚ)⟩ node1234
def node1252 : BoxExpr 3 := .add ⟨(247532247039090045747/1180591620717411303424:ℚ),(998891191591372220007/4722366482869645213696:ℚ)⟩ node332 node1251
def node1253 : BoxExpr 3 := .mul ⟨(706952097543641170653/4722366482869645213696:ℚ),(356604155398119882543/2361183241434822606848:ℚ)⟩ node1252 node335
def node1254 : BoxExpr 3 := .neg ⟨(-356604155398119882543/2361183241434822606848:ℚ),(-706952097543641170653/4722366482869645213696:ℚ)⟩ node1253
def node1255 : BoxExpr 3 := .add ⟨(10645631356830210620571/4722366482869645213696:ℚ),(5337091456643335192289/2361183241434822606848:ℚ)⟩ node1250 node1254
def node1256 : BoxExpr 3 := .mul ⟨(12974895859202302935/295147905179352825856:ℚ),(211288898533878147319/4722366482869645213696:ℚ)⟩ node1252 node1252
def node1257 : BoxExpr 3 := .mul ⟨(42869055918804408897/1180591620717411303424:ℚ),(87262315094491674843/2361183241434822606848:ℚ)⟩ node1256 node340
def node1258 : BoxExpr 3 := .add ⟨(10817107580505428256159/4722366482869645213696:ℚ),(1356088442934456716783/590295810358705651712:ℚ)⟩ node1255 node1257
def node1259 : BoxExpr 3 := .neg ⟨(-1356088442934456716783/590295810358705651712:ℚ),(-10817107580505428256159/4722366482869645213696:ℚ)⟩ node1258
def node1260 : BoxExpr 3 := .add ⟨(-61519100050134058669/2361183241434822606848:ℚ),(30603143902566615935/1180591620717411303424:ℚ)⟩ node1245 node1259
def node1261 : BoxExpr 3 := .var 2
def node1262 : BoxExpr 3 := .mul ⟨(-444498035240817655809/4722366482869645213696:ℚ),(-444498035240817655807/4722366482869645213696:ℚ)⟩ node51 node1261
def node1263 : BoxExpr 3 := .add ⟨(1916685206194004951039/4722366482869645213696:ℚ),(1916685206194004951041/4722366482869645213696:ℚ)⟩ node1262 node301
def node1264 : BoxExpr 3 := .mul ⟨(4034885359782158235059/4722366482869645213696:ℚ),(2017442679891079117537/2361183241434822606848:ℚ)⟩ node68 node1263
def node1265 : BoxExpr 3 := .mul ⟨(4801259337310878735203/4722366482869645213696:ℚ),(4801259337310878735223/4722366482869645213696:ℚ)⟩ node1264 node349
def node1266 : BoxExpr 3 := .add ⟨(-169220053838669964903/4722366482869645213696:ℚ),(-84610026919334982451/2361183241434822606848:ℚ)⟩ node1261 node351
def node1267 : BoxExpr 3 := .mul ⟨(7316174033346868109/4722366482869645213696:ℚ),(3658087016673434055/2361183241434822606848:ℚ)⟩ node1266 node308
def node1268 : BoxExpr 3 := .mul ⟨(7980792330597087169/4722366482869645213696:ℚ),(7980792330597087171/4722366482869645213696:ℚ)⟩ node1267 node69
def node1269 : BoxExpr 3 := .add ⟨(1202310032410368955593/1180591620717411303424:ℚ),(2404620064820737911197/2361183241434822606848:ℚ)⟩ node1265 node1268
def node1270 : BoxExpr 3 := .add ⟨(3897060660639434443567/1180591620717411303424:ℚ),(15588242642557737774343/4722366482869645213696:ℚ)⟩ node1269 node358
def node1271 : BoxExpr 3 := .add ⟨(10833358007777454683451/4722366482869645213696:ℚ),(10833358007777454683531/4722366482869645213696:ℚ)⟩ node1270 node361
def node1272 : BoxExpr 3 := .add ⟨(10833343840678006074515/4722366482869645213696:ℚ),(2708335960169501518649/1180591620717411303424:ℚ)⟩ node1271 node325
def node1273 : BoxExpr 3 := .mul ⟨(931225/16777216:ℚ),(931225/16777216:ℚ)⟩ node1261 node1261
def node1274 : BoxExpr 3 := .neg ⟨(-931225/16777216:ℚ),(-931225/16777216:ℚ)⟩ node1273
def node1275 : BoxExpr 3 := .add ⟨(15845991/16777216:ℚ),(15845991/16777216:ℚ)⟩ node12 node1274
def node1276 : BoxExpr 3 := .sqrt ⟨(2294718656946631816103/2361183241434822606848:ℚ),(4589437313893263632207/4722366482869645213696:ℚ)⟩ node1275
def node1277 : BoxExpr 3 := .mul ⟨(11369889243266165243821/4722366482869645213696:ℚ),(1421236155408270655479/590295810358705651712:ℚ)⟩ node50 node1276
def node1278 : BoxExpr 3 := .neg ⟨(965/4096:ℚ),(965/4096:ℚ)⟩ node1261
def node1279 : BoxExpr 3 := .add ⟨(994510089873866201497/4722366482869645213696:ℚ),(497255044936933100749/2361183241434822606848:ℚ)⟩ node332 node1278
def node1280 : BoxExpr 3 := .mul ⟨(177520051042485116967/1180591620717411303424:ℚ),(355040102084970233935/2361183241434822606848:ℚ)⟩ node1279 node335
def node1281 : BoxExpr 3 := .neg ⟨(-355040102084970233935/2361183241434822606848:ℚ),(-177520051042485116967/1180591620717411303424:ℚ)⟩ node1280
def node1282 : BoxExpr 3 := .add ⟨(10659809039096224775951/4722366482869645213696:ℚ),(2664952259774056193991/1180591620717411303424:ℚ)⟩ node1277 node1281
def node1283 : BoxExpr 3 := .mul ⟨(104719775820946897633/2361183241434822606848:ℚ),(209439551641893795267/4722366482869645213696:ℚ)⟩ node1279 node1279
def node1284 : BoxExpr 3 := .mul ⟨(172997069656204274889/4722366482869645213696:ℚ),(172997069656204274891/4722366482869645213696:ℚ)⟩ node1283 node340
def node1285 : BoxExpr 3 := .add ⟨(1354100763594053631355/590295810358705651712:ℚ),(10832806108752429050855/4722366482869645213696:ℚ)⟩ node1282 node1284
def node1286 : BoxExpr 3 := .neg ⟨(-10832806108752429050855/4722366482869645213696:ℚ),(-1354100763594053631355/590295810358705651712:ℚ)⟩ node1285
def node1287 : BoxExpr 3 := .add ⟨(134432981394255915/1180591620717411303424:ℚ),(134432981394255939/1180591620717411303424:ℚ)⟩ node1272 node1286
def node1288 : BoxExpr 3 := .mul ⟨(1086847600360491204333/4722366482869645213696:ℚ),(1086847600360491204339/4722366482869645213696:ℚ)⟩ node78 node1263
def node1289 : BoxExpr 3 := .mul ⟨(1293280161433498869221/4722366482869645213696:ℚ),(646640080716749434615/2361183241434822606848:ℚ)⟩ node1288 node349
def node1290 : BoxExpr 3 := .add ⟨(2586255749357434928407/2361183241434822606848:ℚ),(5172511498714869857243/4722366482869645213696:ℚ)⟩ node1289 node385
def node1291 : BoxExpr 3 := .add ⟨(704661359550529002013/1180591620717411303424:ℚ),(2818645438202116008483/4722366482869645213696:ℚ)⟩ node1290 node387
def node1292 : BoxExpr 3 := .mul ⟨(177426833602989279137/295147905179352825856:ℚ),(2838829337647828466201/4722366482869645213696:ℚ)⟩ node77 node1276
def node1293 : BoxExpr 3 := .neg ⟨(-2838829337647828466201/4722366482869645213696:ℚ),(-177426833602989279137/295147905179352825856:ℚ)⟩ node1292
def node1294 : BoxExpr 3 := .add ⟨(-20183899445712458149/4722366482869645213696:ℚ),(-20183899445712457709/4722366482869645213696:ℚ)⟩ node1291 node1293
def node1295 : BoxExpr 3 := .mul ⟨(-914013074482610475825/2361183241434822606848:ℚ),(-1828026148965220951639/4722366482869645213696:ℚ)⟩ node98 node1263
def node1296 : BoxExpr 3 := .mul ⟨(-2342110938150965919343/4722366482869645213696:ℚ),(-2342110938150965919337/4722366482869645213696:ℚ)⟩ node68 node1261
def node1297 : BoxExpr 3 := .add ⟨(-4170137087116186870993/4722366482869645213696:ℚ),(-65158391986190419859/73786976294838206464:ℚ)⟩ node1295 node1296
def node1298 : BoxExpr 3 := .mul ⟨(-2481100185268207477421/2361183241434822606848:ℚ),(-4962200370536414954819/4722366482869645213696:ℚ)⟩ node1297 node349
def node1299 : BoxExpr 3 := .mul ⟨(1141279263486078538593/1180591620717411303424:ℚ),(4565117053944314154397/4722366482869645213696:ℚ)⟩ node1264 node399
def node1300 : BoxExpr 3 := .add ⟨(-198541658296050400235/2361183241434822606848:ℚ),(-198541658296050400211/2361183241434822606848:ℚ)⟩ node1298 node1299
def node1301 : BoxExpr 3 := .mul ⟨(1897067446933752235/2361183241434822606848:ℚ),(3794134893867504471/4722366482869645213696:ℚ)⟩ node1267 node103
def node1302 : BoxExpr 3 := .add ⟨(-107564493571898699063/4722366482869645213696:ℚ),(-26891123392974674765/1180591620717411303424:ℚ)⟩ node403 node1301
def node1303 : BoxExpr 3 := .add ⟨(-504647810163999499533/4722366482869645213696:ℚ),(-252323905081999749741/2361183241434822606848:ℚ)⟩ node1300 node1302
def node1304 : BoxExpr 3 := .add ⟨(-182730575539330669259/4722366482869645213696:ℚ),(-45682643884832667273/1180591620717411303424:ℚ)⟩ node1303 node409
def node1305 : BoxExpr 3 := .add ⟨(-965/2048:ℚ),(-965/2048:ℚ)⟩ node1261 node1261
def node1306 : BoxExpr 3 := .neg ⟨(965/2048:ℚ),(965/2048:ℚ)⟩ node1305
def node1307 : BoxExpr 3 := .mul ⟨(2294718656946631816103/1180591620717411303424:ℚ),(4589437313893263632207/2361183241434822606848:ℚ)⟩ node86 node1276
def node1308 : BoxExpr 3 := .inv ⟨(607393229095351979741/1180591620717411303424:ℚ),(1214786458190703959483/2361183241434822606848:ℚ)⟩ node1307
def node1309 : BoxExpr 3 := .mul ⟨(1144793879056669258691/4722366482869645213696:ℚ),(1144793879056669258693/4722366482869645213696:ℚ)⟩ node1306 node1308
def node1310 : BoxExpr 3 := .mul ⟨(177257291049608286527/295147905179352825856:ℚ),(2836116656793732584439/4722366482869645213696:ℚ)⟩ node50 node1309
def node1311 : BoxExpr 3 := .add ⟨(3103943162781329633505/2361183241434822606848:ℚ),(3103943162781329633509/2361183241434822606848:ℚ)⟩ node1310 node335
def node1312 : BoxExpr 3 := .mul ⟨(-497255044936933100749/2361183241434822606848:ℚ),(-994510089873866201497/4722366482869645213696:ℚ)⟩ node422 node1279
def node1313 : BoxExpr 3 := .mul ⟨(-497255044936933100749/2361183241434822606848:ℚ),(-994510089873866201497/4722366482869645213696:ℚ)⟩ node1279 node422
def node1314 : BoxExpr 3 := .add ⟨(-497255044936933100749/1180591620717411303424:ℚ),(-994510089873866201497/2361183241434822606848:ℚ)⟩ node1312 node1313
def node1315 : BoxExpr 3 := .mul ⟨(-1642930668471626964875/4722366482869645213696:ℚ),(-205366333558953370609/590295810358705651712:ℚ)⟩ node1314 node340
def node1316 : BoxExpr 3 := .add ⟨(4564955657091032302135/4722366482869645213696:ℚ),(2282477828545516151073/2361183241434822606848:ℚ)⟩ node1311 node1315
def node1317 : BoxExpr 3 := .neg ⟨(-2282477828545516151073/2361183241434822606848:ℚ),(-4564955657091032302135/4722366482869645213696:ℚ)⟩ node1316
def node1318 : BoxExpr 3 := .add ⟨(-61529955211397888547/4722366482869645213696:ℚ),(-61529955211397888517/4722366482869645213696:ℚ)⟩ node414 node1317
def node1319 : BoxExpr 3 := .mul ⟨(8618582257639460971081/4722366482869645213696:ℚ),(8670882472380056252755/4722366482869645213696:ℚ)⟩ node112 node1236
def node1320 : BoxExpr 3 := .mul ⟨(10236153136918068112541/4722366482869645213696:ℚ),(10337511142252098526241/4722366482869645213696:ℚ)⟩ node1319 node304
def node1321 : BoxExpr 3 := .add ⟨(336911938371575816801/73786976294838206464:ℚ),(22331930377456458470261/2361183241434822606848:ℚ)⟩ node1320 node448
def node1322 : BoxExpr 3 := .mul ⟨(5643698832737345631041/1180591620717411303424:ℚ),(2823155756498552690621/590295810358705651712:ℚ)⟩ node111 node1249
def node1323 : BoxExpr 3 := .neg ⟨(-2823155756498552690621/590295810358705651712:ℚ),(-5643698832737345631041/1180591620717411303424:ℚ)⟩ node1322
def node1324 : BoxExpr 3 := .add ⟨(-127860249525946156213/590295810358705651712:ℚ),(11044532711981767208179/2361183241434822606848:ℚ)⟩ node1321 node1323
def node1325 : BoxExpr 3 := .mul ⟨(-266641477388082090991/2361183241434822606848:ℚ),(-62540579526404918341/590295810358705651712:ℚ)⟩ node131 node1236
def node1326 : BoxExpr 3 := .mul ⟨(-162272402644564370973/1180591620717411303424:ℚ),(-306406681289332324787/2361183241434822606848:ℚ)⟩ node118 node1234
def node1327 : BoxExpr 3 := .add ⟨(-591186282677210832937/2361183241434822606848:ℚ),(-556568999394951998151/2361183241434822606848:ℚ)⟩ node1325 node1326
def node1328 : BoxExpr 3 := .mul ⟨(-704818085562721169483/2361183241434822606848:ℚ),(-1322056305494581658257/4722366482869645213696:ℚ)⟩ node1327 node304
def node1329 : BoxExpr 3 := .mul ⟨(528849140310685384921/2361183241434822606848:ℚ),(279035503692815398373/1180591620717411303424:ℚ)⟩ node118 node1236
def node1330 : BoxExpr 3 := .mul ⟨(1186197361550349134445/4722366482869645213696:ℚ),(1273990715453872904451/4722366482869645213696:ℚ)⟩ node1329 node461
def node1331 : BoxExpr 3 := .add ⟨(-223438809575093204521/4722366482869645213696:ℚ),(-24032795020354376903/2361183241434822606848:ℚ)⟩ node1328 node1330
def node1332 : BoxExpr 3 := .add ⟨(-186296220904347752905/295147905179352825856:ℚ),(682754145265475509549/2361183241434822606848:ℚ)⟩ node1331 node476
def node1333 : BoxExpr 3 := .add ⟨(-1116950353663113350349/2361183241434822606848:ℚ),(-1108188150228101313331/2361183241434822606848:ℚ)⟩ node1234 node1234
def node1334 : BoxExpr 3 := .neg ⟨(1108188150228101313331/2361183241434822606848:ℚ),(1116950353663113350349/2361183241434822606848:ℚ)⟩ node1333
def node1335 : BoxExpr 3 := .mul ⟨(4588373034745809456131/2361183241434822606848:ℚ),(35863259101861695765/18446744073709551616:ℚ)⟩ node86 node1249
def node1336 : BoxExpr 3 := .inv ⟨(1214505989044902019709/2361183241434822606848:ℚ),(2430136459008073932455/4722366482869645213696:ℚ)⟩ node1335
def node1337 : BoxExpr 3 := .mul ⟨(1140022613935507638031/4722366482869645213696:ℚ),(574784228878667486759/2361183241434822606848:ℚ)⟩ node1334 node1336
def node1338 : BoxExpr 3 := .mul ⟨(688342423279240096845/4722366482869645213696:ℚ),(364020718798667918489/2361183241434822606848:ℚ)⟩ node117 node1337
def node1339 : BoxExpr 3 := .neg ⟨(-364020718798667918489/2361183241434822606848:ℚ),(-688342423279240096845/4722366482869645213696:ℚ)⟩ node1338
def node1340 : BoxExpr 3 := .add ⟨(504889154509028138969/4722366482869645213696:ℚ),(625352723450020604881/4722366482869645213696:ℚ)⟩ node479 node1339
def node1341 : BoxExpr 3 := .add ⟨(-2980739534469564046479/4722366482869645213696:ℚ),(682754145265475509549/2361183241434822606848:ℚ)⟩ node1331 node492
def node1342 : BoxExpr 3 := .mul ⟨(-493326920367772770543/1180591620717411303424:ℚ),(-240104222559503543415/590295810358705651712:ℚ)⟩ node175 node1236
def node1343 : BoxExpr 3 := .mul ⟨(522026906744632172125/2361183241434822606848:ℚ),(1078312273959232513639/4722366482869645213696:ℚ)⟩ node148 node1234
def node1344 : BoxExpr 3 := .add ⟨(-464626933990913368961/2361183241434822606848:ℚ),(-842521506516795833681/4722366482869645213696:ℚ)⟩ node1342 node1343
def node1345 : BoxExpr 3 := .add ⟨(14349993188429700791/590295810358705651712:ℚ),(117895383721218339979/2361183241434822606848:ℚ)⟩ node1344 node1343
def node1346 : BoxExpr 3 := .mul ⟨(68173035146376322629/2361183241434822606848:ℚ),(70278016494879903421/1180591620717411303424:ℚ)⟩ node1345 node304
def node1347 : BoxExpr 3 := .mul ⟨(-927105914495555172673/2361183241434822606848:ℚ),(-1802006925496873403929/4722366482869645213696:ℚ)⟩ node148 node1236
def node1348 : BoxExpr 3 := .mul ⟨(-1179761807239968383861/2361183241434822606848:ℚ),(-581201643885718946999/1180591620717411303424:ℚ)⟩ node36 node1234
def node1349 : BoxExpr 3 := .add ⟨(-1053433860867761778267/1180591620717411303424:ℚ),(-4126813501039749191925/4722366482869645213696:ℚ)⟩ node1347 node1348
def node1350 : BoxExpr 3 := .mul ⟨(-4809656621931909739319/4722366482869645213696:ℚ),(-578522175963533679837/590295810358705651712:ℚ)⟩ node1349 node461
def node1351 : BoxExpr 3 := .add ⟨(-4673310551639157094061/4722366482869645213696:ℚ),(-1086766335432187456253/1180591620717411303424:ℚ)⟩ node1346 node1350
def node1352 : BoxExpr 3 := .mul ⟨(19786342589255092517341/4722366482869645213696:ℚ),(20435326675024536655555/4722366482869645213696:ℚ)⟩ node1237 node514
def node1353 : BoxExpr 3 := .add ⟨(7488342983661591389011/2361183241434822606848:ℚ),(15807149267316267216859/4722366482869645213696:ℚ)⟩ node1350 node1352
def node1354 : BoxExpr 3 := .add ⟨(10303375415684025683961/4722366482869645213696:ℚ),(11460083925587517391847/4722366482869645213696:ℚ)⟩ node1351 node1353
def node1355 : BoxExpr 3 := .mul ⟨(1749867918009632333/590295810358705651712:ℚ),(15830732470520208859/4722366482869645213696:ℚ)⟩ node1240 node189
def node1356 : BoxExpr 3 := .add ⟨(-2459962645938971365/295147905179352825856:ℚ),(-36695539601110577075/4722366482869645213696:ℚ)⟩ node518 node1355
def node1357 : BoxExpr 3 := .add ⟨(-11589718501765517793/590295810358705651712:ℚ),(-89221811672741363009/4722366482869645213696:ℚ)⟩ node518 node1356
def node1358 : BoxExpr 3 := .add ⟨(10210657667669901541617/4722366482869645213696:ℚ),(5685431056957388014419/2361183241434822606848:ℚ)⟩ node1354 node1357
def node1359 : BoxExpr 3 := .add ⟨(5328597736509118228285/1180591620717411303424:ℚ),(27964333153242222503381/4722366482869645213696:ℚ)⟩ node1358 node527
def node1360 : BoxExpr 3 := .mul ⟨(-2430136459008073932455/2361183241434822606848:ℚ),(-1214505989044902019709/1180591620717411303424:ℚ)⟩ node6 node1336
def node1361 : BoxExpr 3 := .mul ⟨(1140022613935507638031/2361183241434822606848:ℚ),(574784228878667486759/1180591620717411303424:ℚ)⟩ node86 node1337
def node1362 : BoxExpr 3 := .mul ⟨(4458181545704404927117/1180591620717411303424:ℚ),(17849240882651187317313/4722366482869645213696:ℚ)⟩ node1335 node1335
def node1363 : BoxExpr 3 := .inv ⟨(39043581294902112701/147573952589676412928:ℚ),(625275826306862638057/2361183241434822606848:ℚ)⟩ node1362
def node1364 : BoxExpr 3 := .mul ⟨(603230649096696359453/4722366482869645213696:ℚ),(608845052520134794781/4722366482869645213696:ℚ)⟩ node1361 node1363
def node1365 : BoxExpr 3 := .neg ⟨(-608845052520134794781/4722366482869645213696:ℚ),(-603230649096696359453/4722366482869645213696:ℚ)⟩ node1364
def node1366 : BoxExpr 3 := .mul ⟨(-144006124726930319625/2361183241434822606848:ℚ),(-8847431944454109813/147573952589676412928:ℚ)⟩ node1334 node1365
def node1367 : BoxExpr 3 := .add ⟨(-160883911483437765755/147573952589676412928:ℚ),(-1285285444600534898213/1180591620717411303424:ℚ)⟩ node1360 node1366
def node1368 : BoxExpr 3 := .mul ⟨(-12764048524304552548447/4722366482869645213696:ℚ),(-12727257510927501526349/4722366482869645213696:ℚ)⟩ node11 node1367
def node1369 : BoxExpr 3 := .add ⟨(-2481349547301949327711/2361183241434822606848:ℚ),(-4925908081226847633323/4722366482869645213696:ℚ)⟩ node1368 node546
def node1370 : BoxExpr 3 := .neg ⟨(4925908081226847633323/4722366482869645213696:ℚ),(2481349547301949327711/2361183241434822606848:ℚ)⟩ node1369
def cert_iv6 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-965/4096:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/20480:ℚ)],
    whole := node1260, centerValue := node1287, gradient := ![node1294, node1304, node1318],
    hessian := ![![node1324, node1332, node1340], ![node1341, node1359, node536], ![node1340, node536, node1370]] }
def node1371 : BoxExpr 3 := .var 2
def node1372 : BoxExpr 3 := .mul ⟨(-444964056583848876993/4722366482869645213696:ℚ),(-437048118474956532927/4722366482869645213696:ℚ)⟩ node13 node1371
def node1373 : BoxExpr 3 := .add ⟨(1916219184850973729855/4722366482869645213696:ℚ),(1924135122959866073921/4722366482869645213696:ℚ)⟩ node1372 node301
def node1374 : BoxExpr 3 := .mul ⟨(2009965076871649356069/2361183241434822606848:ℚ),(2032338431687983572493/2361183241434822606848:ℚ)⟩ node36 node1373
def node1375 : BoxExpr 3 := .mul ⟨(4774407138361660578973/4722366482869645213696:ℚ),(2422973814871102917079/2361183241434822606848:ℚ)⟩ node1374 node304
def node1376 : BoxExpr 3 := .add ⟨(-169561318604033591609/4722366482869645213696:ℚ),(-151354382203282264161/4722366482869645213696:ℚ)⟩ node1371 node306
def node1377 : BoxExpr 3 := .mul ⟨(6543757526307228741/4722366482869645213696:ℚ),(3665464252285325293/2361183241434822606848:ℚ)⟩ node1376 node308
def node1378 : BoxExpr 3 := .mul ⟨(222857724570089485/147573952589676412928:ℚ),(8004520653046486213/4722366482869645213696:ℚ)⟩ node1377 node37
def node1379 : BoxExpr 3 := .add ⟨(4781538585547903442493/4722366482869645213696:ℚ),(4853952150395252320371/4722366482869645213696:ℚ)⟩ node1375 node1378
def node1380 : BoxExpr 3 := .add ⟨(3873995710171822450575/1180591620717411303424:ℚ),(15695716147255042817613/4722366482869645213696:ℚ)⟩ node1379 node316
def node1381 : BoxExpr 3 := .add ⟨(670877287982841778121/295147905179352825856:ℚ),(2736973277664074497087/1180591620717411303424:ℚ)⟩ node1380 node323
def node1382 : BoxExpr 3 := .add ⟨(1341752805078252480125/590295810358705651712:ℚ),(10947878943556849379413/4722366482869645213696:ℚ)⟩ node1381 node325
def node1383 : BoxExpr 3 := .mul ⟨(255960103237766097141/4722366482869645213696:ℚ),(130028131103424192185/2361183241434822606848:ℚ)⟩ node1371 node1371
def node1384 : BoxExpr 3 := .neg ⟨(-130028131103424192185/2361183241434822606848:ℚ),(-255960103237766097141/4722366482869645213696:ℚ)⟩ node1383
def node1385 : BoxExpr 3 := .add ⟨(2231155110331398414663/2361183241434822606848:ℚ),(4466406379631879116555/4722366482869645213696:ℚ)⟩ node12 node1384
def node1386 : BoxExpr 3 := .sqrt ⟨(2295248582519148528959/2361183241434822606848:ℚ),(4592603595570680468651/4722366482869645213696:ℚ)⟩ node1385
def node1387 : BoxExpr 3 := .mul ⟨(11364098101333301727061/4722366482869645213696:ℚ),(11386357445224253886389/4722366482869645213696:ℚ)⟩ node11 node1386
def node1388 : BoxExpr 3 := .neg ⟨(1099425946793089276313/4722366482869645213696:ℚ),(277047037557025328333/1180591620717411303424:ℚ)⟩ node1371
def node1389 : BoxExpr 3 := .add ⟨(490683392360674072985/2361183241434822606848:ℚ),(495064494078180091495/2361183241434822606848:ℚ)⟩ node332 node1388
def node1390 : BoxExpr 3 := .mul ⟨(350347942145521288111/2361183241434822606848:ℚ),(706952097543641170655/4722366482869645213696:ℚ)⟩ node1389 node335
def node1391 : BoxExpr 3 := .neg ⟨(-706952097543641170655/4722366482869645213696:ℚ),(-350347942145521288111/2361183241434822606848:ℚ)⟩ node1390
def node1392 : BoxExpr 3 := .add ⟨(5328573001894830278203/2361183241434822606848:ℚ),(10685661560933211310167/4722366482869645213696:ℚ)⟩ node1387 node1391
def node1393 : BoxExpr 3 := .mul ⟨(12746267809369072599/295147905179352825856:ℚ),(103799166873618423481/2361183241434822606848:ℚ)⟩ node1389 node1389
def node1394 : BoxExpr 3 := .mul ⟨(42113668842155415867/1180591620717411303424:ℚ),(171476223675217635591/4722366482869645213696:ℚ)⟩ node1393 node340
def node1395 : BoxExpr 3 := .add ⟨(5412800339579141109937/2361183241434822606848:ℚ),(5428568892304214472879/2361183241434822606848:ℚ)⟩ node1392 node1394
def node1396 : BoxExpr 3 := .neg ⟨(-5428568892304214472879/2361183241434822606848:ℚ),(-5412800339579141109937/2361183241434822606848:ℚ)⟩ node1395
def node1397 : BoxExpr 3 := .add ⟨(-61557671991204552379/2361183241434822606848:ℚ),(122278264398567159539/4722366482869645213696:ℚ)⟩ node1382 node1396
def node1398 : BoxExpr 3 := .var 2
def node1399 : BoxExpr 3 := .mul ⟨(-110249331331491923231/1180591620717411303424:ℚ),(-220498662662983846461/2361183241434822606848:ℚ)⟩ node51 node1398
def node1400 : BoxExpr 3 := .add ⟨(480046479027213728481/1180591620717411303424:ℚ),(960092958054427456963/2361183241434822606848:ℚ)⟩ node1399 node301
def node1401 : BoxExpr 3 := .mul ⟨(2021127417253955869037/2361183241434822606848:ℚ),(4042254834507911738089/4722366482869645213696:ℚ)⟩ node68 node1400
def node1402 : BoxExpr 3 := .mul ⟨(4810028547878985392389/4722366482869645213696:ℚ),(2405014273939492696205/2361183241434822606848:ℚ)⟩ node1401 node349
def node1403 : BoxExpr 3 := .add ⟨(-80228925201828963943/2361183241434822606848:ℚ),(-40114462600914481971/1180591620717411303424:ℚ)⟩ node1398 node351
def node1404 : BoxExpr 3 := .mul ⟨(6937343015438939663/4722366482869645213696:ℚ),(433583938464933729/295147905179352825856:ℚ)⟩ node1403 node308
def node1405 : BoxExpr 3 := .mul ⟨(3783773710137453949/2361183241434822606848:ℚ),(1891886855068726975/1180591620717411303424:ℚ)⟩ node1404 node69
def node1406 : BoxExpr 3 := .add ⟨(4817596095299260300287/4722366482869645213696:ℚ),(2408798047649630150155/2361183241434822606848:ℚ)⟩ node1402 node1405
def node1407 : BoxExpr 3 := .add ⟨(15596598608215522252183/4722366482869645213696:ℚ),(15596598608215522252259/4722366482869645213696:ℚ)⟩ node1406 node358
def node1408 : BoxExpr 3 := .add ⟨(5420856986717619580683/2361183241434822606848:ℚ),(10841713973435239161447/4722366482869645213696:ℚ)⟩ node1407 node361
def node1409 : BoxExpr 3 := .add ⟨(5420849903167895276215/2361183241434822606848:ℚ),(169401559473996727383/73786976294838206464:ℚ)⟩ node1408 node325
def node1410 : BoxExpr 3 := .mul ⟨(129002059111821769441/2361183241434822606848:ℚ),(258004118223643538883/4722366482869645213696:ℚ)⟩ node1398 node1398
def node1411 : BoxExpr 3 := .neg ⟨(-258004118223643538883/4722366482869645213696:ℚ),(-129002059111821769441/2361183241434822606848:ℚ)⟩ node1410
def node1412 : BoxExpr 3 := .add ⟨(4464362364646001674813/4722366482869645213696:ℚ),(2232181182323000837407/2361183241434822606848:ℚ)⟩ node12 node1411
def node1413 : BoxExpr 3 := .sqrt ⟨(2295776295623604060991/2361183241434822606848:ℚ),(35871504619118813453/36893488147419103232:ℚ)⟩ node1412
def node1414 : BoxExpr 3 := .mul ⟨(11375129639329606783199/4722366482869645213696:ℚ),(2843782409832401695803/1180591620717411303424:ℚ)⟩ node50 node1413
def node1415 : BoxExpr 3 := .neg ⟨(551903524255297647411/2361183241434822606848:ℚ),(1103807048510595294823/4722366482869645213696:ℚ)⟩ node1398
def node1416 : BoxExpr 3 := .add ⟨(985747886438854164479/4722366482869645213696:ℚ),(985747886438854164481/4722366482869645213696:ℚ)⟩ node332 node1415
def node1417 : BoxExpr 3 := .mul ⟨(703823990917341873437/4722366482869645213696:ℚ),(21994499716166933545/147573952589676412928:ℚ)⟩ node1416 node335
def node1418 : BoxExpr 3 := .neg ⟨(-21994499716166933545/147573952589676412928:ℚ),(-703823990917341873437/4722366482869645213696:ℚ)⟩ node1417
def node1419 : BoxExpr 3 := .add ⟨(10671305648412264909759/4722366482869645213696:ℚ),(10671305648412264909775/4722366482869645213696:ℚ)⟩ node1414 node1418
def node1420 : BoxExpr 3 := .mul ⟨(205765244849907302399/4722366482869645213696:ℚ),(205765244849907302401/4722366482869645213696:ℚ)⟩ node1416 node1416
def node1421 : BoxExpr 3 := .mul ⟨(169962092246023431781/4722366482869645213696:ℚ),(21245261530752928973/590295810358705651712:ℚ)⟩ node1420 node340
def node1422 : BoxExpr 3 := .add ⟨(2710316935164572085385/1180591620717411303424:ℚ),(10841267740658288341559/4722366482869645213696:ℚ)⟩ node1419 node1421
def node1423 : BoxExpr 3 := .neg ⟨(-10841267740658288341559/4722366482869645213696:ℚ),(-2710316935164572085385/1180591620717411303424:ℚ)⟩ node1422
def node1424 : BoxExpr 3 := .add ⟨(432065677502210871/4722366482869645213696:ℚ),(108016419375552743/1180591620717411303424:ℚ)⟩ node1409 node1423
def node1425 : BoxExpr 3 := .mul ⟨(272208165486002283585/1180591620717411303424:ℚ),(1088832661944009134345/4722366482869645213696:ℚ)⟩ node78 node1400
def node1426 : BoxExpr 3 := .mul ⟨(647821129818912419463/2361183241434822606848:ℚ),(1295642259637824838933/4722366482869645213696:ℚ)⟩ node1425 node349
def node1427 : BoxExpr 3 := .add ⟨(5174873596919195826519/4722366482869645213696:ℚ),(2587436798459597913473/2361183241434822606848:ℚ)⟩ node1426 node385
def node1428 : BoxExpr 3 := .add ⟨(2821007536406441977757/4722366482869645213696:ℚ),(1410503768203220989093/2361183241434822606848:ℚ)⟩ node1427 node387
def node1429 : BoxExpr 3 := .mul ⟨(2840137757612834081067/4722366482869645213696:ℚ),(710034439403208520269/1180591620717411303424:ℚ)⟩ node77 node1413
def node1430 : BoxExpr 3 := .neg ⟨(-710034439403208520269/1180591620717411303424:ℚ),(-2840137757612834081067/4722366482869645213696:ℚ)⟩ node1429
def node1431 : BoxExpr 3 := .add ⟨(-19130221206392103319/4722366482869645213696:ℚ),(-19130221206392102881/4722366482869645213696:ℚ)⟩ node1428 node1430
def node1432 : BoxExpr 3 := .mul ⟨(-915682464229974082401/2361183241434822606848:ℚ),(-1831364928459948164791/4722366482869645213696:ℚ)⟩ node98 node1400
def node1433 : BoxExpr 3 := .mul ⟨(-1161832648800898845171/2361183241434822606848:ℚ),(-1161832648800898845167/2361183241434822606848:ℚ)⟩ node68 node1398
def node1434 : BoxExpr 3 := .add ⟨(-519378778257718231893/590295810358705651712:ℚ),(-4155030226061745855125/4722366482869645213696:ℚ)⟩ node1432 node1433
def node1435 : BoxExpr 3 := .mul ⟨(-4944224157775066770111/4722366482869645213696:ℚ),(-2472112078887533385043/2361183241434822606848:ℚ)⟩ node1434 node349
def node1436 : BoxExpr 3 := .mul ⟨(4573454964875931120911/4722366482869645213696:ℚ),(571681870609491390117/590295810358705651712:ℚ)⟩ node1401 node399
def node1437 : BoxExpr 3 := .add ⟨(-23173074556195978075/295147905179352825856:ℚ),(-185384596449567824575/2361183241434822606848:ℚ)⟩ node1435 node1436
def node1438 : BoxExpr 3 := .mul ⟨(3597674834638119125/4722366482869645213696:ℚ),(1798837417319059563/2361183241434822606848:ℚ)⟩ node1404 node103
def node1439 : BoxExpr 3 := .add ⟨(-13470119203891010551/590295810358705651712:ℚ),(-107760953631128084405/4722366482869645213696:ℚ)⟩ node403 node1438
def node1440 : BoxExpr 3 := .add ⟨(-59816268316282966701/590295810358705651712:ℚ),(-478530146530263733555/4722366482869645213696:ℚ)⟩ node1437 node1439
def node1441 : BoxExpr 3 := .add ⟨(-78306455952797451667/2361183241434822606848:ℚ),(-156612911905594903165/4722366482869645213696:ℚ)⟩ node1440 node409
def node1442 : BoxExpr 3 := .add ⟨(-1103807048510595294823/2361183241434822606848:ℚ),(-551903524255297647411/1180591620717411303424:ℚ)⟩ node1398 node1398
def node1443 : BoxExpr 3 := .neg ⟨(551903524255297647411/1180591620717411303424:ℚ),(1103807048510595294823/2361183241434822606848:ℚ)⟩ node1442
def node1444 : BoxExpr 3 := .mul ⟨(2295776295623604060991/1180591620717411303424:ℚ),(35871504619118813453/18446744073709551616:ℚ)⟩ node86 node1413
def node1445 : BoxExpr 3 := .inv ⟨(2428453639085188931319/4722366482869645213696:ℚ),(2428453639085188931321/4722366482869645213696:ℚ)⟩ node1444
def node1446 : BoxExpr 3 := .mul ⟨(567627322768593721397/2361183241434822606848:ℚ),(1135254645537187442797/4722366482869645213696:ℚ)⟩ node1443 node1445
def node1447 : BoxExpr 3 := .mul ⟨(2812484123835100089065/4722366482869645213696:ℚ),(703121030958775022269/1180591620717411303424:ℚ)⟩ node50 node1446
def node1448 : BoxExpr 3 := .add ⟨(6184253792604026771643/4722366482869645213696:ℚ),(6184253792604026771655/4722366482869645213696:ℚ)⟩ node1447 node335
def node1449 : BoxExpr 3 := .mul ⟨(-985747886438854164481/4722366482869645213696:ℚ),(-985747886438854164479/4722366482869645213696:ℚ)⟩ node422 node1416
def node1450 : BoxExpr 3 := .mul ⟨(-985747886438854164481/4722366482869645213696:ℚ),(-985747886438854164479/4722366482869645213696:ℚ)⟩ node1416 node422
def node1451 : BoxExpr 3 := .add ⟨(-985747886438854164481/2361183241434822606848:ℚ),(-985747886438854164479/2361183241434822606848:ℚ)⟩ node1449 node1450
def node1452 : BoxExpr 3 := .mul ⟨(-1628455508396987079723/4722366482869645213696:ℚ),(-814227754198493539859/2361183241434822606848:ℚ)⟩ node1451 node340
def node1453 : BoxExpr 3 := .add ⟨(284737392762939980745/295147905179352825856:ℚ),(4555798284207039691937/4722366482869645213696:ℚ)⟩ node1448 node1452
def node1454 : BoxExpr 3 := .neg ⟨(-4555798284207039691937/4722366482869645213696:ℚ),(-284737392762939980745/295147905179352825856:ℚ)⟩ node1453
def node1455 : BoxExpr 3 := .add ⟨(-26186291163702639169/2361183241434822606848:ℚ),(-26186291163702639151/2361183241434822606848:ℚ)⟩ node414 node1454
def node1456 : BoxExpr 3 := .mul ⟨(4317217666393469805193/2361183241434822606848:ℚ),(8686607493442050763947/4722366482869645213696:ℚ)⟩ node112 node1373
def node1457 : BoxExpr 3 := .mul ⟨(10254981582252777561501/4722366482869645213696:ℚ),(2589064666654952781759/1180591620717411303424:ℚ)⟩ node1456 node304
def node1458 : BoxExpr 3 := .add ⟨(337206132829930651941/73786976294838206464:ℚ),(44682608279280629541317/4722366482869645213696:ℚ)⟩ node1457 node448
def node1459 : BoxExpr 3 := .mul ⟨(5646311512997105381239/1180591620717411303424:ℚ),(5648902422551936976441/1180591620717411303424:ℚ)⟩ node111 node1386
def node1460 : BoxExpr 3 := .neg ⟨(-5648902422551936976441/1180591620717411303424:ℚ),(-5646311512997105381239/1180591620717411303424:ℚ)⟩ node1459
def node1461 : BoxExpr 3 := .add ⟨(-253604297273046545385/1180591620717411303424:ℚ),(22097362227292208016361/4722366482869645213696:ℚ)⟩ node1458 node1460
def node1462 : BoxExpr 3 := .mul ⟨(-534250086521124394805/4722366482869645213696:ℚ),(-250622468268308037297/2361183241434822606848:ℚ)⟩ node131 node1373
def node1463 : BoxExpr 3 := .mul ⟨(-160999415175428647171/1180591620717411303424:ℚ),(-607967980186240750971/4722366482869645213696:ℚ)⟩ node118 node1371
def node1464 : BoxExpr 3 := .add ⟨(-1178247747222838983489/4722366482869645213696:ℚ),(-1109212916722856825565/4722366482869645213696:ℚ)⟩ node1462 node1463
def node1465 : BoxExpr 3 := .mul ⟨(-175589815310722101255/590295810358705651712:ℚ),(-1317394547920979290345/4722366482869645213696:ℚ)⟩ node1464 node304
def node1466 : BoxExpr 3 := .mul ⟨(1059643817581488158867/4722366482869645213696:ℚ),(1118166186676066276467/4722366482869645213696:ℚ)⟩ node118 node1373
def node1467 : BoxExpr 3 := .mul ⟨(1188379260539098710023/4722366482869645213696:ℚ),(1276301152816749377245/4722366482869645213696:ℚ)⟩ node1466 node461
def node1468 : BoxExpr 3 := .add ⟨(-216339261946678100017/4722366482869645213696:ℚ),(-10273348776057478275/1180591620717411303424:ℚ)⟩ node1465 node1467
def node1469 : BoxExpr 3 := .add ⟨(-371704998355143617747/590295810358705651712:ℚ),(343120121366857464951/1180591620717411303424:ℚ)⟩ node1468 node476
def node1470 : BoxExpr 3 := .add ⟨(-277047037557025328333/590295810358705651712:ℚ),(-1099425946793089276313/2361183241434822606848:ℚ)⟩ node1371 node1371
def node1471 : BoxExpr 3 := .neg ⟨(1099425946793089276313/2361183241434822606848:ℚ),(277047037557025328333/590295810358705651712:ℚ)⟩ node1470
def node1472 : BoxExpr 3 := .mul ⟨(2295248582519148528959/1180591620717411303424:ℚ),(4592603595570680468651/2361183241434822606848:ℚ)⟩ node86 node1386
def node1473 : BoxExpr 3 := .inv ⟨(303487236793614387227/590295810358705651712:ℚ),(607252994522451009855/1180591620717411303424:ℚ)⟩ node1472
def node1474 : BoxExpr 3 := .mul ⟨(1130489957056213592419/4722366482869645213696:ℚ),(570011306967753819017/2361183241434822606848:ℚ)⟩ node1471 node1473
def node1475 : BoxExpr 3 := .mul ⟨(341293316036334240933/2361183241434822606848:ℚ),(721995890842616282325/4722366482869645213696:ℚ)⟩ node117 node1474
def node1476 : BoxExpr 3 := .neg ⟨(-721995890842616282325/4722366482869645213696:ℚ),(-341293316036334240933/2361183241434822606848:ℚ)⟩ node1475
def node1477 : BoxExpr 3 := .add ⟨(255467350631873846811/2361183241434822606848:ℚ),(157777128664148054965/1180591620717411303424:ℚ)⟩ node479 node1476
def node1478 : BoxExpr 3 := .add ⟨(-2973639986841148941975/4722366482869645213696:ℚ),(343120121366857464951/1180591620717411303424:ℚ)⟩ node1468 node492
def node1479 : BoxExpr 3 := .mul ⟨(-1976886360452356411907/4722366482869645213696:ℚ),(-962183487188499287871/2361183241434822606848:ℚ)⟩ node175 node1373
def node1480 : BoxExpr 3 := .mul ⟨(258949676587433020879/1180591620717411303424:ℚ),(1069853176847248443549/4722366482869645213696:ℚ)⟩ node148 node1371
def node1481 : BoxExpr 3 := .add ⟨(-941087654102624328391/4722366482869645213696:ℚ),(-854513797529750132193/4722366482869645213696:ℚ)⟩ node1479 node1480
def node1482 : BoxExpr 3 := .add ⟨(94711052247107755125/4722366482869645213696:ℚ),(53834844829374577839/1180591620717411303424:ℚ)⟩ node1481 node1480
def node1483 : BoxExpr 3 := .mul ⟨(112486811122641950559/4722366482869645213696:ℚ),(128364860217581677877/2361183241434822606848:ℚ)⟩ node1482 node304
def node1484 : BoxExpr 3 := .mul ⟨(-464393630620907771761/1180591620717411303424:ℚ),(-1805321548523283222375/4722366482869645213696:ℚ)⟩ node148 node1373
def node1485 : BoxExpr 3 := .mul ⟨(-1170506863252536757399/2361183241434822606848:ℚ),(-576606208499190166311/1180591620717411303424:ℚ)⟩ node36 node1371
def node1486 : BoxExpr 3 := .add ⟨(-2099294124494352300921/2361183241434822606848:ℚ),(-4111746382520043887619/4722366482869645213696:ℚ)⟩ node1484 node1485
def node1487 : BoxExpr 3 := .mul ⟨(-4792367258320207304313/4722366482869645213696:ℚ),(-4611279794691690503451/4722366482869645213696:ℚ)⟩ node1486 node461
def node1488 : BoxExpr 3 := .add ⟨(-2339940223598782676877/2361183241434822606848:ℚ),(-4354550074256527147697/4722366482869645213696:ℚ)⟩ node1483 node1487
def node1489 : BoxExpr 3 := .mul ⟨(19822737713950129096365/4722366482869645213696:ℚ),(20472387025386463932843/4722366482869645213696:ℚ)⟩ node1374 node514
def node1490 : BoxExpr 3 := .add ⟨(3757592613907480448013/1180591620717411303424:ℚ),(991319201918423339337/295147905179352825856:ℚ)⟩ node1487 node1489
def node1491 : BoxExpr 3 := .add ⟨(5175245004216178219149/2361183241434822606848:ℚ),(11506557156438246281695/4722366482869645213696:ℚ)⟩ node1488 node1490
def node1492 : BoxExpr 3 := .mul ⟨(13232866619626381125/4722366482869645213696:ℚ),(1881608102983007187/590295810358705651712:ℚ)⟩ node1377 node189
def node1493 : BoxExpr 3 := .add ⟨(-40125479059474219379/4722366482869645213696:ℚ),(-18736703623883364219/2361183241434822606848:ℚ)⟩ node518 node1492
def node1494 : BoxExpr 3 := .add ⟨(-93483824738574819883/4722366482869645213696:ℚ),(-22499919829849378593/1180591620717411303424:ℚ)⟩ node518 node1493
def node1495 : BoxExpr 3 := .add ⟨(10257006183693781618415/4722366482869645213696:ℚ),(11416557477118848767323/4722366482869645213696:ℚ)⟩ node1491 node1494
def node1496 : BoxExpr 3 := .add ⟨(10680369731030176494969/2361183241434822606848:ℚ),(14005014258223147620933/2361183241434822606848:ℚ)⟩ node1495 node527
def node1497 : BoxExpr 3 := .mul ⟨(-607252994522451009855/590295810358705651712:ℚ),(-303487236793614387227/295147905179352825856:ℚ)⟩ node6 node1473
def node1498 : BoxExpr 3 := .mul ⟨(1130489957056213592419/2361183241434822606848:ℚ),(570011306967753819017/1180591620717411303424:ℚ)⟩ node86 node1474
def node1499 : BoxExpr 3 := .mul ⟨(1115577555165699207331/295147905179352825856:ℚ),(17865625518527516466227/4722366482869645213696:ℚ)⟩ node1472 node1472
def node1500 : BoxExpr 3 := .inv ⟨(1248248776702706176015/4722366482869645213696:ℚ),(624697300718433803217/2361183241434822606848:ℚ)⟩ node1499
def node1501 : BoxExpr 3 := .mul ⟨(597637947452400609519/4722366482869645213696:ℚ),(603230649096696359457/4722366482869645213696:ℚ)⟩ node1498 node1500
def node1502 : BoxExpr 3 := .neg ⟨(-603230649096696359457/4722366482869645213696:ℚ),(-597637947452400609519/4722366482869645213696:ℚ)⟩ node1501
def node1503 : BoxExpr 3 := .mul ⟨(-283117822222531514019/4722366482869645213696:ℚ),(-278275169282524033807/4722366482869645213696:ℚ)⟩ node1471 node1502
def node1504 : BoxExpr 3 := .add ⟨(-5141141778402139592859/4722366482869645213696:ℚ),(-5134070957980354229439/4722366482869645213696:ℚ)⟩ node1497 node1503
def node1505 : BoxExpr 3 := .mul ⟨(-12746338051453051046217/4722366482869645213696:ℚ),(-6354876599211258074795/2361183241434822606848:ℚ)⟩ node11 node1504
def node1506 : BoxExpr 3 := .add ⟨(-618123577719049644149/590295810358705651712:ℚ),(-1227100942180465564141/1180591620717411303424:ℚ)⟩ node1505 node546
def node1507 : BoxExpr 3 := .neg ⟨(1227100942180465564141/1180591620717411303424:ℚ),(618123577719049644149/590295810358705651712:ℚ)⟩ node1506
def cert_iv7 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-4787/20480:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/20480:ℚ)],
    whole := node1397, centerValue := node1424, gradient := ![node1431, node1441, node1455],
    hessian := ![![node1461, node1469, node1477], ![node1478, node1496, node536], ![node1477, node536, node1507]] }

end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part2
end

section
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646CheckB4Part2
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part2

theorem cert_iv4_check : cert_iv4.check = true := by decide +kernel

theorem cert_iv4_lower_pos : 0 < cert_iv4.lower := by decide +kernel

theorem positive_iv4 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(317/1280:ℝ)) ≤ r) (hrhi : r ≤ (-(123/512:ℝ))) :
    0 < node986.eval ![A,ρ,r] := by
  apply cert_iv4.positive_sound cert_iv4_check cert_iv4_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv4,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv4,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv4,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv5_check : cert_iv5.check = true := by decide +kernel

theorem cert_iv5_lower_pos : 0 < cert_iv5.lower := by decide +kernel

theorem positive_iv5 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(123/512:ℝ)) ≤ r) (hrhi : r ≤ (-(1211/5120:ℝ))) :
    0 < node1123.eval ![A,ρ,r] := by
  apply cert_iv5.positive_sound cert_iv5_check cert_iv5_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv5,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv5,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv5,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv6_check : cert_iv6.check = true := by decide +kernel

theorem cert_iv6_lower_pos : 0 < cert_iv6.lower := by decide +kernel

theorem positive_iv6 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(1211/5120:ℝ)) ≤ r) (hrhi : r ≤ (-(2403/10240:ℝ))) :
    0 < node1260.eval ![A,ρ,r] := by
  apply cert_iv6.positive_sound cert_iv6_check cert_iv6_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv6,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv6,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv6,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv7_check : cert_iv7.check = true := by decide +kernel

theorem cert_iv7_lower_pos : 0 < cert_iv7.lower := by decide +kernel

theorem positive_iv7 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(2403/10240:ℝ)) ≤ r) (hrhi : r ≤ (-(149/640:ℝ))) :
    0 < node1397.eval ![A,ρ,r] := by
  apply cert_iv7.positive_sound cert_iv7_check cert_iv7_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv7,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv7,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv7,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part2
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
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646BoundB4Part2
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part2
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate.CapacityCore
noncomputable section
namespace Parameters
def b : ℚ := (103531361122339324647880530522418473224550678173/6474633415922124204664207433178390079472570088576:ℚ)
def c : ℚ := (148022665013912365111/4722366482869645213696:ℚ)
def theta : ℚ := (105113898053531722649817636563532003778556764000751/182628568201966125342452015454275643968150995402752:ℚ)
end Parameters

theorem iv_shape4 : SplitDataB4Part2.node986.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound4 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(317/1280:ℝ)) ≤ r) (hrhi : r ≤ (-(123/512:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part2.node986 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape4 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part2.positive_iv4 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part2.node986.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape5 : SplitDataB4Part2.node1123.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound5 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(123/512:ℝ)) ≤ r) (hrhi : r ≤ (-(1211/5120:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part2.node1123 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape5 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part2.positive_iv5 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part2.node1123.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape6 : SplitDataB4Part2.node1260.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound6 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(1211/5120:ℝ)) ≤ r) (hrhi : r ≤ (-(2403/10240:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part2.node1260 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape6 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part2.positive_iv6 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part2.node1260.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape7 : SplitDataB4Part2.node1397.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound7 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(2403/10240:ℝ)) ≤ r) (hrhi : r ≤ (-(149/640:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part2.node1397 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape7 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part2.positive_iv7 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part2.node1397.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem actual_bound (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (r : ℝ)
    (hrlo : (-(317/1280:ℝ)) ≤ r) (hrhi : r ≤ (-(149/640:ℝ))) : fA A r+3/10^6 ≤ l40Lhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) r := by
  have hc : 0 ≤ (Parameters.c:ℝ) := by norm_num [Parameters.c]
  have hθ : 0 ≤ (Parameters.theta:ℝ) := by norm_num [Parameters.theta]
  by_cases h0 : r ≤ (-(123/512:ℝ))
  · have h := iv_bound4 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  by_cases h1 : r ≤ (-(1211/5120:ℝ))
  · have h := iv_bound5 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  by_cases h2 : r ≤ (-(2403/10240:ℝ))
  · have h := iv_bound6 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  have h := iv_bound7 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
  exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
    (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
end
end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part2
end

section
-- Source module: Solutions.Sol_GaussLocalMaxCase1FamilyAdaptive0Seed25646B4Part2
set_option autoImplicit false
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate
open GaussLocalMaxColoring.Certificate.CapacityCore
theorem solution (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (r : ℝ)
    (hrlo : (-(317/1280:ℝ)) ≤ r) (hrhi : r ≤ (-(149/640:ℝ))) :
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
  have h := GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part2.actual_bound A ρ hAlo hAhi hρlo hρhi r hrlo hrhi
  simpa only [Case2Static,constructedA,constructedMu,constructedMass,constructedKappa,thresholdCapacity,
    GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part2.Parameters.b,GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part2.Parameters.c,GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part2.Parameters.theta,
    show ¬ (4:ℕ)=1 by decide,show ¬ (4:ℕ)=2 by decide,show ¬ (4:ℕ)=3 by decide,ite_false,and_assoc] using h
end

#print axioms solution
