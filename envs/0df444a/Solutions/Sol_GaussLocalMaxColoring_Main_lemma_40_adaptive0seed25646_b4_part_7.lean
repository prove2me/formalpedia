-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_40_adaptive0seed25646_b4_part_7
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T14:29:13.885193+00:00
-- url     : https://prove2.me/submissions/9251202f-fa50-457e-ba48-8d1bdc80aa4b

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
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646DefsB4Part7
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part7

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
def node3700 : BoxExpr 3 := .var 2
def node3701 : BoxExpr 3 := .mul ⟨(-99806752600372261631/1180591620717411303424:ℚ),(-97070880340809347393/1180591620717411303424:ℚ)⟩ node13 node3700
def node3702 : BoxExpr 3 := .add ⟨(490489057758333390081/1180591620717411303424:ℚ),(493224930017896304319/1180591620717411303424:ℚ)⟩ node3701 node301
def node3703 : BoxExpr 3 := .mul ⟨(4115879371111100538373/4722366482869645213696:ℚ),(2083845295022755113845/2361183241434822606848:ℚ)⟩ node36 node3702
def node3704 : BoxExpr 3 := .mul ⟨(4888364498514913794219/4722366482869645213696:ℚ),(2484380802605248136553/2361183241434822606848:ℚ)⟩ node3703 node304
def node3705 : BoxExpr 3 := .add ⟨(-13913168487219277595/1180591620717411303424:ℚ),(-28683534113113745915/4722366482869645213696:ℚ)⟩ node3700 node306
def node3706 : BoxExpr 3 := .mul ⟨(310030818899057625/1180591620717411303424:ℚ),(2406125271767580791/4722366482869645213696:ℚ)⟩ node3705 node308
def node3707 : BoxExpr 3 := .mul ⟨(337874440212326803/1180591620717411303424:ℚ),(2627208738930223743/4722366482869645213696:ℚ)⟩ node3706 node37
def node3708 : BoxExpr 3 := .add ⟨(4889715996275763101431/4722366482869645213696:ℚ),(4971388813949426496849/4722366482869645213696:ℚ)⟩ node3704 node3707
def node3709 : BoxExpr 3 := .add ⟨(7802080125707574730619/2361183241434822606848:ℚ),(15813152810809216994091/4722366482869645213696:ℚ)⟩ node3708 node316
def node3710 : BoxExpr 3 := .add ⟨(5421107009226664054437/2361183241434822606848:ℚ),(5532664887105236082413/2361183241434822606848:ℚ)⟩ node3709 node323
def node3711 : BoxExpr 3 := .add ⟨(5421099925676939749969/2361183241434822606848:ℚ),(11065315607111023555891/4722366482869645213696:ℚ)⟩ node3710 node325
def node3712 : BoxExpr 3 := .mul ⟨(101014028274061824491/2361183241434822606848:ℚ),(209342442774928618947/4722366482869645213696:ℚ)⟩ node3700 node3700
def node3713 : BoxExpr 3 := .neg ⟨(-209342442774928618947/4722366482869645213696:ℚ),(-101014028274061824491/2361183241434822606848:ℚ)⟩ node3712
def node3714 : BoxExpr 3 := .add ⟨(4513024040094716594749/4722366482869645213696:ℚ),(2260169213160760782357/2361183241434822606848:ℚ)⟩ node12 node3713
def node3715 : BoxExpr 3 := .sqrt ⟨(1154127198994120933223/1180591620717411303424:ℚ),(4620248334850462415043/4722366482869645213696:ℚ)⟩ node3714
def node3716 : BoxExpr 3 := .mul ⟨(357140366262397854943/147573952589676412928:ℚ),(357965516805699557945/147573952589676412928:ℚ)⟩ node11 node3715
def node3717 : BoxExpr 3 := .neg ⟨(976755098702920758067/4722366482869645213696:ℚ),(994279505572944832103/4722366482869645213696:ℚ)⟩ node3700
def node3718 : BoxExpr 3 := .add ⟨(214673984157794906931/1180591620717411303424:ℚ),(876220343501203701761/4722366482869645213696:ℚ)⟩ node332 node3717
def node3719 : BoxExpr 3 := .mul ⟨(306554449377331127097/2361183241434822606848:ℚ),(312810662629929721529/2361183241434822606848:ℚ)⟩ node3718 node335
def node3720 : BoxExpr 3 := .neg ⟨(-312810662629929721529/2361183241434822606848:ℚ),(-306554449377331127097/2361183241434822606848:ℚ)⟩ node3719
def node3721 : BoxExpr 3 := .add ⟨(5401435197568435957559/2361183241434822606848:ℚ),(5420893819513861800023/2361183241434822606848:ℚ)⟩ node3716 node3720
def node3722 : BoxExpr 3 := .mul ⟨(156141780664771139337/4722366482869645213696:ℚ),(162579946548074905601/4722366482869645213696:ℚ)⟩ node3718 node3718
def node3723 : BoxExpr 3 := .mul ⟨(32243277707275240273/1180591620717411303424:ℚ),(134291035848709872027/4722366482869645213696:ℚ)⟩ node3722 node340
def node3724 : BoxExpr 3 := .add ⟨(5465921752982986438105/2361183241434822606848:ℚ),(10976078674876433472073/4722366482869645213696:ℚ)⟩ node3721 node3723
def node3725 : BoxExpr 3 := .neg ⟨(-10976078674876433472073/4722366482869645213696:ℚ),(-5465921752982986438105/2361183241434822606848:ℚ)⟩ node3724
def node3726 : BoxExpr 3 := .add ⟨(-133878823522553972135/4722366482869645213696:ℚ),(133472101145050679681/4722366482869645213696:ℚ)⟩ node3711 node3725
def node3727 : BoxExpr 3 := .var 2
def node3728 : BoxExpr 3 := .mul ⟨(-393737741475493193975/4722366482869645213696:ℚ),(-393737741475493193973/4722366482869645213696:ℚ)⟩ node51 node3727
def node3729 : BoxExpr 3 := .add ⟨(1967445499959329412873/4722366482869645213696:ℚ),(1967445499959329412875/4722366482869645213696:ℚ)⟩ node3728 node301
def node3730 : BoxExpr 3 := .mul ⟨(4141742743305584028779/4722366482869645213696:ℚ),(2070871371652792014397/2361183241434822606848:ℚ)⟩ node68 node3729
def node3731 : BoxExpr 3 := .mul ⟨(2464206445274212632205/2361183241434822606848:ℚ),(4928412890548425264431/4722366482869645213696:ℚ)⟩ node3730 node349
def node3732 : BoxExpr 3 := .add ⟨(-10542026007748857037/1180591620717411303424:ℚ),(-21084052015497714073/2361183241434822606848:ℚ)⟩ node3727 node351
def node3733 : BoxExpr 3 := .mul ⟨(1823124273681905645/4722366482869645213696:ℚ),(911562136840952823/2361183241434822606848:ℚ)⟩ node3732 node308
def node3734 : BoxExpr 3 := .mul ⟨(497185282731371935/1180591620717411303424:ℚ),(1988741130925487743/4722366482869645213696:ℚ)⟩ node3733 node69
def node3735 : BoxExpr 3 := .add ⟨(2465200815839675376075/2361183241434822606848:ℚ),(2465200815839675376087/2361183241434822606848:ℚ)⟩ node3731 node3734
def node3736 : BoxExpr 3 := .add ⟨(7854702072297806352023/2361183241434822606848:ℚ),(15709404144595612704123/4722366482869645213696:ℚ)⟩ node3735 node358
def node3737 : BoxExpr 3 := .add ⟨(10954519509815329613229/4722366482869645213696:ℚ),(10954519509815329613311/4722366482869645213696:ℚ)⟩ node3736 node361
def node3738 : BoxExpr 3 := .add ⟨(10954505342715881004293/4722366482869645213696:ℚ),(1369313167839485125547/590295810358705651712:ℚ)⟩ node3737 node325
def node3739 : BoxExpr 3 := .mul ⟨(205668991666871326473/4722366482869645213696:ℚ),(205668991666871326475/4722366482869645213696:ℚ)⟩ node3727 node3727
def node3740 : BoxExpr 3 := .neg ⟨(-205668991666871326475/4722366482869645213696:ℚ),(-205668991666871326473/4722366482869645213696:ℚ)⟩ node3739
def node3741 : BoxExpr 3 := .add ⟨(4516697491202773887221/4722366482869645213696:ℚ),(4516697491202773887223/4722366482869645213696:ℚ)⟩ node12 node3740
def node3742 : BoxExpr 3 := .sqrt ⟨(4618387255927916838311/4722366482869645213696:ℚ),(4618387255927916838313/4722366482869645213696:ℚ)⟩ node3741
def node3743 : BoxExpr 3 := .mul ⟨(5720804969211700589303/2361183241434822606848:ℚ),(2860402484605850294655/1180591620717411303424:ℚ)⟩ node50 node3742
def node3744 : BoxExpr 3 := .neg ⟨(246379325534483198771/1180591620717411303424:ℚ),(985517302137932795085/4722366482869645213696:ℚ)⟩ node3727
def node3745 : BoxExpr 3 := .add ⟨(867458140066191664741/4722366482869645213696:ℚ),(867458140066191664743/4722366482869645213696:ℚ)⟩ node332 node3744
def node3746 : BoxExpr 3 := .mul ⟨(38710319500453803039/295147905179352825856:ℚ),(619365112007260848627/4722366482869645213696:ℚ)⟩ node3745 node335
def node3747 : BoxExpr 3 := .neg ⟨(-619365112007260848627/4722366482869645213696:ℚ),(-38710319500453803039/295147905179352825856:ℚ)⟩ node3746
def node3748 : BoxExpr 3 := .add ⟨(10822244826416140329979/4722366482869645213696:ℚ),(2705561206604035082499/1180591620717411303424:ℚ)⟩ node3743 node3747
def node3749 : BoxExpr 3 := .mul ⟨(79672302805884107489/2361183241434822606848:ℚ),(159344605611768214979/4722366482869645213696:ℚ)⟩ node3745 node3745
def node3750 : BoxExpr 3 := .mul ⟨(131618644235320545571/4722366482869645213696:ℚ),(131618644235320545573/4722366482869645213696:ℚ)⟩ node3749 node340
def node3751 : BoxExpr 3 := .add ⟨(5476931735325730437775/2361183241434822606848:ℚ),(10953863470651460875569/4722366482869645213696:ℚ)⟩ node3748 node3750
def node3752 : BoxExpr 3 := .neg ⟨(-10953863470651460875569/4722366482869645213696:ℚ),(-5476931735325730437775/2361183241434822606848:ℚ)⟩ node3751
def node3753 : BoxExpr 3 := .add ⟨(160468016105032181/1180591620717411303424:ℚ),(320936032210064413/2361183241434822606848:ℚ)⟩ node3738 node3752
def node3754 : BoxExpr 3 := .mul ⟨(1115630993321501189431/4722366482869645213696:ℚ),(1115630993321501189437/4722366482869645213696:ℚ)⟩ node78 node3729
def node3755 : BoxExpr 3 := .mul ⟨(1327530585396225429935/4722366482869645213696:ℚ),(1327530585396225429943/4722366482869645213696:ℚ)⟩ node3754 node349
def node3756 : BoxExpr 3 := .add ⟨(650845240334699552191/590295810358705651712:ℚ),(1301690480669399104489/1180591620717411303424:ℚ)⟩ node3755 node385
def node3757 : BoxExpr 3 := .add ⟨(1426447931082421284383/2361183241434822606848:ℚ),(713223965541210642299/1180591620717411303424:ℚ)⟩ node3756 node387
def node3758 : BoxExpr 3 := .mul ⟨(2856736531743799277291/4722366482869645213696:ℚ),(714184132935949819325/1180591620717411303424:ℚ)⟩ node77 node3742
def node3759 : BoxExpr 3 := .neg ⟨(-714184132935949819325/1180591620717411303424:ℚ),(-2856736531743799277291/4722366482869645213696:ℚ)⟩ node3758
def node3760 : BoxExpr 3 := .add ⟨(-1920334789478354267/2361183241434822606848:ℚ),(-3840669578956708095/4722366482869645213696:ℚ)⟩ node3757 node3759
def node3761 : BoxExpr 3 := .mul ⟨(-1876438451638765542353/4722366482869645213696:ℚ),(-938219225819382771171/2361183241434822606848:ℚ)⟩ node98 node3729
def node3762 : BoxExpr 3 := .mul ⟨(-2074649150188026598813/4722366482869645213696:ℚ),(-1037324575094013299403/2361183241434822606848:ℚ)⟩ node68 node3727
def node3763 : BoxExpr 3 := .add ⟨(-1975543800913396070583/2361183241434822606848:ℚ),(-987771900456698035287/1180591620717411303424:ℚ)⟩ node3761 node3762
def node3764 : BoxExpr 3 := .mul ⟨(-4701545285496866276225/4722366482869645213696:ℚ),(-587693160687108284525/590295810358705651712:ℚ)⟩ node3763 node349
def node3765 : BoxExpr 3 := .mul ⟨(1171504190613190042297/1180591620717411303424:ℚ),(2343008381226380084607/2361183241434822606848:ℚ)⟩ node3730 node399
def node3766 : BoxExpr 3 := .add ⟨(-15528523044106107037/4722366482869645213696:ℚ),(-7764261522053053493/2361183241434822606848:ℚ)⟩ node3764 node3765
def node3767 : BoxExpr 3 := .mul ⟨(945464035041416971/4722366482869645213696:ℚ),(236366008760354243/1180591620717411303424:ℚ)⟩ node3733 node103
def node3768 : BoxExpr 3 := .add ⟨(-55206582215362393281/2361183241434822606848:ℚ),(-110413164430724786559/4722366482869645213696:ℚ)⟩ node403 node3767
def node3769 : BoxExpr 3 := .add ⟨(-125941687474830893599/4722366482869645213696:ℚ),(-125941687474830893545/4722366482869645213696:ℚ)⟩ node3766 node3768
def node3770 : BoxExpr 3 := .add ⟨(195975547149837936675/4722366482869645213696:ℚ),(195975547149837936845/4722366482869645213696:ℚ)⟩ node3769 node409
def node3771 : BoxExpr 3 := .add ⟨(-985517302137932795085/2361183241434822606848:ℚ),(-246379325534483198771/590295810358705651712:ℚ)⟩ node3727 node3727
def node3772 : BoxExpr 3 := .neg ⟨(246379325534483198771/590295810358705651712:ℚ),(985517302137932795085/2361183241434822606848:ℚ)⟩ node3771
def node3773 : BoxExpr 3 := .mul ⟨(4618387255927916838311/2361183241434822606848:ℚ),(4618387255927916838313/2361183241434822606848:ℚ)⟩ node86 node3742
def node3774 : BoxExpr 3 := .inv ⟨(603585839675596980377/1180591620717411303424:ℚ),(1207171679351193960755/2361183241434822606848:ℚ)⟩ node3773
def node3775 : BoxExpr 3 := .mul ⟨(125963177674487377643/590295810358705651712:ℚ),(1007705421395899021147/4722366482869645213696:ℚ)⟩ node3772 node3774
def node3776 : BoxExpr 3 := .mul ⟨(1248246598382092761715/2361183241434822606848:ℚ),(156030824797761595215/295147905179352825856:ℚ)⟩ node50 node3775
def node3777 : BoxExpr 3 := .add ⟨(733532858191639025751/590295810358705651712:ℚ),(5868262865533112206019/4722366482869645213696:ℚ)⟩ node3776 node335
def node3778 : BoxExpr 3 := .mul ⟨(-867458140066191664743/4722366482869645213696:ℚ),(-867458140066191664741/4722366482869645213696:ℚ)⟩ node422 node3745
def node3779 : BoxExpr 3 := .mul ⟨(-867458140066191664743/4722366482869645213696:ℚ),(-867458140066191664741/4722366482869645213696:ℚ)⟩ node3745 node422
def node3780 : BoxExpr 3 := .add ⟨(-867458140066191664743/2361183241434822606848:ℚ),(-867458140066191664741/2361183241434822606848:ℚ)⟩ node3778 node3779
def node3781 : BoxExpr 3 := .mul ⟨(-358260211847337157539/1180591620717411303424:ℚ),(-1433040847389348630151/4722366482869645213696:ℚ)⟩ node3780 node340
def node3782 : BoxExpr 3 := .add ⟨(1108805504535940893963/1180591620717411303424:ℚ),(1108805504535940893967/1180591620717411303424:ℚ)⟩ node3777 node3781
def node3783 : BoxExpr 3 := .neg ⟨(-1108805504535940893967/1180591620717411303424:ℚ),(-1108805504535940893963/1180591620717411303424:ℚ)⟩ node3782
def node3784 : BoxExpr 3 := .add ⟨(68203683735870837731/4722366482869645213696:ℚ),(34101841867935418883/2361183241434822606848:ℚ)⟩ node414 node3783
def node3785 : BoxExpr 3 := .mul ⟨(4420262654852080960685/2361183241434822606848:ℚ),(4453378894154986960317/2361183241434822606848:ℚ)⟩ node112 node3702
def node3786 : BoxExpr 3 := .mul ⟨(5249875685802000199001/2361183241434822606848:ℚ),(5309362003883893769081/2361183241434822606848:ℚ)⟩ node3785 node304
def node3787 : BoxExpr 3 := .add ⟨(21825962290466784560725/4722366482869645213696:ℚ),(44945073620428605952443/4722366482869645213696:ℚ)⟩ node3786 node448
def node3788 : BoxExpr 3 := .mul ⟨(5678305819051074991457/1180591620717411303424:ℚ),(22731621807464275082013/4722366482869645213696:ℚ)⟩ node111 node3715
def node3789 : BoxExpr 3 := .neg ⟨(-22731621807464275082013/4722366482869645213696:ℚ),(-5678305819051074991457/1180591620717411303424:ℚ)⟩ node3788
def node3790 : BoxExpr 3 := .add ⟨(-113207439624686315161/590295810358705651712:ℚ),(22231850344224305986615/4722366482869645213696:ℚ)⟩ node3787 node3789
def node3791 : BoxExpr 3 := .mul ⟨(-136947482737641843581/1180591620717411303424:ℚ),(-513208840766513536853/4722366482869645213696:ℚ)⟩ node131 node3702
def node3792 : BoxExpr 3 := .mul ⟨(-577802312306656950979/4722366482869645213696:ℚ),(-67516578336538271317/590295810358705651712:ℚ)⟩ node118 node3700
def node3793 : BoxExpr 3 := .add ⟨(-1125592243257224325303/4722366482869645213696:ℚ),(-1053341467458819707389/4722366482869645213696:ℚ)⟩ node3791 node3792
def node3794 : BoxExpr 3 := .mul ⟨(-1341942114123730391301/4722366482869645213696:ℚ),(-156379614478025530529/590295810358705651712:ℚ)⟩ node3793 node304
def node3795 : BoxExpr 3 := .mul ⟨(1084935798063014216189/4722366482869645213696:ℚ),(1146504593343331838117/4722366482869645213696:ℚ)⟩ node118 node3702
def node3796 : BoxExpr 3 := .mul ⟨(1216743947392843192531/4722366482869645213696:ℚ),(81790454743563749773/295147905179352825856:ℚ)⟩ node3795 node461
def node3797 : BoxExpr 3 := .add ⟨(-62599083365443599385/2361183241434822606848:ℚ),(7201295009101969017/590295810358705651712:ℚ)⟩ node3794 node3796
def node3798 : BoxExpr 3 := .add ⟨(-2882498891625358040729/4722366482869645213696:ℚ),(91949015040279720315/295147905179352825856:ℚ)⟩ node3797 node476
def node3799 : BoxExpr 3 := .add ⟨(-994279505572944832103/2361183241434822606848:ℚ),(-976755098702920758067/2361183241434822606848:ℚ)⟩ node3700 node3700
def node3800 : BoxExpr 3 := .neg ⟨(976755098702920758067/2361183241434822606848:ℚ),(994279505572944832103/2361183241434822606848:ℚ)⟩ node3799
def node3801 : BoxExpr 3 := .mul ⟨(1154127198994120933223/590295810358705651712:ℚ),(4620248334850462415043/2361183241434822606848:ℚ)⟩ node86 node3715
def node3802 : BoxExpr 3 := .inv ⟨(2413370838783322935303/4722366482869645213696:ℚ),(2415325756334183537513/4722366482869645213696:ℚ)⟩ node3801
def node3803 : BoxExpr 3 := .mul ⟨(998343639949819917377/4722366482869645213696:ℚ),(1017078580206347599001/4722366482869645213696:ℚ)⟩ node3800 node3802
def node3804 : BoxExpr 3 := .mul ⟨(75349632541077823441/590295810358705651712:ℚ),(644133323845246959243/4722366482869645213696:ℚ)⟩ node117 node3803
def node3805 : BoxExpr 3 := .neg ⟨(-644133323845246959243/4722366482869645213696:ℚ),(-75349632541077823441/590295810358705651712:ℚ)⟩ node3804
def node3806 : BoxExpr 3 := .add ⟨(4599978658289976693/36893488147419103232:ℚ),(355449043200319057099/2361183241434822606848:ℚ)⟩ node479 node3805
def node3807 : BoxExpr 3 := .add ⟨(-360312361453169755091/590295810358705651712:ℚ),(91949015040279720315/295147905179352825856:ℚ)⟩ node3797 node492
def node3808 : BoxExpr 3 := .mul ⟨(-2026987866190071028197/4722366482869645213696:ℚ),(-1970298495089611545235/4722366482869645213696:ℚ)⟩ node175 node3702
def node3809 : BoxExpr 3 := .mul ⟨(920227206396280433259/4722366482869645213696:ℚ),(959884914391455532373/4722366482869645213696:ℚ)⟩ node148 node3700
def node3810 : BoxExpr 3 := .add ⟨(-553380329896895297469/2361183241434822606848:ℚ),(-505206790349078006431/2361183241434822606848:ℚ)⟩ node3808 node3809
def node3811 : BoxExpr 3 := .add ⟨(-186533453397510161679/4722366482869645213696:ℚ),(-50528666306700480489/4722366482869645213696:ℚ)⟩ node3810 node3809
def node3812 : BoxExpr 3 := .mul ⟨(-1737398538875873369/36893488147419103232:ℚ),(-7501511714138923063/590295810358705651712:ℚ)⟩ node3811 node304
def node3813 : BoxExpr 3 := .mul ⟨(-238081528922365183853/590295810358705651712:ℚ),(-1848411647866610862177/4722366482869645213696:ℚ)⟩ node148 node3702
def node3814 : BoxExpr 3 := .mul ⟨(-262548147853981403345/590295810358705651712:ℚ),(-2049080452351148946723/4722366482869645213696:ℚ)⟩ node36 node3700
def node3815 : BoxExpr 3 := .add ⟨(-250314838388173293599/295147905179352825856:ℚ),(-974373025054439952225/1180591620717411303424:ℚ)⟩ node3813 node3814
def node3816 : BoxExpr 3 := .mul ⟨(-2285721894357491864953/2361183241434822606848:ℚ),(-1092748974505665861625/1180591620717411303424:ℚ)⟩ node3815 node461
def node3817 : BoxExpr 3 := .add ⟨(-2396915400845547760569/2361183241434822606848:ℚ),(-1107751997933943707751/1180591620717411303424:ℚ)⟩ node3812 node3816
def node3818 : BoxExpr 3 := .mul ⟨(20295874334985604623677/4722366482869645213696:ℚ),(10495615965226722907461/2361183241434822606848:ℚ)⟩ node3703 node514
def node3819 : BoxExpr 3 := .add ⟨(15724430546270620893771/4722366482869645213696:ℚ),(8310118016215391184211/2361183241434822606848:ℚ)⟩ node3816 node3818
def node3820 : BoxExpr 3 := .add ⟨(10930599744579525372633/4722366482869645213696:ℚ),(6094614020347503768709/2361183241434822606848:ℚ)⟩ node3817 node3819
def node3821 : BoxExpr 3 := .mul ⟨(626948119329223897/1180591620717411303424:ℚ),(4940585417334089791/4722366482869645213696:ℚ)⟩ node3706 node189
def node3822 : BoxExpr 3 := .add ⟨(-12712638300445926229/1180591620717411303424:ℚ),(-47585686654296696143/4722366482869645213696:ℚ)⟩ node518 node3821
def node3823 : BoxExpr 3 := .add ⟨(-26052224720221076355/1180591620717411303424:ℚ),(-100111958725927482077/4722366482869645213696:ℚ)⟩ node518 node3822
def node3824 : BoxExpr 3 := .add ⟨(10826390845698641067213/4722366482869645213696:ℚ),(12089116081969080055341/4722366482869645213696:ℚ)⟩ node3820 node3823
def node3825 : BoxExpr 3 := .add ⟨(1370632757754075777421/295147905179352825856:ℚ),(7170646780324131632471/1180591620717411303424:ℚ)⟩ node3824 node527
def node3826 : BoxExpr 3 := .mul ⟨(-2415325756334183537513/2361183241434822606848:ℚ),(-2413370838783322935303/2361183241434822606848:ℚ)⟩ node6 node3802
def node3827 : BoxExpr 3 := .mul ⟨(998343639949819917377/2361183241434822606848:ℚ),(1017078580206347599001/2361183241434822606848:ℚ)⟩ node86 node3803
def node3828 : BoxExpr 3 := .mul ⟨(18052096160378866378995/4722366482869645213696:ℚ),(18081353705286086258861/4722366482869645213696:ℚ)⟩ node3801 node3801
def node3829 : BoxExpr 3 := .inv ⟨(308338987805030842291/1180591620717411303424:ℚ),(1235354886236246855281/4722366482869645213696:ℚ)⟩ node3828
def node3830 : BoxExpr 3 := .mul ⟨(521481369208192941643/4722366482869645213696:ℚ),(33258033824299515985/295147905179352825856:ℚ)⟩ node3827 node3829
def node3831 : BoxExpr 3 := .neg ⟨(-33258033824299515985/295147905179352825856:ℚ),(-521481369208192941643/4722366482869645213696:ℚ)⟩ node3830
def node3832 : BoxExpr 3 := .mul ⟨(-112038001445608994475/2361183241434822606848:ℚ),(-215722175777920439531/4722366482869645213696:ℚ)⟩ node3800 node3831
def node3833 : BoxExpr 3 := .add ⟨(-631840939444948132997/590295810358705651712:ℚ),(-5042463853344566310137/4722366482869645213696:ℚ)⟩ node3826 node3832
def node3834 : BoxExpr 3 := .mul ⟨(-6266046381172590234573/2361183241434822606848:ℚ),(-3120743344438854982945/1180591620717411303424:ℚ)⟩ node11 node3833
def node3835 : BoxExpr 3 := .add ⟨(-4730743332644526576121/4722366482869645213696:ℚ),(-2340811974027383019377/2361183241434822606848:ℚ)⟩ node3834 node546
def node3836 : BoxExpr 3 := .neg ⟨(2340811974027383019377/2361183241434822606848:ℚ),(4730743332644526576121/4722366482869645213696:ℚ)⟩ node3835
def cert_iv24 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-2137/10240:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/10240:ℚ)],
    whole := node3726, centerValue := node3753, gradient := ![node3760, node3770, node3784],
    hessian := ![![node3790, node3798, node3806], ![node3807, node3825, node536], ![node3806, node536, node3836]] }
def node3837 : BoxExpr 3 := .var 2
def node3838 : BoxExpr 3 := .mul ⟨(-196095270879024536303/2361183241434822606848:ℚ),(-190658575173638755975/2361183241434822606848:ℚ)⟩ node13 node3837
def node3839 : BoxExpr 3 := .add ⟨(984496349838386767121/2361183241434822606848:ℚ),(989933045543772547449/2361183241434822606848:ℚ)⟩ node3838 node301
def node3840 : BoxExpr 3 := .mul ⟨(4130640789167685434717/4722366482869645213696:ℚ),(2091203418356293905467/2361183241434822606848:ℚ)⟩ node36 node3839
def node3841 : BoxExpr 3 := .mul ⟨(4905896400076952750411/4722366482869645213696:ℚ),(2493153229424411739335/2361183241434822606848:ℚ)⟩ node3840 node304
def node3842 : BoxExpr 3 := .add ⟨(-38128267078853036345/4722366482869645213696:ℚ),(-1394890905386208985/590295810358705651712:ℚ)⟩ node3837 node306
def node3843 : BoxExpr 3 := .mul ⟨(60307654972546701/590295810358705651712:ℚ),(1648463235951723899/4722366482869645213696:ℚ)⟩ node3842 node308
def node3844 : BoxExpr 3 := .mul ⟨(525790700078799167/4722366482869645213696:ℚ),(1799929982912337209/4722366482869645213696:ℚ)⟩ node3843 node37
def node3845 : BoxExpr 3 := .add ⟨(2453211095388515774789/2361183241434822606848:ℚ),(4988106388831735815879/4722366482869645213696:ℚ)⟩ node3841 node3844
def node3846 : BoxExpr 3 := .add ⟨(15620866445916417909385/4722366482869645213696:ℚ),(15829870385691526313121/4722366482869645213696:ℚ)⟩ node3845 node316
def node3847 : BoxExpr 3 := .add ⟨(10858920212954596557021/4722366482869645213696:ℚ),(692627959318298842741/295147905179352825856:ℚ)⟩ node3846 node323
def node3848 : BoxExpr 3 := .add ⟨(10858906045855147948085/4722366482869645213696:ℚ),(11082033181993332874921/4722366482869645213696:ℚ)⟩ node3847 node325
def node3849 : BoxExpr 3 := .mul ⟨(169/4096:ℚ),(25253507068515456123/590295810358705651712:ℚ)⟩ node3837 node3837
def node3850 : BoxExpr 3 := .neg ⟨(-25253507068515456123/590295810358705651712:ℚ),(-169/4096:ℚ)⟩ node3849
def node3851 : BoxExpr 3 := .add ⟨(565042303290190195589/590295810358705651712:ℚ),(3927/4096:ℚ)⟩ node12 node3850
def node3852 : BoxExpr 3 := .sqrt ⟨(4620248334850462415041/4722366482869645213696:ℚ),(577989804170135285359/590295810358705651712:ℚ)⟩ node3851
def node3853 : BoxExpr 3 := .mul ⟨(11437749211489700735975/4722366482869645213696:ℚ),(11463995745373784832235/4722366482869645213696:ℚ)⟩ node11 node3852
def node3854 : BoxExpr 3 := .neg ⟨(13/64:ℚ),(244188774675730189517/1180591620717411303424:ℚ)⟩ node3837
def node3855 : BoxExpr 3 := .add ⟨(841171529761155553689/4722366482869645213696:ℚ),(429347968315589813863/2361183241434822606848:ℚ)⟩ node332 node3854
def node3856 : BoxExpr 3 := .mul ⟨(600596472249465065333/4722366482869645213696:ℚ),(613108898754662254197/4722366482869645213696:ℚ)⟩ node3855 node335
def node3857 : BoxExpr 3 := .neg ⟨(-613108898754662254197/4722366482869645213696:ℚ),(-600596472249465065333/4722366482869645213696:ℚ)⟩ node3856
def node3858 : BoxExpr 3 := .add ⟨(5412320156367519240889/2361183241434822606848:ℚ),(5431699636562159883451/2361183241434822606848:ℚ)⟩ node3853 node3857
def node3859 : BoxExpr 3 := .mul ⟨(18729209842338229125/590295810358705651712:ℚ),(156141780664771139339/4722366482869645213696:ℚ)⟩ node3855 node3855
def node3860 : BoxExpr 3 := .mul ⟨(123762618638171018057/4722366482869645213696:ℚ),(128973110829100961095/4722366482869645213696:ℚ)⟩ node3859 node340
def node3861 : BoxExpr 3 := .add ⟨(10948402931373209499835/4722366482869645213696:ℚ),(10992372383953420727997/4722366482869645213696:ℚ)⟩ node3858 node3860
def node3862 : BoxExpr 3 := .neg ⟨(-10992372383953420727997/4722366482869645213696:ℚ),(-10948402931373209499835/4722366482869645213696:ℚ)⟩ node3861
def node3863 : BoxExpr 3 := .add ⟨(-16683292262284097489/590295810358705651712:ℚ),(66815125310061687543/2361183241434822606848:ℚ)⟩ node3848 node3862
def node3864 : BoxExpr 3 := .var 2
def node3865 : BoxExpr 3 := .mul ⟨(-96684080411448317051/1180591620717411303424:ℚ),(-386736321645793268203/4722366482869645213696:ℚ)⟩ node51 node3864
def node3866 : BoxExpr 3 := .add ⟨(493611729947257334661/1180591620717411303424:ℚ),(1974446919789029338645/4722366482869645213696:ℚ)⟩ node3865 node301
def node3867 : BoxExpr 3 := .mul ⟨(1039120423189272758703/1180591620717411303424:ℚ),(519560211594636379353/590295810358705651712:ℚ)⟩ node68 node3866
def node3868 : BoxExpr 3 := .mul ⟨(4945951311684638578787/4722366482869645213696:ℚ),(1236487827921159644701/1180591620717411303424:ℚ)⟩ node3867 node349
def node3869 : BoxExpr 3 := .add ⟨(-24643697160971354113/4722366482869645213696:ℚ),(-24643697160971354111/4722366482869645213696:ℚ)⟩ node3864 node351
def node3870 : BoxExpr 3 := .mul ⟨(1065462237866048753/4722366482869645213696:ℚ),(532731118933024377/2361183241434822606848:ℚ)⟩ node3869 node308
def node3871 : BoxExpr 3 := .mul ⟨(581125655140564599/2361183241434822606848:ℚ),(72640706892570575/295147905179352825856:ℚ)⟩ node3870 node69
def node3872 : BoxExpr 3 := .add ⟨(4947113562994919707985/4722366482869645213696:ℚ),(1236778390748729927001/1180591620717411303424:ℚ)⟩ node3868 node3871
def node3873 : BoxExpr 3 := .add ⟨(15726116075911181659881/4722366482869645213696:ℚ),(15726116075911181659953/4722366482869645213696:ℚ)⟩ node3872 node358
def node3874 : BoxExpr 3 := .add ⟨(1371403930141362321133/590295810358705651712:ℚ),(10971231441130898569141/4722366482869645213696:ℚ)⟩ node3873 node361
def node3875 : BoxExpr 3 := .add ⟨(171425269906741405627/73786976294838206464:ℚ),(5485608637015724980103/2361183241434822606848:ℚ)⟩ node3874 node325
def node3876 : BoxExpr 3 := .mul ⟨(24802454677335698309/590295810358705651712:ℚ),(99209818709342793237/2361183241434822606848:ℚ)⟩ node3864 node3864
def node3877 : BoxExpr 3 := .neg ⟨(-99209818709342793237/2361183241434822606848:ℚ),(-24802454677335698309/590295810358705651712:ℚ)⟩ node3876
def node3878 : BoxExpr 3 := .add ⟨(2261973422725479813611/2361183241434822606848:ℚ),(565493355681369953403/590295810358705651712:ℚ)⟩ node12 node3877
def node3879 : BoxExpr 3 := .sqrt ⟨(1155523013434865417855/1180591620717411303424:ℚ),(2311046026869730835711/2361183241434822606848:ℚ)⟩ node3878
def node3880 : BoxExpr 3 := .mul ⟨(11450788218440091539237/4722366482869645213696:ℚ),(11450788218440091539251/4722366482869645213696:ℚ)⟩ node50 node3879
def node3881 : BoxExpr 3 := .neg ⟨(967992895267908721049/4722366482869645213696:ℚ),(483996447633954360525/2361183241434822606848:ℚ)⟩ node3864
def node3882 : BoxExpr 3 := .add ⟨(424966866598083795353/2361183241434822606848:ℚ),(212483433299041897677/1180591620717411303424:ℚ)⟩ node332 node3881
def node3883 : BoxExpr 3 := .mul ⟨(606852685502063659763/4722366482869645213696:ℚ),(303426342751031829883/2361183241434822606848:ℚ)⟩ node3882 node335
def node3884 : BoxExpr 3 := .neg ⟨(-303426342751031829883/2361183241434822606848:ℚ),(-606852685502063659763/4722366482869645213696:ℚ)⟩ node3883
def node3885 : BoxExpr 3 := .add ⟨(10843935532938027879471/4722366482869645213696:ℚ),(169436492702156685617/73786976294838206464:ℚ)⟩ node3880 node3884
def node3886 : BoxExpr 3 := .mul ⟨(76485735853541839339/2361183241434822606848:ℚ),(19121433963385459835/590295810358705651712:ℚ)⟩ node3882 node3882
def node3887 : BoxExpr 3 := .mul ⟨(126354435630051118587/4722366482869645213696:ℚ),(63177217815025559295/2361183241434822606848:ℚ)⟩ node3886 node340
def node3888 : BoxExpr 3 := .add ⟨(5485144984284039499029/2361183241434822606848:ℚ),(5485144984284039499039/2361183241434822606848:ℚ)⟩ node3885 node3887
def node3889 : BoxExpr 3 := .neg ⟨(-5485144984284039499039/2361183241434822606848:ℚ),(-5485144984284039499029/2361183241434822606848:ℚ)⟩ node3888
def node3890 : BoxExpr 3 := .add ⟨(463652731685481025/2361183241434822606848:ℚ),(231826365842740537/1180591620717411303424:ℚ)⟩ node3875 node3889
def node3891 : BoxExpr 3 := .mul ⟨(1119601116488537049445/4722366482869645213696:ℚ),(559800558244268524725/2361183241434822606848:ℚ)⟩ node78 node3866
def node3892 : BoxExpr 3 := .mul ⟨(325257515089081389/1152921504606846976:ℚ),(166531847725609671169/590295810358705651712:ℚ)⟩ node3891 node349
def node3893 : BoxExpr 3 := .add ⟨(5211486119086248356937/4722366482869645213696:ℚ),(5211486119086248357365/4722366482869645213696:ℚ)⟩ node3892 node385
def node3894 : BoxExpr 3 := .add ⟨(2857620058573494508175/4722366482869645213696:ℚ),(2857620058573494508605/4722366482869645213696:ℚ)⟩ node3893 node387
def node3895 : BoxExpr 3 := .mul ⟨(2859028160978090970067/4722366482869645213696:ℚ),(714757040244522742519/1180591620717411303424:ℚ)⟩ node77 node3879
def node3896 : BoxExpr 3 := .neg ⟨(-714757040244522742519/1180591620717411303424:ℚ),(-2859028160978090970067/4722366482869645213696:ℚ)⟩ node3895
def node3897 : BoxExpr 3 := .add ⟨(-1408102404596461901/4722366482869645213696:ℚ),(-704051202298230731/2361183241434822606848:ℚ)⟩ node3894 node3896
def node3898 : BoxExpr 3 := .mul ⟨(-1883116010628219968657/4722366482869645213696:ℚ),(-941558005314109984323/2361183241434822606848:ℚ)⟩ node98 node3866
def node3899 : BoxExpr 3 := .mul ⟨(-1018878934544845070405/2361183241434822606848:ℚ),(-1018878934544845070401/2361183241434822606848:ℚ)⟩ node68 node3864
def node3900 : BoxExpr 3 := .add ⟨(-3920873879717910109467/4722366482869645213696:ℚ),(-490109234964738763681/590295810358705651712:ℚ)⟩ node3898 node3899
def node3901 : BoxExpr 3 := .mul ⟨(-2332796429987084953381/2361183241434822606848:ℚ),(-291599553748385619171/295147905179352825856:ℚ)⟩ node3900 node349
def node3902 : BoxExpr 3 := .mul ⟨(4702692584315994102269/4722366482869645213696:ℚ),(1175673146078998525573/1180591620717411303424:ℚ)⟩ node3867 node399
def node3903 : BoxExpr 3 := .add ⟨(37099724341824195507/4722366482869645213696:ℚ),(9274931085456048889/1180591620717411303424:ℚ)⟩ node3901 node3902
def node3904 : BoxExpr 3 := .mul ⟨(552543916582646281/4722366482869645213696:ℚ),(552543916582646283/4722366482869645213696:ℚ)⟩ node3870 node103
def node3905 : BoxExpr 3 := .add ⟨(-27701521137295889313/1180591620717411303424:ℚ),(-865672535540496541/36893488147419103232:ℚ)⟩ node403 node3904
def node3906 : BoxExpr 3 := .add ⟨(-73706360207359361745/4722366482869645213696:ℚ),(-18426590051839840423/1180591620717411303424:ℚ)⟩ node3903 node3905
def node3907 : BoxExpr 3 := .add ⟨(248210874417309468529/4722366482869645213696:ℚ),(124105437208654734349/2361183241434822606848:ℚ)⟩ node3906 node409
def node3908 : BoxExpr 3 := .add ⟨(-483996447633954360525/1180591620717411303424:ℚ),(-967992895267908721049/2361183241434822606848:ℚ)⟩ node3864 node3864
def node3909 : BoxExpr 3 := .neg ⟨(967992895267908721049/2361183241434822606848:ℚ),(483996447633954360525/1180591620717411303424:ℚ)⟩ node3908
def node3910 : BoxExpr 3 := .mul ⟨(1155523013434865417855/590295810358705651712:ℚ),(2311046026869730835711/1180591620717411303424:ℚ)⟩ node86 node3879
def node3911 : BoxExpr 3 := .inv ⟨(2412408162715886134389/4722366482869645213696:ℚ),(2412408162715886134391/4722366482869645213696:ℚ)⟩ node3910
def node3912 : BoxExpr 3 := .mul ⟨(247248278004914306449/1180591620717411303424:ℚ),(988993112019657225799/4722366482869645213696:ℚ)⟩ node3909 node3911
def node3913 : BoxExpr 3 := .mul ⟨(2450135251216146979329/4722366482869645213696:ℚ),(2450135251216146979339/4722366482869645213696:ℚ)⟩ node50 node3912
def node3914 : BoxExpr 3 := .add ⟨(5821904919985073661907/4722366482869645213696:ℚ),(2910952459992536830959/2361183241434822606848:ℚ)⟩ node3913 node335
def node3915 : BoxExpr 3 := .mul ⟨(-212483433299041897677/1180591620717411303424:ℚ),(-424966866598083795353/2361183241434822606848:ℚ)⟩ node422 node3882
def node3916 : BoxExpr 3 := .mul ⟨(-212483433299041897677/1180591620717411303424:ℚ),(-424966866598083795353/2361183241434822606848:ℚ)⟩ node3882 node422
def node3917 : BoxExpr 3 := .add ⟨(-212483433299041897677/590295810358705651712:ℚ),(-424966866598083795353/1180591620717411303424:ℚ)⟩ node3915 node3916
def node3918 : BoxExpr 3 := .mul ⟨(-702045263620034429925/2361183241434822606848:ℚ),(-1404090527240068859845/4722366482869645213696:ℚ)⟩ node3917 node340
def node3919 : BoxExpr 3 := .add ⟨(4417814392745004802057/4722366482869645213696:ℚ),(4417814392745004802073/4722366482869645213696:ℚ)⟩ node3914 node3918
def node3920 : BoxExpr 3 := .neg ⟨(-4417814392745004802073/4722366482869645213696:ℚ),(-4417814392745004802057/4722366482869645213696:ℚ)⟩ node3919
def node3921 : BoxExpr 3 := .add ⟨(42805654567314805763/2361183241434822606848:ℚ),(85611309134629611561/4722366482869645213696:ℚ)⟩ node414 node3920
def node3922 : BoxExpr 3 := .mul ⟨(8872231459999119199981/4722366482869645213696:ℚ),(8938207830433962943017/4722366482869645213696:ℚ)⟩ node112 node3839
def node3923 : BoxExpr 3 := .mul ⟨(10537408262273419295923/4722366482869645213696:ℚ),(10656219056503212739751/4722366482869645213696:ℚ)⟩ node3922 node304
def node3924 : BoxExpr 3 := .add ⟨(10931809590568101729323/2361183241434822606848:ℚ),(2811410541822751947127/295147905179352825856:ℚ)⟩ node3923 node448
def node3925 : BoxExpr 3 := .mul ⟨(22731621807464275082001/4722366482869645213696:ℚ),(22749678692136524831731/4722366482869645213696:ℚ)⟩ node111 node3852
def node3926 : BoxExpr 3 := .neg ⟨(-22749678692136524831731/4722366482869645213696:ℚ),(-22731621807464275082001/4722366482869645213696:ℚ)⟩ node3925
def node3927 : BoxExpr 3 := .add ⟨(-886059511000321373085/4722366482869645213696:ℚ),(22250946861699756072031/4722366482869645213696:ℚ)⟩ node3924 node3926
def node3928 : BoxExpr 3 := .mul ⟨(-274862097220243899985/2361183241434822606848:ℚ),(-64381180177158374073/590295810358705651712:ℚ)⟩ node131 node3839
def node3929 : BoxExpr 3 := .mul ⟨(-567618412553571160563/4722366482869645213696:ℚ),(-530441861907458373331/4722366482869645213696:ℚ)⟩ node118 node3837
def node3930 : BoxExpr 3 := .add ⟨(-1117342606994058960533/4722366482869645213696:ℚ),(-1045491303324725365915/4722366482869645213696:ℚ)⟩ node3928 node3929
def node3931 : BoxExpr 3 := .mul ⟨(-1332106816844399333449/4722366482869645213696:ℚ),(-155214175084624938551/590295810358705651712:ℚ)⟩ node3930 node304
def node3932 : BoxExpr 3 := .mul ⟨(544413435991624497119/2361183241434822606848:ℚ),(1150552937152941204067/4722366482869645213696:ℚ)⟩ node118 node3839
def node3933 : BoxExpr 3 := .mul ⟨(1221107745370342343685/4722366482869645213696:ℚ),(1313268150622772941957/4722366482869645213696:ℚ)⟩ node3932 node461
def node3934 : BoxExpr 3 := .add ⟨(-27749767868514247441/1180591620717411303424:ℚ),(71554749945773433549/4722366482869645213696:ℚ)⟩ node3931 node3933
def node3935 : BoxExpr 3 := .add ⟨(-2868299796368527831723/4722366482869645213696:ℚ),(1485128630517433206453/4722366482869645213696:ℚ)⟩ node3934 node476
def node3936 : BoxExpr 3 := .add ⟨(-244188774675730189517/590295810358705651712:ℚ),(-13/32:ℚ)⟩ node3837 node3837
def node3937 : BoxExpr 3 := .neg ⟨(13/32:ℚ),(244188774675730189517/590295810358705651712:ℚ)⟩ node3936
def node3938 : BoxExpr 3 := .mul ⟨(4620248334850462415041/2361183241434822606848:ℚ),(577989804170135285359/295147905179352825856:ℚ)⟩ node86 node3852
def node3939 : BoxExpr 3 := .inv ⟨(150715956065754655515/295147905179352825856:ℚ),(2413370838783322935305/4722366482869645213696:ℚ)⟩ node3938
def node3940 : BoxExpr 3 := .mul ⟨(979653714427405260847/4722366482869645213696:ℚ),(998343639949819917379/4722366482869645213696:ℚ)⟩ node3937 node3939
def node3941 : BoxExpr 3 := .mul ⟨(295756068134283872963/2361183241434822606848:ℚ),(316134082289970635747/2361183241434822606848:ℚ)⟩ node117 node3940
def node3942 : BoxExpr 3 := .neg ⟨(-316134082289970635747/2361183241434822606848:ℚ),(-295756068134283872963/2361183241434822606848:ℚ)⟩ node3941
def node3943 : BoxExpr 3 := .add ⟨(600662427526422704453/4722366482869645213696:ℚ),(90272876307586619475/590295810358705651712:ℚ)⟩ node479 node3942
def node3944 : BoxExpr 3 := .add ⟨(-1434149898184263915861/2361183241434822606848:ℚ),(1485128630517433206453/4722366482869645213696:ℚ)⟩ node3934 node492
def node3945 : BoxExpr 3 := .mul ⟨(-2034145224152601687667/4722366482869645213696:ℚ),(-61792652590361000065/147573952589676412928:ℚ)⟩ node175 node3839
def node3946 : BoxExpr 3 := .mul ⟨(903716992117215911793/4722366482869645213696:ℚ),(14733855002616990503/73786976294838206464:ℚ)⟩ node148 node3837
def node3947 : BoxExpr 3 := .add ⟨(-565214116017692887937/2361183241434822606848:ℚ),(-32324942585127019059/147573952589676412928:ℚ)⟩ node3945 node3946
def node3948 : BoxExpr 3 := .add ⟨(-226711239918169864081/4722366482869645213696:ℚ),(-2857232579893038053/147573952589676412928:ℚ)⟩ node3947 node3946
def node3949 : BoxExpr 3 := .mul ⟨(-16892960262357893663/295147905179352825856:ℚ),(-108591670829488249665/4722366482869645213696:ℚ)⟩ node3948 node304
def node3950 : BoxExpr 3 := .mul ⟨(-1911377618363962954221/4722366482869645213696:ℚ),(-1855040893919430499069/4722366482869645213696:ℚ)⟩ node148 node3839
def node3951 : BoxExpr 3 := .mul ⟨(-515841351720531180227/1180591620717411303424:ℚ),(-2012316969258918701221/4722366482869645213696:ℚ)⟩ node36 node3837
def node3952 : BoxExpr 3 := .add ⟨(-3974743025246087675129/4722366482869645213696:ℚ),(-1933678931589174600145/2361183241434822606848:ℚ)⟩ node3950 node3951
def node3953 : BoxExpr 3 := .mul ⟨(-4536865061491578859891/4722366482869645213696:ℚ),(-1084300167997376394003/1180591620717411303424:ℚ)⟩ node3952 node461
def node3954 : BoxExpr 3 := .add ⟨(-4807152425689305158499/4722366482869645213696:ℚ),(-4445792342818993825677/4722366482869645213696:ℚ)⟩ node3949 node3953
def node3955 : BoxExpr 3 := .mul ⟨(20368664584375677781725/4722366482869645213696:ℚ),(21065352631177300369507/4722366482869645213696:ℚ)⟩ node3840 node514
def node3956 : BoxExpr 3 := .add ⟨(7915899761442049460917/2361183241434822606848:ℚ),(16728151959187794793495/4722366482869645213696:ℚ)⟩ node3953 node3955
def node3957 : BoxExpr 3 := .add ⟨(11024647097194793763335/4722366482869645213696:ℚ),(6141179808184400483909/2361183241434822606848:ℚ)⟩ node3954 node3956
def node3958 : BoxExpr 3 := .mul ⟨(487819514207770255/2361183241434822606848:ℚ),(1692425062010893533/2361183241434822606848:ℚ)⟩ node3843 node189
def node3959 : BoxExpr 3 := .add ⟨(-26191353325342529997/2361183241434822606848:ℚ),(-12285355486902249717/1180591620717411303424:ℚ)⟩ node518 node3958
def node3960 : BoxExpr 3 := .add ⟨(-52870526164892830249/2361183241434822606848:ℚ),(-50833847009619892401/2361183241434822606848:ℚ)⟩ node518 node3959
def node3961 : BoxExpr 3 := .add ⟨(10918906044865008102837/4722366482869645213696:ℚ),(1522586490293695147877/590295810358705651712:ℚ)⟩ node3957 node3960
def node3962 : BoxExpr 3 := .add ⟨(2752829915403947434295/590295810358705651712:ℚ),(28774162961677007657559/4722366482869645213696:ℚ)⟩ node3961 node527
def node3963 : BoxExpr 3 := .mul ⟨(-2413370838783322935305/2361183241434822606848:ℚ),(-150715956065754655515/147573952589676412928:ℚ)⟩ node6 node3939
def node3964 : BoxExpr 3 := .mul ⟨(979653714427405260847/2361183241434822606848:ℚ),(998343639949819917379/2361183241434822606848:ℚ)⟩ node86 node3940
def node3965 : BoxExpr 3 := .mul ⟨(4520338426321521564711/1180591620717411303424:ℚ),(18110090994364352299011/4722366482869645213696:ℚ)⟩ node3938 node3938
def node3966 : BoxExpr 3 := .inv ⟨(1231398848601608530385/4722366482869645213696:ℚ),(1233355951220123369167/4722366482869645213696:ℚ)⟩ node3965
def node3967 : BoxExpr 3 := .mul ⟨(255453374986927167585/2361183241434822606848:ℚ),(260740684604096470823/2361183241434822606848:ℚ)⟩ node3964 node3966
def node3968 : BoxExpr 3 := .neg ⟨(-260740684604096470823/2361183241434822606848:ℚ),(-255453374986927167585/2361183241434822606848:ℚ)⟩ node3967
def node3969 : BoxExpr 3 := .mul ⟨(-215722175777920439533/4722366482869645213696:ℚ),(-103777933588439161831/2361183241434822606848:ℚ)⟩ node3937 node3968
def node3970 : BoxExpr 3 := .add ⟨(-5042463853344566310143/4722366482869645213696:ℚ),(-2515233230640513650071/2361183241434822606848:ℚ)⟩ node3963 node3969
def node3971 : BoxExpr 3 := .mul ⟨(-12501687690655046373897/4722366482869645213696:ℚ),(-12453272991181043853521/4722366482869645213696:ℚ)⟩ node11 node3970
def node3972 : BoxExpr 3 := .add ⟨(-587542282619299060109/590295810358705651712:ℚ),(-4651923561480389960495/4722366482869645213696:ℚ)⟩ node3971 node546
def node3973 : BoxExpr 3 := .neg ⟨(4651923561480389960495/4722366482869645213696:ℚ),(587542282619299060109/590295810358705651712:ℚ)⟩ node3972
def cert_iv25 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-2099/10240:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/10240:ℚ)],
    whole := node3863, centerValue := node3890, gradient := ![node3897, node3907, node3921],
    hessian := ![![node3927, node3935, node3943], ![node3944, node3962, node536], ![node3943, node536, node3973]] }
def node3974 : BoxExpr 3 := .var 2
def node3975 : BoxExpr 3 := .mul ⟨(-385154073114609098687/4722366482869645213696:ℚ),(-353451666283438001461/4722366482869645213696:ℚ)⟩ node13 node3974
def node3976 : BoxExpr 3 := .add ⟨(1976029168320213508161/4722366482869645213696:ℚ),(2007731575151384605387/4722366482869645213696:ℚ)⟩ node3975 node301
def node3977 : BoxExpr 3 := .mul ⟨(2072701103612135165531/2361183241434822606848:ℚ),(1060317955845224535977/1180591620717411303424:ℚ)⟩ node36 node3976
def node3978 : BoxExpr 3 := .mul ⟨(1230857075409747926651/1180591620717411303424:ℚ),(2528242936701066150463/2361183241434822606848:ℚ)⟩ node3977 node304
def node3979 : BoxExpr 3 := .add ⟨(-20603860208828962309/4722366482869645213696:ℚ),(58938500237006624261/4722366482869645213696:ℚ)⟩ node3974 node306
def node3980 : BoxExpr 3 := .mul ⟨(-1274093451741526979/2361183241434822606848:ℚ),(6959384376061461/36893488147419103232:ℚ)⟩ node3979 node308
def node3981 : BoxExpr 3 := .mul ⟨(-695580876420894367/1180591620717411303424:ℚ),(972651226894450675/4722366482869645213696:ℚ)⟩ node3980 node37
def node3982 : BoxExpr 3 := .add ⟨(307540373633331758071/295147905179352825856:ℚ),(5057458524629026751601/4722366482869645213696:ℚ)⟩ node3978 node3981
def node3983 : BoxExpr 3 := .add ⟨(15635090233272694488943/4722366482869645213696:ℚ),(15899222521488817248843/4722366482869645213696:ℚ)⟩ node3982 node316
def node3984 : BoxExpr 3 := .add ⟨(10873144000310873136579/4722366482869645213696:ℚ),(5575699742445036209789/2361183241434822606848:ℚ)⟩ node3983 node323
def node3985 : BoxExpr 3 := .add ⟨(10873129833211424527643/4722366482869645213696:ℚ),(11151385317790623810643/4722366482869645213696:ℚ)⟩ node3984 node325
def node3986 : BoxExpr 3 := .mul ⟨(10462942798292231127/295147905179352825856:ℚ),(169/4096:ℚ)⟩ node3974 node3974
def node3987 : BoxExpr 3 := .neg ⟨(-169/4096:ℚ),(-10462942798292231127/295147905179352825856:ℚ)⟩ node3986
def node3988 : BoxExpr 3 := .add ⟨(3927/4096:ℚ),(284684962381060594729/295147905179352825856:ℚ)⟩ node12 node3987
def node3989 : BoxExpr 3 := .sqrt ⟨(4623918433361082282871/4722366482869645213696:ℚ),(2318953836992298886677/2361183241434822606848:ℚ)⟩ node3988
def node3990 : BoxExpr 3 := .mul ⟨(5723417399043350691457/2361183241434822606848:ℚ),(2874669752951710769479/1180591620717411303424:ℚ)⟩ node11 node3989
def node3991 : BoxExpr 3 := .neg ⟨(889133064352800387891/4722366482869645213696:ℚ),(13/64:ℚ)⟩ node3974
def node3992 : BoxExpr 3 := .add ⟨(192768475570264814387/1180591620717411303424:ℚ),(420585764880577776845/2361183241434822606848:ℚ)⟩ node332 node3991
def node3993 : BoxExpr 3 := .mul ⟨(550546766228676309889/4722366482869645213696:ℚ),(600596472249465065335/4722366482869645213696:ℚ)⟩ node3992 node335
def node3994 : BoxExpr 3 := .neg ⟨(-600596472249465065335/4722366482869645213696:ℚ),(-550546766228676309889/4722366482869645213696:ℚ)⟩ node3993
def node3995 : BoxExpr 3 := .add ⟨(10846238325837236317579/4722366482869645213696:ℚ),(10948132245578166768027/4722366482869645213696:ℚ)⟩ node3990 node3994
def node3996 : BoxExpr 3 := .mul ⟨(7868869412926825431/295147905179352825856:ℚ),(74916839369352916501/2361183241434822606848:ℚ)⟩ node3992 node3992
def node3997 : BoxExpr 3 := .mul ⟨(3249843067538778903/147573952589676412928:ℚ),(30940654659542754515/1180591620717411303424:ℚ)⟩ node3996 node340
def node3998 : BoxExpr 3 := .add ⟨(10950233303998477242475/4722366482869645213696:ℚ),(11071894864216337786087/4722366482869645213696:ℚ)⟩ node3995 node3997
def node3999 : BoxExpr 3 := .neg ⟨(-11071894864216337786087/4722366482869645213696:ℚ),(-10950233303998477242475/4722366482869645213696:ℚ)⟩ node3998
def node4000 : BoxExpr 3 := .add ⟨(-49691257751228314611/1180591620717411303424:ℚ),(25144001724018321021/590295810358705651712:ℚ)⟩ node3985 node3999
def node4001 : BoxExpr 3 := .var 2
def node4002 : BoxExpr 3 := .mul ⟨(-369232772071543453779/4722366482869645213696:ℚ),(-369232772071543453777/4722366482869645213696:ℚ)⟩ node51 node4001
def node4003 : BoxExpr 3 := .add ⟨(1991950469363279153069/4722366482869645213696:ℚ),(1991950469363279153071/4722366482869645213696:ℚ)⟩ node4002 node301
def node4004 : BoxExpr 3 := .mul ⟨(2096664533192929274943/2361183241434822606848:ℚ),(4193329066385858549901/4722366482869645213696:ℚ)⟩ node68 node4003
def node4005 : BoxExpr 3 := .mul ⟨(2494898682262585932359/2361183241434822606848:ℚ),(4989797364525171864739/4722366482869645213696:ℚ)⟩ node4004 node349
def node4006 : BoxExpr 3 := .add ⟨(19167320014088830975/4722366482869645213696:ℚ),(19167320014088830977/4722366482869645213696:ℚ)⟩ node4001 node351
def node4007 : BoxExpr 3 := .mul ⟨(-207173212918398369/1180591620717411303424:ℚ),(-828692851673593475/4722366482869645213696:ℚ)⟩ node4006 node308
def node4008 : BoxExpr 3 := .mul ⟨(-903973241329767157/4722366482869645213696:ℚ),(-451986620664883577/2361183241434822606848:ℚ)⟩ node4007 node69
def node4009 : BoxExpr 3 := .add ⟨(4988893391283842097561/4722366482869645213696:ℚ),(4988893391283842097585/4722366482869645213696:ℚ)⟩ node4005 node4008
def node4010 : BoxExpr 3 := .add ⟨(15767895904200104049457/4722366482869645213696:ℚ),(7883947952100052024767/2361183241434822606848:ℚ)⟩ node4009 node358
def node4011 : BoxExpr 3 := .add ⟨(688313204338738809915/295147905179352825856:ℚ),(5506505634709910479361/2361183241434822606848:ℚ)⟩ node4010 node361
def node4012 : BoxExpr 3 := .add ⟨(1376624637790046543713/590295810358705651712:ℚ),(11012997102320372349787/4722366482869645213696:ℚ)⟩ node4011 node325
def node4013 : BoxExpr 3 := .mul ⟨(180865281611139498639/4722366482869645213696:ℚ),(11304080100696218665/295147905179352825856:ℚ)⟩ node4001 node4001
def node4014 : BoxExpr 3 := .neg ⟨(-11304080100696218665/295147905179352825856:ℚ),(-180865281611139498639/4722366482869645213696:ℚ)⟩ node4013
def node4015 : BoxExpr 3 := .add ⟨(283843825078656607191/295147905179352825856:ℚ),(4541501201258505715057/4722366482869645213696:ℚ)⟩ node12 node4014
def node4016 : BoxExpr 3 := .sqrt ⟨(4631050966544786191039/4722366482869645213696:ℚ),(4631050966544786191041/4722366482869645213696:ℚ)⟩ node4015
def node4017 : BoxExpr 3 := .mul ⟨(11472983062681292947007/4722366482869645213696:ℚ),(11472983062681292947021/4722366482869645213696:ℚ)⟩ node50 node4016
def node4018 : BoxExpr 3 := .neg ⟨(924181878092848535961/4722366482869645213696:ℚ),(462090939046424267981/2361183241434822606848:ℚ)⟩ node4001
def node4019 : BoxExpr 3 := .add ⟨(403061358010553702809/2361183241434822606848:ℚ),(201530679005276851405/1180591620717411303424:ℚ)⟩ node332 node4018
def node4020 : BoxExpr 3 := .mul ⟨(575571619239070687611/4722366482869645213696:ℚ),(575571619239070687613/4722366482869645213696:ℚ)⟩ node4019 node335
def node4021 : BoxExpr 3 := .neg ⟨(-575571619239070687613/4722366482869645213696:ℚ),(-575571619239070687611/4722366482869645213696:ℚ)⟩ node4020
def node4022 : BoxExpr 3 := .add ⟨(5448705721721111129697/2361183241434822606848:ℚ),(5448705721721111129705/2361183241434822606848:ℚ)⟩ node4017 node4021
def node4023 : BoxExpr 3 := .mul ⟨(137607666758290600099/4722366482869645213696:ℚ),(137607666758290600101/4722366482869645213696:ℚ)⟩ node4019 node4019
def node4024 : BoxExpr 3 := .mul ⟨(113663932742348035681/4722366482869645213696:ℚ),(28415983185587008921/1180591620717411303424:ℚ)⟩ node4023 node340
def node4025 : BoxExpr 3 := .add ⟨(11011075376184570295075/4722366482869645213696:ℚ),(5505537688092285147547/2361183241434822606848:ℚ)⟩ node4022 node4024
def node4026 : BoxExpr 3 := .neg ⟨(-5505537688092285147547/2361183241434822606848:ℚ),(-11011075376184570295075/4722366482869645213696:ℚ)⟩ node4025
def node4027 : BoxExpr 3 := .add ⟨(960863067901027305/2361183241434822606848:ℚ),(240215766975256839/590295810358705651712:ℚ)⟩ node4012 node4026
def node4028 : BoxExpr 3 := .mul ⟨(564763212203063349739/2361183241434822606848:ℚ),(282381606101531674871/1180591620717411303424:ℚ)⟩ node78 node4003
def node4029 : BoxExpr 3 := .mul ⟨(1344065272826507217865/4722366482869645213696:ℚ),(672032636413253608937/2361183241434822606848:ℚ)⟩ node4028 node349
def node4030 : BoxExpr 3 := .add ⟨(2611648305053939102729/2361183241434822606848:ℚ),(5223296610107878205887/4722366482869645213696:ℚ)⟩ node4029 node385
def node4031 : BoxExpr 3 := .add ⟨(358678818699390544587/590295810358705651712:ℚ),(2869430549595124357127/4722366482869645213696:ℚ)⟩ node4030 node387
def node4032 : BoxExpr 3 := .mul ⟨(2864569760691893171717/4722366482869645213696:ℚ),(1432284880345946585863/2361183241434822606848:ℚ)⟩ node77 node4016
def node4033 : BoxExpr 3 := .neg ⟨(-1432284880345946585863/2361183241434822606848:ℚ),(-2864569760691893171717/4722366482869645213696:ℚ)⟩ node4032
def node4034 : BoxExpr 3 := .add ⟨(2430394451615592485/2361183241434822606848:ℚ),(2430394451615592705/2361183241434822606848:ℚ)⟩ node4031 node4033
def node4035 : BoxExpr 3 := .mul ⟨(-1899809908101856034417/4722366482869645213696:ℚ),(-1899809908101856034405/4722366482869645213696:ℚ)⟩ node98 node4003
def node4036 : BoxExpr 3 := .mul ⟨(-1945529666343848995799/4722366482869645213696:ℚ),(-121595604146490562237/295147905179352825856:ℚ)⟩ node68 node4001
def node4037 : BoxExpr 3 := .add ⟨(-480667446805713128777/590295810358705651712:ℚ),(-3845339574445705030197/4722366482869645213696:ℚ)⟩ node4035 node4036
def node4038 : BoxExpr 3 := .mul ⟨(-1143927949041857245775/1180591620717411303424:ℚ),(-4575711796167428983075/4722366482869645213696:ℚ)⟩ node4037 node349
def node4039 : BoxExpr 3 := .mul ⟨(4744382138974078934963/4722366482869645213696:ℚ),(4744382138974078934989/4722366482869645213696:ℚ)⟩ node4004 node399
def node4040 : BoxExpr 3 := .add ⟨(168670342806649951863/4722366482869645213696:ℚ),(84335171403324975957/2361183241434822606848:ℚ)⟩ node4038 node4039
def node4041 : BoxExpr 3 := .mul ⟨(-429756379564280443/4722366482869645213696:ℚ),(-429756379564280441/4722366482869645213696:ℚ)⟩ node4007 node103
def node4042 : BoxExpr 3 := .add ⟨(-13973548105666310497/590295810358705651712:ℚ),(-27947096211332620993/1180591620717411303424:ℚ)⟩ node403 node4041
def node4043 : BoxExpr 3 := .add ⟨(56881957961319467887/4722366482869645213696:ℚ),(28440978980659733971/2361183241434822606848:ℚ)⟩ node4040 node4042
def node4044 : BoxExpr 3 := .add ⟨(378799192585988298161/4722366482869645213696:ℚ),(94699798146497074583/1180591620717411303424:ℚ)⟩ node4043 node409
def node4045 : BoxExpr 3 := .add ⟨(-462090939046424267981/1180591620717411303424:ℚ),(-924181878092848535961/2361183241434822606848:ℚ)⟩ node4001 node4001
def node4046 : BoxExpr 3 := .neg ⟨(924181878092848535961/2361183241434822606848:ℚ),(462090939046424267981/1180591620717411303424:ℚ)⟩ node4045
def node4047 : BoxExpr 3 := .mul ⟨(4631050966544786191039/2361183241434822606848:ℚ),(4631050966544786191041/2361183241434822606848:ℚ)⟩ node86 node4016
def node4048 : BoxExpr 3 := .inv ⟨(2407741283742461703623/4722366482869645213696:ℚ),(2407741283742461703625/4722366482869645213696:ℚ)⟩ node4047
def node4049 : BoxExpr 3 := .mul ⟨(942404986839822901183/4722366482869645213696:ℚ),(942404986839822901185/4722366482869645213696:ℚ)⟩ node4046 node4048
def node4050 : BoxExpr 3 := .mul ⟨(2334717654871033216947/4722366482869645213696:ℚ),(1167358827435516608477/2361183241434822606848:ℚ)⟩ node50 node4049
def node4051 : BoxExpr 3 := .add ⟨(5706487323639959899525/4722366482869645213696:ℚ),(5706487323639959899533/4722366482869645213696:ℚ)⟩ node4050 node335
def node4052 : BoxExpr 3 := .mul ⟨(-201530679005276851405/1180591620717411303424:ℚ),(-403061358010553702809/2361183241434822606848:ℚ)⟩ node422 node4019
def node4053 : BoxExpr 3 := .mul ⟨(-201530679005276851405/1180591620717411303424:ℚ),(-403061358010553702809/2361183241434822606848:ℚ)⟩ node4019 node422
def node4054 : BoxExpr 3 := .add ⟨(-201530679005276851405/590295810358705651712:ℚ),(-403061358010553702809/1180591620717411303424:ℚ)⟩ node4052 node4053
def node4055 : BoxExpr 3 := .mul ⟨(-1331714726866869434085/4722366482869645213696:ℚ),(-41616085214589669815/147573952589676412928:ℚ)⟩ node4054 node340
def node4056 : BoxExpr 3 := .add ⟨(136711643649159077045/147573952589676412928:ℚ),(4374772596773090465453/4722366482869645213696:ℚ)⟩ node4051 node4055
def node4057 : BoxExpr 3 := .neg ⟨(-4374772596773090465453/4722366482869645213696:ℚ),(-136711643649159077045/147573952589676412928:ℚ)⟩ node4056
def node4058 : BoxExpr 3 := .add ⟨(64326552553271974073/2361183241434822606848:ℚ),(64326552553271974089/2361183241434822606848:ℚ)⟩ node414 node4057
def node4059 : BoxExpr 3 := .mul ⟨(8903937610294076478597/4722366482869645213696:ℚ),(9064007998929919032555/4722366482869645213696:ℚ)⟩ node112 node3976
def node4060 : BoxExpr 3 := .mul ⟨(5287532576471419096925/2361183241434822606848:ℚ),(84423431651913387079/36893488147419103232:ℚ)⟩ node4059 node304
def node4061 : BoxExpr 3 := .add ⟨(21901276071805622356573/4722366482869645213696:ℚ),(45132548864105731960393/4722366482869645213696:ℚ)⟩ node4060 node448
def node4062 : BoxExpr 3 := .mul ⟨(22749678692136524831725/4722366482869645213696:ℚ),(22818505756004221044903/4722366482869645213696:ℚ)⟩ node111 node3989
def node4063 : BoxExpr 3 := .neg ⟨(-22818505756004221044903/4722366482869645213696:ℚ),(-22749678692136524831725/4722366482869645213696:ℚ)⟩ node4062
def node4064 : BoxExpr 3 := .add ⟨(-458614842099299344165/2361183241434822606848:ℚ),(5595717542992301782167/1180591620717411303424:ℚ)⟩ node4061 node4063
def node4065 : BoxExpr 3 := .mul ⟨(-69682656050021187819/590295810358705651712:ℚ),(-516890042068020448317/4722366482869645213696:ℚ)⟩ node131 node3976
def node4066 : BoxExpr 3 := .mul ⟨(-557434512800485370147/4722366482869645213696:ℚ),(-245839401384033592255/2361183241434822606848:ℚ)⟩ node118 node3974
def node4067 : BoxExpr 3 := .add ⟨(-1114895761200654872699/4722366482869645213696:ℚ),(-1008568844836087632827/4722366482869645213696:ℚ)⟩ node4065 node4066
def node4068 : BoxExpr 3 := .mul ⟨(-664594831643350509705/2361183241434822606848:ℚ),(-1197861183690129192989/4722366482869645213696:ℚ)⟩ node4067 node304
def node4069 : BoxExpr 3 := .mul ⟨(8536858952370966971/36893488147419103232:ℚ),(1166746312391378667867/4722366482869645213696:ℚ)⟩ node118 node3976
def node4070 : BoxExpr 3 := .mul ⟨(1225471543347841494841/4722366482869645213696:ℚ),(1331751649525784724313/4722366482869645213696:ℚ)⟩ node4069 node461
def node4071 : BoxExpr 3 := .add ⟨(-103718119938859524569/4722366482869645213696:ℚ),(33472616458913882831/1180591620717411303424:ℚ)⟩ node4068 node4070
def node4072 : BoxExpr 3 := .add ⟨(-44703419450520786977/73786976294838206464:ℚ),(386866086601828826057/1180591620717411303424:ℚ)⟩ node4071 node476
def node4073 : BoxExpr 3 := .add ⟨(-13/32:ℚ),(-889133064352800387891/2361183241434822606848:ℚ)⟩ node3974 node3974
def node4074 : BoxExpr 3 := .neg ⟨(889133064352800387891/2361183241434822606848:ℚ),(13/32:ℚ)⟩ node4073
def node4075 : BoxExpr 3 := .mul ⟨(4623918433361082282871/2361183241434822606848:ℚ),(2318953836992298886677/1180591620717411303424:ℚ)⟩ node86 node3989
def node4076 : BoxExpr 3 := .inv ⟨(1202090833093882468011/2361183241434822606848:ℚ),(1205727648526037244121/2361183241434822606848:ℚ)⟩ node4075
def node4077 : BoxExpr 3 := .mul ⟨(113165582334228779215/590295810358705651712:ℚ),(979653714427405260849/4722366482869645213696:ℚ)⟩ node4074 node4076
def node4078 : BoxExpr 3 := .mul ⟨(273316231532775907639/2361183241434822606848:ℚ),(620431513918464749231/4722366482869645213696:ℚ)⟩ node117 node4077
def node4079 : BoxExpr 3 := .neg ⟨(-620431513918464749231/4722366482869645213696:ℚ),(-273316231532775907639/2361183241434822606848:ℚ)⟩ node4078
def node4080 : BoxExpr 3 := .add ⟨(153124769546974806679/1180591620717411303424:ℚ),(47941417728981805403/295147905179352825856:ℚ)⟩ node479 node4079
def node4081 : BoxExpr 3 := .add ⟨(-2861018844833330366527/4722366482869645213696:ℚ),(386866086601828826057/1180591620717411303424:ℚ)⟩ node4071 node492
def node4082 : BoxExpr 3 := .mul ⟨(-515693664000681081387/1180591620717411303424:ℚ),(-1984431270693492458925/4722366482869645213696:ℚ)⟩ node175 node3976
def node4083 : BoxExpr 3 := .mul ⟨(837676135000957825931/4722366482869645213696:ℚ),(463024262971759626005/2361183241434822606848:ℚ)⟩ node148 node3974
def node4084 : BoxExpr 3 := .add ⟨(-1225098521001766499617/4722366482869645213696:ℚ),(-1058382744749973206915/4722366482869645213696:ℚ)⟩ node4082 node4083
def node4085 : BoxExpr 3 := .add ⟨(-193711193000404336843/2361183241434822606848:ℚ),(-132334218806453954905/4722366482869645213696:ℚ)⟩ node4084 node4083
def node4086 : BoxExpr 3 := .mul ⟨(-461888769084184328109/4722366482869645213696:ℚ),(-157171247945865114829/4722366482869645213696:ℚ)⟩ node4085 node304
def node4087 : BoxExpr 3 := .mul ⟨(-969139583152064443905/2361183241434822606848:ℚ),(-1861670139972250135963/4722366482869645213696:ℚ)⟩ node148 node3976
def node4088 : BoxExpr 3 := .mul ⟨(-1013172815466199107527/2361183241434822606848:ℚ),(-233157879611249714901/590295810358705651712:ℚ)⟩ node36 node3974
def node4089 : BoxExpr 3 := .add ⟨(-247789049827282943929/295147905179352825856:ℚ),(-3726933176862247855171/4722366482869645213696:ℚ)⟩ node4087 node4088
def node4090 : BoxExpr 3 := .mul ⟨(-4525315878349622474011/4722366482869645213696:ℚ),(-261232242577208894553/295147905179352825856:ℚ)⟩ node4089 node461
def node4091 : BoxExpr 3 := .add ⟨(-623400580929225850265/590295810358705651712:ℚ),(-4336887129181207427677/4722366482869645213696:ℚ)⟩ node4086 node4090
def node4092 : BoxExpr 3 := .mul ⟨(20441454833765750939779/4722366482869645213696:ℚ),(21361835434072718587839/4722366482869645213696:ℚ)⟩ node3977 node514
def node4093 : BoxExpr 3 := .add ⟨(1989517369427016058221/590295810358705651712:ℚ),(17182119552837376274991/4722366482869645213696:ℚ)⟩ node4090 node4092
def node4094 : BoxExpr 3 := .add ⟨(341529197124447551989/147573952589676412928:ℚ),(6422616211828084423657/2361183241434822606848:ℚ)⟩ node4091 node4093
def node4095 : BoxExpr 3 := .mul ⟨(-5232285784830146551/4722366482869645213696:ℚ),(1829114830709484343/4722366482869645213696:ℚ)⟩ node3980 node189
def node4096 : BoxExpr 3 := .add ⟨(-58590631463930747055/4722366482869645213696:ℚ),(-50697157240921301591/4722366482869645213696:ℚ)⟩ node518 node4095
def node4097 : BoxExpr 3 := .add ⟨(-111948977143031347559/4722366482869645213696:ℚ),(-103223429312552087525/4722366482869645213696:ℚ)⟩ node518 node4096
def node4098 : BoxExpr 3 := .add ⟨(10816985330839290316089/4722366482869645213696:ℚ),(12742008994343616759789/4722366482869645213696:ℚ)⟩ node4094 node4097
def node4099 : BoxExpr 3 := .add ⟨(5480179652301465421903/1180591620717411303424:ℚ),(7333870008417765808583/1180591620717411303424:ℚ)⟩ node4098 node527
def node4100 : BoxExpr 3 := .mul ⟨(-1205727648526037244121/1180591620717411303424:ℚ),(-1202090833093882468011/1180591620717411303424:ℚ)⟩ node6 node4076
def node4101 : BoxExpr 3 := .mul ⟨(113165582334228779215/295147905179352825856:ℚ),(979653714427405260849/2361183241434822606848:ℚ)⟩ node86 node4077
def node4102 : BoxExpr 3 := .mul ⟨(9055045497182176149501/2361183241434822606848:ℚ),(9109918796193939031329/2361183241434822606848:ℚ)⟩ node4075 node4075
def node4103 : BoxExpr 3 := .inv ⟨(305995389440898748849/1180591620717411303424:ℚ),(1231398848601608530387/4722366482869645213696:ℚ)⟩ node4102
def node4104 : BoxExpr 3 := .mul ⟨(469298894960828622235/4722366482869645213696:ℚ),(510906749973854335173/4722366482869645213696:ℚ)⟩ node4101 node4103
def node4105 : BoxExpr 3 := .neg ⟨(-510906749973854335173/4722366482869645213696:ℚ),(-469298894960828622235/4722366482869645213696:ℚ)⟩ node4104
def node4106 : BoxExpr 3 := .mul ⟨(-207555867176878323665/4722366482869645213696:ℚ),(-44180091283421757015/1180591620717411303424:ℚ)⟩ node4074 node4105
def node4107 : BoxExpr 3 := .add ⟨(-5030466461281027300149/4722366482869645213696:ℚ),(-623135462188652112513/590295810358705651712:ℚ)⟩ node4100 node4106
def node4108 : BoxExpr 3 := .mul ⟨(-12471942777643677070121/4722366482869645213696:ℚ),(-12340924772443349521079/4722366482869645213696:ℚ)⟩ node11 node4107
def node4109 : BoxExpr 3 := .add ⟨(-583824168492877897137/590295810358705651712:ℚ),(-4539575342742695628053/4722366482869645213696:ℚ)⟩ node4108 node546
def node4110 : BoxExpr 3 := .neg ⟨(4539575342742695628053/4722366482869645213696:ℚ),(583824168492877897137/590295810358705651712:ℚ)⟩ node4109
def cert_iv26 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-501/2560:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/2560:ℚ)],
    whole := node4000, centerValue := node4027, gradient := ![node4034, node4044, node4058],
    hessian := ![![node4064, node4072, node4080], ![node4081, node4099, node536], ![node4080, node536, node4110]] }
def node4111 : BoxExpr 3 := .var 2
def node4112 : BoxExpr 3 := .mul ⟨(-178504099270424601507/2361183241434822606848:ℚ),(-81396545554899622743/1180591620717411303424:ℚ)⟩ node13 node4111
def node4113 : BoxExpr 3 := .add ⟨(1002087521446986701917/2361183241434822606848:ℚ),(508899264803806028969/1180591620717411303424:ℚ)⟩ node4112 node301
def node4114 : BoxExpr 3 := .mul ⟨(4204447879450609916437/4722366482869645213696:ℚ),(4300136810049208476883/4722366482869645213696:ℚ)⟩ node36 node4113
def node4115 : BoxExpr 3 := .mul ⟨(2496777953943573765685/2361183241434822606848:ℚ),(320416580497215070199/295147905179352825856:ℚ)⟩ node4114 node304
def node4116 : BoxExpr 3 := .add ⟨(49493767271267333831/4722366482869645213696:ℚ),(64518063858551460201/2361183241434822606848:ℚ)⟩ node4111 node306
def node4117 : BoxExpr 3 := .mul ⟨(-1394708761686620381/1180591620717411303424:ℚ),(-2139846943127560559/4722366482869645213696:ℚ)⟩ node4116 node308
def node4118 : BoxExpr 3 := .mul ⟨(-6091438529755123603/4722366482869645213696:ℚ),(-1166012447757142757/2361183241434822606848:ℚ)⟩ node4117 node37
def node4119 : BoxExpr 3 := .add ⟨(4987464469357392407767/4722366482869645213696:ℚ),(2562166631529963418835/2361183241434822606848:ℚ)⟩ node4115 node4118
def node4120 : BoxExpr 3 := .add ⟨(7850954362248389383787/2361183241434822606848:ℚ),(124735134843122791679/36893488147419103232:ℚ)⟩ node4119 node316
def node4121 : BoxExpr 3 := .add ⟨(5469981245767478707605/2361183241434822606848:ℚ),(11218274223320972505647/4722366482869645213696:ℚ)⟩ node4120 node323
def node4122 : BoxExpr 3 := .add ⟨(5469974162217754403137/2361183241434822606848:ℚ),(1402282507027690487089/590295810358705651712:ℚ)⟩ node4121 node325
def node4123 : BoxExpr 3 := .mul ⟨(17756432322826201989/590295810358705651712:ℚ),(167407084772675698033/4722366482869645213696:ℚ)⟩ node4111 node4111
def node4124 : BoxExpr 3 := .neg ⟨(-167407084772675698033/4722366482869645213696:ℚ),(-17756432322826201989/590295810358705651712:ℚ)⟩ node4123
def node4125 : BoxExpr 3 := .add ⟨(4554959398096969515663/4722366482869645213696:ℚ),(572539378035879449723/590295810358705651712:ℚ)⟩ node12 node4124
def node4126 : BoxExpr 3 := .sqrt ⟨(4637907673984597773353/4722366482869645213696:ℚ),(2325399221191780754023/2361183241434822606848:ℚ)⟩ node4125
def node4127 : BoxExpr 3 := .mul ⟨(11481466145649566243253/4722366482869645213696:ℚ),(5765319428150114310259/2361183241434822606848:ℚ)⟩ node11 node4126
def node4128 : BoxExpr 3 := .neg ⟨(409517718436352045875/2361183241434822606848:ℚ),(222283266088200096973/1180591620717411303424:ℚ)⟩ node4111
def node4129 : BoxExpr 3 := .add ⟨(700976274800962961407/4722366482869645213696:ℚ),(385536951140529628775/2361183241434822606848:ℚ)⟩ node332 node4128
def node4130 : BoxExpr 3 := .mul ⟨(125124265051971888611/1180591620717411303424:ℚ),(550546766228676309891/4722366482869645213696:ℚ)⟩ node4129 node335
def node4131 : BoxExpr 3 := .neg ⟨(-550546766228676309891/4722366482869645213696:ℚ),(-125124265051971888611/1180591620717411303424:ℚ)⟩ node4130
def node4132 : BoxExpr 3 := .add ⟨(5465459689710444966681/2361183241434822606848:ℚ),(5515070898046170533037/2361183241434822606848:ℚ)⟩ node4127 node4131
def node4133 : BoxExpr 3 := .mul ⟨(104051165790767939583/4722366482869645213696:ℚ),(62950955303414603449/2361183241434822606848:ℚ)⟩ node4129 node4129
def node4134 : BoxExpr 3 := .mul ⟨(85946262943174318095/4722366482869645213696:ℚ),(51997489080620462449/2361183241434822606848:ℚ)⟩ node4133 node340
def node4135 : BoxExpr 3 := .add ⟨(11016865642364064251457/4722366482869645213696:ℚ),(2783534193563395497743/1180591620717411303424:ℚ)⟩ node4132 node4134
def node4136 : BoxExpr 3 := .neg ⟨(-2783534193563395497743/1180591620717411303424:ℚ),(-11016865642364064251457/4722366482869645213696:ℚ)⟩ node4135
def node4137 : BoxExpr 3 := .add ⟨(-97094224909036592349/2361183241434822606848:ℚ),(201394413857459645255/4722366482869645213696:ℚ)⟩ node4122 node4136
def node4138 : BoxExpr 3 := .var 2
def node4139 : BoxExpr 3 := .mul ⟨(-170613546376371875349/2361183241434822606848:ℚ),(-42653386594092968837/590295810358705651712:ℚ)⟩ node51 node4138
def node4140 : BoxExpr 3 := .add ⟨(1009978074341039428075/2361183241434822606848:ℚ),(252494518585259857019/590295810358705651712:ℚ)⟩ node4139 node301
def node4141 : BoxExpr 3 := .mul ⟨(531535608023985821751/590295810358705651712:ℚ),(4252284864191886574023/4722366482869645213696:ℚ)⟩ node68 node4140
def node4142 : BoxExpr 3 := .mul ⟨(1264987762267506280553/1180591620717411303424:ℚ),(5059951049070025122233/4722366482869645213696:ℚ)⟩ node4141 node349
def node4143 : BoxExpr 3 := .add ⟨(22316236873546281779/1180591620717411303424:ℚ),(44632473747092563559/2361183241434822606848:ℚ)⟩ node4138 node351
def node4144 : BoxExpr 3 := .mul ⟨(-1929670497468510521/2361183241434822606848:ℚ),(-3859340994937021041/4722366482869645213696:ℚ)⟩ node4143 node308
def node4145 : BoxExpr 3 := .mul ⟨(-1052483130976800331/1180591620717411303424:ℚ),(-4209932523907201321/4722366482869645213696:ℚ)⟩ node4144 node69
def node4146 : BoxExpr 3 := .add ⟨(631967639568264740111/590295810358705651712:ℚ),(315983819784132370057/295147905179352825856:ℚ)⟩ node4142 node4145
def node4147 : BoxExpr 3 := .add ⟨(989671476841398742049/295147905179352825856:ℚ),(15834743629462379872861/4722366482869645213696:ℚ)⟩ node4146 node358
def node4148 : BoxExpr 3 := .add ⟨(11079858994682096781967/4722366482869645213696:ℚ),(11079858994682096782049/4722366482869645213696:ℚ)⟩ node4147 node361
def node4149 : BoxExpr 3 := .add ⟨(11079844827582648173031/4722366482869645213696:ℚ),(5539922413791324086557/2361183241434822606848:ℚ)⟩ node4148 node325
def node4150 : BoxExpr 3 := .mul ⟨(154469143763165737123/4722366482869645213696:ℚ),(38617285940791434281/1180591620717411303424:ℚ)⟩ node4138 node4138
def node4151 : BoxExpr 3 := .neg ⟨(-38617285940791434281/1180591620717411303424:ℚ),(-154469143763165737123/4722366482869645213696:ℚ)⟩ node4150
def node4152 : BoxExpr 3 := .add ⟨(1141974334776619869143/1180591620717411303424:ℚ),(4567897339106479476573/4722366482869645213696:ℚ)⟩ node12 node4151
def node4153 : BoxExpr 3 := .sqrt ⟨(1161122444323430208933/1180591620717411303424:ℚ),(2322244888646860417867/2361183241434822606848:ℚ)⟩ node4152
def node4154 : BoxExpr 3 := .mul ⟨(11506276422918298103123/4722366482869645213696:ℚ),(11506276422918298103137/4722366482869645213696:ℚ)⟩ node50 node4153
def node4155 : BoxExpr 3 := .neg ⟨(213521062653188059955/1180591620717411303424:ℚ),(854084250612752239821/4722366482869645213696:ℚ)⟩ node4138
def node4156 : BoxExpr 3 := .add ⟨(736025088541011109477/4722366482869645213696:ℚ),(736025088541011109479/4722366482869645213696:ℚ)⟩ node332 node4155
def node4157 : BoxExpr 3 := .mul ⟨(262760956609140966083/2361183241434822606848:ℚ),(525521913218281932169/4722366482869645213696:ℚ)⟩ node4156 node335
def node4158 : BoxExpr 3 := .neg ⟨(-525521913218281932169/4722366482869645213696:ℚ),(-262760956609140966083/2361183241434822606848:ℚ)⟩ node4157
def node4159 : BoxExpr 3 := .add ⟨(5490377254850008085477/2361183241434822606848:ℚ),(10980754509700016170971/4722366482869645213696:ℚ)⟩ node4154 node4158
def node4160 : BoxExpr 3 := .mul ⟨(57358205142160826695/2361183241434822606848:ℚ),(7169775642770103337/295147905179352825856:ℚ)⟩ node4156 node4156
def node4161 : BoxExpr 3 := .mul ⟨(23688938723712421425/1180591620717411303424:ℚ),(47377877447424842851/2361183241434822606848:ℚ)⟩ node4160 node340
def node4162 : BoxExpr 3 := .add ⟨(5537755132297432928327/2361183241434822606848:ℚ),(11075510264594865856673/4722366482869645213696:ℚ)⟩ node4159 node4161
def node4163 : BoxExpr 3 := .neg ⟨(-11075510264594865856673/4722366482869645213696:ℚ),(-5537755132297432928327/2361183241434822606848:ℚ)⟩ node4162
def node4164 : BoxExpr 3 := .add ⟨(2167281493891158179/2361183241434822606848:ℚ),(1083640746945579115/1180591620717411303424:ℚ)⟩ node4149 node4163
def node4165 : BoxExpr 3 := .mul ⟨(286351729268567534883/1180591620717411303424:ℚ),(572703458537135069769/2361183241434822606848:ℚ)⟩ node78 node4140
def node4166 : BoxExpr 3 := .mul ⟨(340740514615278743875/1180591620717411303424:ℚ),(1362962058461114975509/4722366482869645213696:ℚ)⟩ node4165 node349
def node4167 : BoxExpr 3 := .add ⟨(5242193395742485963093/4722366482869645213696:ℚ),(2621096697871242981761/2361183241434822606848:ℚ)⟩ node4166 node385
def node4168 : BoxExpr 3 := .add ⟨(2888327335229732114331/4722366482869645213696:ℚ),(1444163667614866057381/2361183241434822606848:ℚ)⟩ node4167 node387
def node4169 : BoxExpr 3 := .mul ⟨(2872882433380913784733/4722366482869645213696:ℚ),(2872882433380913784743/4722366482869645213696:ℚ)⟩ node77 node4153
def node4170 : BoxExpr 3 := .neg ⟨(-2872882433380913784743/4722366482869645213696:ℚ),(-2872882433380913784733/4722366482869645213696:ℚ)⟩ node4169
def node4171 : BoxExpr 3 := .add ⟨(3861225462204582397/1180591620717411303424:ℚ),(15444901848818330029/4722366482869645213696:ℚ)⟩ node4168 node4170
def node4172 : BoxExpr 3 := .mul ⟨(-120407509003729608727/295147905179352825856:ℚ),(-481630036014918434905/1180591620717411303424:ℚ)⟩ node98 node4140
def node4173 : BoxExpr 3 := .mul ⟨(-898982270975251581891/2361183241434822606848:ℚ),(-1797964541950503163775/4722366482869645213696:ℚ)⟩ node68 node4138
def node4174 : BoxExpr 3 := .add ⟨(-1862242343005088451707/2361183241434822606848:ℚ),(-3724484686010176903395/4722366482869645213696:ℚ)⟩ node4172 node4173
def node4175 : BoxExpr 3 := .mul ⟨(-4431902094076643505241/4722366482869645213696:ℚ),(-69248470219947554769/73786976294838206464:ℚ)⟩ node4174 node349
def node4176 : BoxExpr 3 := .mul ⟨(1202771356606753666819/1180591620717411303424:ℚ),(2405542713213507333651/2361183241434822606848:ℚ)⟩ node4141 node399
def node4177 : BoxExpr 3 := .add ⟨(379183332350371162035/4722366482869645213696:ℚ),(189591666175185581043/2361183241434822606848:ℚ)⟩ node4175 node4176
def node4178 : BoxExpr 3 := .mul ⟨(-15636225417182525/36893488147419103232:ℚ),(-2001436853399363199/4722366482869645213696:ℚ)⟩ node4144 node103
def node4179 : BoxExpr 3 := .add ⟨(-113360065319165566733/4722366482869645213696:ℚ),(-56680032659582783365/2361183241434822606848:ℚ)⟩ node403 node4178
def node4180 : BoxExpr 3 := .add ⟨(132911633515602797651/2361183241434822606848:ℚ),(66455816757801398839/1180591620717411303424:ℚ)⟩ node4177 node4179
def node4181 : BoxExpr 3 := .add ⟨(73467562706984303197/590295810358705651712:ℚ),(293870250827937212873/2361183241434822606848:ℚ)⟩ node4180 node409
def node4182 : BoxExpr 3 := .add ⟨(-854084250612752239821/2361183241434822606848:ℚ),(-213521062653188059955/590295810358705651712:ℚ)⟩ node4138 node4138
def node4183 : BoxExpr 3 := .neg ⟨(213521062653188059955/590295810358705651712:ℚ),(854084250612752239821/2361183241434822606848:ℚ)⟩ node4182
def node4184 : BoxExpr 3 := .mul ⟨(1161122444323430208933/590295810358705651712:ℚ),(2322244888646860417867/1180591620717411303424:ℚ)⟩ node86 node4153
def node4185 : BoxExpr 3 := .inv ⟨(2400774494924710021535/4722366482869645213696:ℚ),(2400774494924710021537/4722366482869645213696:ℚ)⟩ node4184
def node4186 : BoxExpr 3 := .mul ⟨(868405149336047453101/4722366482869645213696:ℚ),(54275321833502965819/295147905179352825856:ℚ)⟩ node4183 node4185
def node4187 : BoxExpr 3 := .mul ⟨(2151390179432899728003/4722366482869645213696:ℚ),(2151390179432899728013/4722366482869645213696:ℚ)⟩ node50 node4186
def node4188 : BoxExpr 3 := .add ⟨(5523159848201826410581/4722366482869645213696:ℚ),(172598745256307075331/147573952589676412928:ℚ)⟩ node4187 node335
def node4189 : BoxExpr 3 := .mul ⟨(-736025088541011109479/4722366482869645213696:ℚ),(-736025088541011109477/4722366482869645213696:ℚ)⟩ node422 node4156
def node4190 : BoxExpr 3 := .mul ⟨(-736025088541011109479/4722366482869645213696:ℚ),(-736025088541011109477/4722366482869645213696:ℚ)⟩ node4156 node422
def node4191 : BoxExpr 3 := .add ⟨(-736025088541011109479/2361183241434822606848:ℚ),(-736025088541011109477/2361183241434822606848:ℚ)⟩ node4189 node4190
def node4192 : BoxExpr 3 := .mul ⟨(-303978361567437588215/1180591620717411303424:ℚ),(-1215913446269750352855/4722366482869645213696:ℚ)⟩ node4191 node340
def node4193 : BoxExpr 3 := .add ⟨(4307246401932076057721/4722366482869645213696:ℚ),(4307246401932076057737/4722366482869645213696:ℚ)⟩ node4188 node4192
def node4194 : BoxExpr 3 := .neg ⟨(-4307246401932076057737/4722366482869645213696:ℚ),(-4307246401932076057721/4722366482869645213696:ℚ)⟩ node4193
def node4195 : BoxExpr 3 := .add ⟨(98089649973779177931/2361183241434822606848:ℚ),(196179299947558355897/4722366482869645213696:ℚ)⟩ node414 node4194
def node4196 : BoxExpr 3 := .mul ⟨(9030762211473905593047/4722366482869645213696:ℚ),(2297452041856468780523/1180591620717411303424:ℚ)⟩ node112 node4113
def node4197 : BoxExpr 3 := .mul ⟨(10725692715620513785541/4722366482869645213696:ℚ),(10956179446386614352471/4722366482869645213696:ℚ)⟩ node4196 node304
def node4198 : BoxExpr 3 := .add ⟨(2756487954310412243533/590295810358705651712:ℚ),(1415079033095232273961/147573952589676412928:ℚ)⟩ node4197 node448
def node4199 : BoxExpr 3 := .mul ⟨(713078304875131907653/147573952589676412928:ℚ),(22881928336527122619587/4722366482869645213696:ℚ)⟩ node111 node4126
def node4200 : BoxExpr 3 := .neg ⟨(-22881928336527122619587/4722366482869645213696:ℚ),(-713078304875131907653/147573952589676412928:ℚ)⟩ node4199
def node4201 : BoxExpr 3 := .add ⟨(-830024702043824671323/4722366482869645213696:ℚ),(175500182055025091577/36893488147419103232:ℚ)⟩ node4198 node4200
def node4202 : BoxExpr 3 := .mul ⟨(-565198302359851205135/4722366482869645213696:ℚ),(-524252444671034271245/4722366482869645213696:ℚ)⟩ node131 node4113
def node4203 : BoxExpr 3 := .mul ⟨(-516698913788142208483/4722366482869645213696:ℚ),(-226457871814337997845/2361183241434822606848:ℚ)⟩ node118 node4111
def node4204 : BoxExpr 3 := .add ⟨(-540948608073996706809/2361183241434822606848:ℚ),(-977168188299710266935/4722366482869645213696:ℚ)⟩ node4202 node4203
def node4205 : BoxExpr 3 := .mul ⟨(-1289848474169376788001/4722366482869645213696:ℚ),(-580283561550655124849/2361183241434822606848:ℚ)⟩ node4204 node304
def node4206 : BoxExpr 3 := .mul ⟨(554141120792211442243/2361183241434822606848:ℚ),(1182939687629816131667/4722366482869645213696:ℚ)⟩ node118 node4113
def node4207 : BoxExpr 3 := .mul ⟨(1242926735257838099461/4722366482869645213696:ℚ),(1350235148428796506669/4722366482869645213696:ℚ)⟩ node4206 node461
def node4208 : BoxExpr 3 := .add ⟨(-11730434727884672135/1180591620717411303424:ℚ),(189668025327486256971/4722366482869645213696:ℚ)⟩ node4205 node4207
def node4209 : BoxExpr 3 := .add ⟨(-2804222463806009530499/4722366482869645213696:ℚ),(1603241905899146029875/4722366482869645213696:ℚ)⟩ node4208 node476
def node4210 : BoxExpr 3 := .add ⟨(-222283266088200096973/590295810358705651712:ℚ),(-409517718436352045875/1180591620717411303424:ℚ)⟩ node4111 node4111
def node4211 : BoxExpr 3 := .neg ⟨(409517718436352045875/1180591620717411303424:ℚ),(222283266088200096973/590295810358705651712:ℚ)⟩ node4210
def node4212 : BoxExpr 3 := .mul ⟨(4637907673984597773353/2361183241434822606848:ℚ),(2325399221191780754023/1180591620717411303424:ℚ)⟩ node86 node4126
def node4213 : BoxExpr 3 := .inv ⟨(1198758959069260389861/2361183241434822606848:ℚ),(300522708273470617003/590295810358705651712:ℚ)⟩ node4212
def node4214 : BoxExpr 3 := .mul ⟨(831639027854299395465/4722366482869645213696:ℚ),(905324658673830233723/4722366482869645213696:ℚ)⟩ node4211 node4213
def node4215 : BoxExpr 3 := .mul ⟨(31383830500883608855/295147905179352825856:ℚ),(573357646989603283783/4722366482869645213696:ℚ)⟩ node117 node4214
def node4216 : BoxExpr 3 := .neg ⟨(-573357646989603283783/4722366482869645213696:ℚ),(-31383830500883608855/295147905179352825856:ℚ)⟩ node4215
def node4217 : BoxExpr 3 := .add ⟨(164893236279190173041/1180591620717411303424:ℚ),(405776929357561480023/2361183241434822606848:ℚ)⟩ node479 node4216
def node4218 : BoxExpr 3 := .add ⟨(-1402111231903004765249/2361183241434822606848:ℚ),(1603241905899146029875/4722366482869645213696:ℚ)⟩ node4208 node492
def node4219 : BoxExpr 3 := .mul ⟨(-2091404087852846963429/4722366482869645213696:ℚ),(-2012696821901254286305/4722366482869645213696:ℚ)⟩ node175 node4113
def node4220 : BoxExpr 3 := .mul ⟨(771635277884699740069/4722366482869645213696:ℚ),(858375749047646691287/4722366482869645213696:ℚ)⟩ node148 node4111
def node4221 : BoxExpr 3 := .add ⟨(-20621387655752300365/73786976294838206464:ℚ),(-577160536426803797509/2361183241434822606848:ℚ)⟩ node4219 node4220
def node4222 : BoxExpr 3 := .add ⟨(-548133532083447483291/4722366482869645213696:ℚ),(-295945323805960903731/4722366482869645213696:ℚ)⟩ node4221 node4220
def node4223 : BoxExpr 3 := .mul ⟨(-653490173970642357611/4722366482869645213696:ℚ),(-351489556411372575473/4722366482869645213696:ℚ)⟩ node4222 node304
def node4224 : BoxExpr 3 := .mul ⟨(-1965180714244294821399/4722366482869645213696:ℚ),(-1888187124183528683533/4722366482869645213696:ℚ)⟩ node148 node4113
def node4225 : BoxExpr 3 := .mul ⟨(-58695828972921630989/147573952589676412928:ℚ),(-1718209104521076737195/4722366482869645213696:ℚ)⟩ node36 node4111
def node4226 : BoxExpr 3 := .add ⟨(-3843447241377787013047/4722366482869645213696:ℚ),(-450799528588075677591/590295810358705651712:ℚ)⟩ node4224 node4225
def node4227 : BoxExpr 3 := .mul ⟨(-2193500484728001496977/2361183241434822606848:ℚ),(-2022267488551355415447/2361183241434822606848:ℚ)⟩ node4226 node461
def node4228 : BoxExpr 3 := .add ⟨(-5040491143426645351565/4722366482869645213696:ℚ),(-4396024533514083406367/4722366482869645213696:ℚ)⟩ node4223 node4227
def node4229 : BoxExpr 3 := .mul ⟨(20732615831326043571969/4722366482869645213696:ℚ),(676822444905254275193/147573952589676412928:ℚ)⟩ node4114 node514
def node4230 : BoxExpr 3 := .add ⟨(16345614861870040578015/4722366482869645213696:ℚ),(8806891629932712987641/2361183241434822606848:ℚ)⟩ node4227 node4229
def node4231 : BoxExpr 3 := .add ⟨(5652561859221697613225/2361183241434822606848:ℚ),(13217758726351342568915/4722366482869645213696:ℚ)⟩ node4228 node4230
def node4232 : BoxExpr 3 := .mul ⟨(-5727613479039678723/2361183241434822606848:ℚ),(-2163612348943627371/2361183241434822606848:ℚ)⟩ node4117 node189
def node4233 : BoxExpr 3 := .add ⟨(-32406786318589978975/2361183241434822606848:ℚ),(-14213374192379510169/1180591620717411303424:ℚ)⟩ node518 node4232
def node4234 : BoxExpr 3 := .add ⟨(-59085959158140279227/2361183241434822606848:ℚ),(-54689884420574413305/2361183241434822606848:ℚ)⟩ node518 node4233
def node4235 : BoxExpr 3 := .add ⟨(2796737950031778666999/1180591620717411303424:ℚ),(13108378957510193742305/4722366482869645213696:ℚ)⟩ node4231 node4234
def node4236 : BoxExpr 3 := .add ⟨(22290685078493686039519/4722366482869645213696:ℚ),(1856365624802352513553/295147905179352825856:ℚ)⟩ node4235 node527
def node4237 : BoxExpr 3 := .mul ⟨(-300522708273470617003/295147905179352825856:ℚ),(-1198758959069260389861/1180591620717411303424:ℚ)⟩ node6 node4213
def node4238 : BoxExpr 3 := .mul ⟨(831639027854299395465/2361183241434822606848:ℚ),(905324658673830233723/2361183241434822606848:ℚ)⟩ node86 node4214
def node4239 : BoxExpr 3 := .mul ⟨(18219837592387878062649/4722366482869645213696:ℚ),(18321260097148142391139/4722366482869645213696:ℚ)⟩ node4212 node4212
def node4240 : BoxExpr 3 := .inv ⟨(1217205862494246285059/4722366482869645213696:ℚ),(1223981557763594995397/4722366482869645213696:ℚ)⟩ node4239
def node4241 : BoxExpr 3 := .mul ⟨(107178879895841786371/1180591620717411303424:ℚ),(234649447480414311119/2361183241434822606848:ℚ)⟩ node4238 node4240
def node4242 : BoxExpr 3 := .neg ⟨(-234649447480414311119/2361183241434822606848:ℚ),(-107178879895841786371/1180591620717411303424:ℚ)⟩ node4241
def node4243 : BoxExpr 3 := .mul ⟨(-88360182566843514031/2361183241434822606848:ℚ),(-148710695855480478589/4722366482869645213696:ℚ)⟩ node4211 node4242
def node4244 : BoxExpr 3 := .add ⟨(-2492541848754608450055/2361183241434822606848:ℚ),(-4943746532132522038033/4722366482869645213696:ℚ)⟩ node4237 node4243
def node4245 : BoxExpr 3 := .mul ⟨(-6179713063951782355483/2361183241434822606848:ℚ),(-12238591716636336572981/4722366482869645213696:ℚ)⟩ node11 node4244
def node4246 : BoxExpr 3 := .add ⟨(-4558076698202910817941/4722366482869645213696:ℚ),(-4437242286935682679955/4722366482869645213696:ℚ)⟩ node4245 node546
def node4247 : BoxExpr 3 := .neg ⟨(4437242286935682679955/4722366482869645213696:ℚ),(4558076698202910817941/4722366482869645213696:ℚ)⟩ node4246
def cert_iv27 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-463/2560:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/2560:ℚ)],
    whole := node4137, centerValue := node4164, gradient := ![node4171, node4181, node4195],
    hessian := ![![node4201, node4209, node4217], ![node4218, node4236, node536], ![node4217, node536, node4247]] }

end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part7
end

section
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646CheckB4Part7
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part7

theorem cert_iv24_check : cert_iv24.check = true := by decide +kernel

theorem cert_iv24_lower_pos : 0 < cert_iv24.lower := by decide +kernel

theorem positive_iv24 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(539/2560:ℝ)) ≤ r) (hrhi : r ≤ (-(1059/5120:ℝ))) :
    0 < node3726.eval ![A,ρ,r] := by
  apply cert_iv24.positive_sound cert_iv24_check cert_iv24_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv24,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv24,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv24,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv25_check : cert_iv25.check = true := by decide +kernel

theorem cert_iv25_lower_pos : 0 < cert_iv25.lower := by decide +kernel

theorem positive_iv25 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(1059/5120:ℝ)) ≤ r) (hrhi : r ≤ (-(13/64:ℝ))) :
    0 < node3863.eval ![A,ρ,r] := by
  apply cert_iv25.positive_sound cert_iv25_check cert_iv25_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv25,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv25,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv25,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv26_check : cert_iv26.check = true := by decide +kernel

theorem cert_iv26_lower_pos : 0 < cert_iv26.lower := by decide +kernel

theorem positive_iv26 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(13/64:ℝ)) ≤ r) (hrhi : r ≤ (-(241/1280:ℝ))) :
    0 < node4000.eval ![A,ρ,r] := by
  apply cert_iv26.positive_sound cert_iv26_check cert_iv26_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv26,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv26,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv26,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv27_check : cert_iv27.check = true := by decide +kernel

theorem cert_iv27_lower_pos : 0 < cert_iv27.lower := by decide +kernel

theorem positive_iv27 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(241/1280:ℝ)) ≤ r) (hrhi : r ≤ (-(111/640:ℝ))) :
    0 < node4137.eval ![A,ρ,r] := by
  apply cert_iv27.positive_sound cert_iv27_check cert_iv27_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv27,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv27,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv27,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part7
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
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646BoundB4Part7
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part7
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate.CapacityCore
noncomputable section
namespace Parameters
def b : ℚ := (103531361122339324647880530522418473224550678173/6474633415922124204664207433178390079472570088576:ℚ)
def c : ℚ := (148022665013912365111/4722366482869645213696:ℚ)
def theta : ℚ := (105113898053531722649817636563532003778556764000751/182628568201966125342452015454275643968150995402752:ℚ)
end Parameters

theorem iv_shape24 : SplitDataB4Part7.node3726.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound24 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(539/2560:ℝ)) ≤ r) (hrhi : r ≤ (-(1059/5120:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part7.node3726 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape24 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part7.positive_iv24 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part7.node3726.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape25 : SplitDataB4Part7.node3863.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound25 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(1059/5120:ℝ)) ≤ r) (hrhi : r ≤ (-(13/64:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part7.node3863 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape25 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part7.positive_iv25 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part7.node3863.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape26 : SplitDataB4Part7.node4000.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound26 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(13/64:ℝ)) ≤ r) (hrhi : r ≤ (-(241/1280:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part7.node4000 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape26 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part7.positive_iv26 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part7.node4000.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape27 : SplitDataB4Part7.node4137.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound27 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(241/1280:ℝ)) ≤ r) (hrhi : r ≤ (-(111/640:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part7.node4137 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape27 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part7.positive_iv27 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part7.node4137.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem actual_bound (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (r : ℝ)
    (hrlo : (-(539/2560:ℝ)) ≤ r) (hrhi : r ≤ (-(111/640:ℝ))) : fA A r+3/10^6 ≤ l40Lhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) r := by
  have hc : 0 ≤ (Parameters.c:ℝ) := by norm_num [Parameters.c]
  have hθ : 0 ≤ (Parameters.theta:ℝ) := by norm_num [Parameters.theta]
  by_cases h0 : r ≤ (-(1059/5120:ℝ))
  · have h := iv_bound24 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  by_cases h1 : r ≤ (-(13/64:ℝ))
  · have h := iv_bound25 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  by_cases h2 : r ≤ (-(241/1280:ℝ))
  · have h := iv_bound26 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  have h := iv_bound27 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
  exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
    (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
end
end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part7
end

section
-- Source module: Solutions.Sol_GaussLocalMaxCase1FamilyAdaptive0Seed25646B4Part7
set_option autoImplicit false
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate
open GaussLocalMaxColoring.Certificate.CapacityCore
theorem solution (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (r : ℝ)
    (hrlo : (-(539/2560:ℝ)) ≤ r) (hrhi : r ≤ (-(111/640:ℝ))) :
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
  have h := GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part7.actual_bound A ρ hAlo hAhi hρlo hρhi r hrlo hrhi
  simpa only [Case2Static,constructedA,constructedMu,constructedMass,constructedKappa,thresholdCapacity,
    GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part7.Parameters.b,GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part7.Parameters.c,GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part7.Parameters.theta,
    show ¬ (4:ℕ)=1 by decide,show ¬ (4:ℕ)=2 by decide,show ¬ (4:ℕ)=3 by decide,ite_false,and_assoc] using h
end

#print axioms solution
