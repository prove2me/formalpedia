-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_40_adaptive0seed25646_b4_part_1
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T14:28:47.814726+00:00
-- url     : https://prove2.me/submissions/dcf67adf-881f-4fcd-99da-baf64b5aeef4

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
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646DefsB4Part1
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part1

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
def node299 : BoxExpr 3 := .var 2
def node300 : BoxExpr 3 := .mul ⟨(-118508945573725876519/590295810358705651712:ℚ),(-715702959113351637813/4722366482869645213696:ℚ)⟩ node13 node299
def node301 : BoxExpr 3 := .lit (1/2:ℚ)
def node302 : BoxExpr 3 := .add ⟨(176638959605626949337/590295810358705651712:ℚ),(1645480282321470969035/4722366482869645213696:ℚ)⟩ node300 node301
def node303 : BoxExpr 3 := .mul ⟨(2964488762697478623549/4722366482869645213696:ℚ),(3476026996692863815247/4722366482869645213696:ℚ)⟩ node36 node302
def node304 : BoxExpr 3 := .inv ⟨(5608679599763125114383/4722366482869645213696:ℚ),(2815025822917362847029/2361183241434822606848:ℚ)⟩ node16
def node305 : BoxExpr 3 := .mul ⟨(3520876176675875211265/4722366482869645213696:ℚ),(4144153484209117611599/4722366482869645213696:ℚ)⟩ node303 node304
def node306 : BoxExpr 3 := .mul ⟨(938626831624067721723/4722366482869645213696:ℚ),(118508945573725876519/590295810358705651712:ℚ)⟩ node13 node301
def node307 : BoxExpr 3 := .add ⟨(-1422556409810754885125/4722366482869645213696:ℚ),(-852330657004245225569/4722366482869645213696:ℚ)⟩ node299 node306
def node308 : BoxExpr 3 := .lit (-1886104779486749201381471199754505392441916025864035703364771907920146519389705837816997363452447960883131061278435345/43624816861295183480575856049041147371514908121470076568809273260400089500027672742507792890927579075052513478012043264:ℚ)
def node309 : BoxExpr 3 := .mul ⟨(9212559739735376101/1180591620717411303424:ℚ),(30751882032702209167/2361183241434822606848:ℚ)⟩ node307 node308
def node310 : BoxExpr 3 := .mul ⟨(40159729617063185283/4722366482869645213696:ℚ),(33577475854162686691/2361183241434822606848:ℚ)⟩ node309 node37
def node311 : BoxExpr 3 := .add ⟨(890258976573234599137/1180591620717411303424:ℚ),(4211308435917442984981/4722366482869645213696:ℚ)⟩ node305 node310
def node312 : BoxExpr 3 := .sqrt ⟨(4533599411214240034727/4722366482869645213696:ℚ),(4587472173287055931965/4722366482869645213696:ℚ)⟩ node250
def node313 : BoxExpr 3 := .lit (287742466255497847992269652017807647746707759403503/182628568201966125342452015454275643968150995402752:ℚ)
def node314 : BoxExpr 3 := .mul ⟨(3571481418379795453269/2361183241434822606848:ℚ),(1806960666143298416207/1180591620717411303424:ℚ)⟩ node312 node313
def node315 : BoxExpr 3 := .lit (3/2:ℚ)
def node316 : BoxExpr 3 := .mul ⟨(10714444255139386359807/4722366482869645213696:ℚ),(5420881998429895248621/2361183241434822606848:ℚ)⟩ node314 node315
def node317 : BoxExpr 3 := .add ⟨(14275480161432324756355/4722366482869645213696:ℚ),(15053072432777233482223/4722366482869645213696:ℚ)⟩ node311 node316
def node318 : BoxExpr 3 := .lit (3/1:ℚ)
def node319 : BoxExpr 3 := .sqrt ⟨(8179378680290567732005/4722366482869645213696:ℚ),(4089689340145283866003/2361183241434822606848:ℚ)⟩ node318
def node320 : BoxExpr 3 := .mul ⟨(2044844670072641933001/2361183241434822606848:ℚ),(4089689340145283866003/4722366482869645213696:ℚ)⟩ node319 node301
def node321 : BoxExpr 3 := .mul ⟨(294233257564094231095/590295810358705651712:ℚ),(1176933030256376924381/2361183241434822606848:ℚ)⟩ node320 node203
def node322 : BoxExpr 3 := .mul ⟨(4747823036598744829265/4722366482869645213696:ℚ),(1190486558240455338091/1180591620717411303424:ℚ)⟩ node321 node1
def node323 : BoxExpr 3 := .neg ⟨(-1190486558240455338091/1180591620717411303424:ℚ),(-4747823036598744829265/4722366482869645213696:ℚ)⟩ node322
def node324 : BoxExpr 3 := .add ⟨(9513533928470503403991/4722366482869645213696:ℚ),(5152624698089244326479/2361183241434822606848:ℚ)⟩ node317 node323
def node325 : BoxExpr 3 := .lit (-3/1000000:ℚ)
def node326 : BoxExpr 3 := .add ⟨(9513519761371054795055/4722366482869645213696:ℚ),(10305235229079040044023/4722366482869645213696:ℚ)⟩ node324 node325
def node327 : BoxExpr 3 := .mul ⟨(343201673491366207815/2361183241434822606848:ℚ),(1/4:ℚ)⟩ node299 node299
def node328 : BoxExpr 3 := .neg ⟨(-1/4:ℚ),(-343201673491366207815/2361183241434822606848:ℚ)⟩ node327
def node329 : BoxExpr 3 := .add ⟨(3/4:ℚ),(2017981567943456399033/2361183241434822606848:ℚ)⟩ node12 node328
def node330 : BoxExpr 3 := .sqrt ⟨(2044844670072641933001/2361183241434822606848:ℚ),(272855967606779907901/295147905179352825856:ℚ)⟩ node329
def node331 : BoxExpr 3 := .mul ⟨(10124313161404671635045/4722366482869645213696:ℚ),(10823788340817229919127/4722366482869645213696:ℚ)⟩ node11 node330
def node332 : BoxExpr 3 := .lit (-1/40:ℚ)
def node333 : BoxExpr 3 := .neg ⟨(1800402221594052237721/4722366482869645213696:ℚ),(1/2:ℚ)⟩ node299
def node334 : BoxExpr 3 := .add ⟨(841171529761155553689/2361183241434822606848:ℚ),(1121562039681540738253/2361183241434822606848:ℚ)⟩ node332 node333
def node335 : BoxExpr 3 := .lit (357/500:ℚ)
def node336 : BoxExpr 3 := .mul ⟨(1201192944498930130667/4722366482869645213696:ℚ),(800795296332620087113/2361183241434822606848:ℚ)⟩ node334 node335
def node337 : BoxExpr 3 := .neg ⟨(-800795296332620087113/2361183241434822606848:ℚ),(-1201192944498930130667/4722366482869645213696:ℚ)⟩ node336
def node338 : BoxExpr 3 := .add ⟨(8522722568739431460819/4722366482869645213696:ℚ),(2405648849079574947115/1180591620717411303424:ℚ)⟩ node331 node337
def node339 : BoxExpr 3 := .mul ⟨(299667357477411666001/2361183241434822606848:ℚ),(1065483937697463701341/4722366482869645213696:ℚ)⟩ node334 node334
def node340 : BoxExpr 3 := .lit (413/500:ℚ)
def node341 : BoxExpr 3 := .mul ⟨(495050474552684072233/4722366482869645213696:ℚ),(220022433134526254327/1180591620717411303424:ℚ)⟩ node339 node340
def node342 : BoxExpr 3 := .add ⟨(2254443260823028883263/1180591620717411303424:ℚ),(1312835641107050600721/590295810358705651712:ℚ)⟩ node338 node341
def node343 : BoxExpr 3 := .neg ⟨(-1312835641107050600721/590295810358705651712:ℚ),(-2254443260823028883263/1180591620717411303424:ℚ)⟩ node342
def node344 : BoxExpr 3 := .add ⟨(-989165367485350010713/4722366482869645213696:ℚ),(1287462185786924510971/4722366482869645213696:ℚ)⟩ node326 node343
def node345 : BoxExpr 3 := .var 2
def node346 : BoxExpr 3 := .mul ⟨(-831326480831738554615/4722366482869645213696:ℚ),(-831326480831738554613/4722366482869645213696:ℚ)⟩ node51 node345
def node347 : BoxExpr 3 := .add ⟨(1529856760603084052233/4722366482869645213696:ℚ),(1529856760603084052235/4722366482869645213696:ℚ)⟩ node346 node301
def node348 : BoxExpr 3 := .mul ⟨(805139600646599037969/1180591620717411303424:ℚ),(201284900161649759493/295147905179352825856:ℚ)⟩ node68 node347
def node349 : BoxExpr 3 := .inv ⟨(5619318555138810741159/4722366482869645213696:ℚ),(5619318555138810741161/4722366482869645213696:ℚ)⟩ node54
def node350 : BoxExpr 3 := .mul ⟨(3832261569535093116063/4722366482869645213696:ℚ),(239516348095943319755/295147905179352825856:ℚ)⟩ node348 node349
def node351 : BoxExpr 3 := .mul ⟨(943349198106937366937/4722366482869645213696:ℚ),(471674599053468683469/2361183241434822606848:ℚ)⟩ node51 node301
def node352 : BoxExpr 3 := .add ⟨(-284360883351875013837/1180591620717411303424:ℚ),(-568721766703750027673/2361183241434822606848:ℚ)⟩ node345 node351
def node353 : BoxExpr 3 := .mul ⟨(6147125189021620171/590295810358705651712:ℚ),(49177001512172961369/4722366482869645213696:ℚ)⟩ node352 node308
def node354 : BoxExpr 3 := .mul ⟨(53644354921197896605/4722366482869645213696:ℚ),(53644354921197896607/4722366482869645213696:ℚ)⟩ node353 node69
def node355 : BoxExpr 3 := .add ⟨(971476481114072753167/1180591620717411303424:ℚ),(3885905924456291012687/4722366482869645213696:ℚ)⟩ node350 node354
def node356 : BoxExpr 3 := .sqrt ⟨(4560915926422751217325/4722366482869645213696:ℚ),(2280457963211375608673/2361183241434822606848:ℚ)⟩ node254
def node357 : BoxExpr 3 := .mul ⟨(7186001675277507967931/4722366482869645213696:ℚ),(3593000837638753983983/2361183241434822606848:ℚ)⟩ node356 node313
def node358 : BoxExpr 3 := .mul ⟨(1347375314114532743987/590295810358705651712:ℚ),(10779002512916261951949/4722366482869645213696:ℚ)⟩ node357 node315
def node359 : BoxExpr 3 := .add ⟨(3666227109343138241141/1180591620717411303424:ℚ),(3666227109343138241159/1180591620717411303424:ℚ)⟩ node355 node358
def node360 : BoxExpr 3 := .mul ⟨(1188721158695070772703/1180591620717411303424:ℚ),(4754884634780283090817/4722366482869645213696:ℚ)⟩ node321 node44
def node361 : BoxExpr 3 := .neg ⟨(-4754884634780283090817/4722366482869645213696:ℚ),(-1188721158695070772703/1180591620717411303424:ℚ)⟩ node360
def node362 : BoxExpr 3 := .add ⟨(9910023802592269873747/4722366482869645213696:ℚ),(309688243831008433557/147573952589676412928:ℚ)⟩ node359 node361
def node363 : BoxExpr 3 := .add ⟨(9910009635492821264811/4722366482869645213696:ℚ),(9910009635492821264889/4722366482869645213696:ℚ)⟩ node362 node325
def node364 : BoxExpr 3 := .mul ⟨(916849297323548989193/4722366482869645213696:ℚ),(916849297323548989195/4722366482869645213696:ℚ)⟩ node345 node345
def node365 : BoxExpr 3 := .neg ⟨(-916849297323548989195/4722366482869645213696:ℚ),(-916849297323548989193/4722366482869645213696:ℚ)⟩ node364
def node366 : BoxExpr 3 := .add ⟨(3805517185546096224501/4722366482869645213696:ℚ),(3805517185546096224503/4722366482869645213696:ℚ)⟩ node12 node365
def node367 : BoxExpr 3 := .sqrt ⟨(1059806786842751277661/1180591620717411303424:ℚ),(2119613573685502555323/2361183241434822606848:ℚ)⟩ node366
def node368 : BoxExpr 3 := .mul ⟨(10502277261036902048709/4722366482869645213696:ℚ),(10502277261036902048723/4722366482869645213696:ℚ)⟩ node50 node367
def node369 : BoxExpr 3 := .neg ⟨(520198182878609355571/1180591620717411303424:ℚ),(2080792731514437422285/4722366482869645213696:ℚ)⟩ node345
def node370 : BoxExpr 3 := .add ⟨(1962733569442696291941/4722366482869645213696:ℚ),(1962733569442696291943/4722366482869645213696:ℚ)⟩ node332 node369
def node371 : BoxExpr 3 := .mul ⟨(1401391768582085152445/4722366482869645213696:ℚ),(21896746384095080507/73786976294838206464:ℚ)⟩ node370 node335
def node372 : BoxExpr 3 := .neg ⟨(-21896746384095080507/73786976294838206464:ℚ),(-1401391768582085152445/4722366482869645213696:ℚ)⟩ node371
def node373 : BoxExpr 3 := .add ⟨(9100885492454816896261/4722366482869645213696:ℚ),(4550442746227408448139/2361183241434822606848:ℚ)⟩ node368 node372
def node374 : BoxExpr 3 := .mul ⟨(815761139799620646337/4722366482869645213696:ℚ),(203940284949905161585/1180591620717411303424:ℚ)⟩ node370 node370
def node375 : BoxExpr 3 := .mul ⟨(336909350737243326937/2361183241434822606848:ℚ),(673818701474486653877/4722366482869645213696:ℚ)⟩ node374 node340
def node376 : BoxExpr 3 := .add ⟨(9774704193929303550135/4722366482869645213696:ℚ),(9774704193929303550155/4722366482869645213696:ℚ)⟩ node373 node375
def node377 : BoxExpr 3 := .neg ⟨(-9774704193929303550155/4722366482869645213696:ℚ),(-9774704193929303550135/4722366482869645213696:ℚ)⟩ node376
def node378 : BoxExpr 3 := .add ⟨(4228295048859928583/147573952589676412928:ℚ),(67652720781758857377/2361183241434822606848:ℚ)⟩ node363 node377
def node379 : BoxExpr 3 := .mul ⟨(867498295381759938587/4722366482869645213696:ℚ),(27109321730679998081/147573952589676412928:ℚ)⟩ node78 node347
def node380 : BoxExpr 3 := .mul ⟨(1032268309855479216887/4722366482869645213696:ℚ),(516134154927739608447/2361183241434822606848:ℚ)⟩ node379 node349
def node381 : BoxExpr 3 := .mul ⟨(4560915926422751217325/2361183241434822606848:ℚ),(2280457963211375608673/1180591620717411303424:ℚ)⟩ node86 node356
def node382 : BoxExpr 3 := .inv ⟨(2444766090659085683355/4722366482869645213696:ℚ),(2444766090659085683367/4722366482869645213696:ℚ)⟩ node381
def node383 : BoxExpr 3 := .mul ⟨(1641417929653866236565/4722366482869645213696:ℚ),(820708964826933118371/2361183241434822606848:ℚ)⟩ node259 node382
def node384 : BoxExpr 3 := .mul ⟨(1293077112427123662531/2361183241434822606848:ℚ),(1293077112427123662671/2361183241434822606848:ℚ)⟩ node383 node313
def node385 : BoxExpr 3 := .mul ⟨(3879231337281370987593/4722366482869645213696:ℚ),(3879231337281370988013/4722366482869645213696:ℚ)⟩ node384 node315
def node386 : BoxExpr 3 := .add ⟨(76742181986513284445/73786976294838206464:ℚ),(4911499647136850204907/4722366482869645213696:ℚ)⟩ node380 node385
def node387 : BoxExpr 3 := .neg ⟨(-1176933030256376924381/2361183241434822606848:ℚ),(-294233257564094231095/590295810358705651712:ℚ)⟩ node321
def node388 : BoxExpr 3 := .add ⟨(1278816793312048177859/2361183241434822606848:ℚ),(2557633586624096356147/4722366482869645213696:ℚ)⟩ node386 node387
def node389 : BoxExpr 3 := .mul ⟨(1311102164799042761013/2361183241434822606848:ℚ),(2622204329598085522035/4722366482869645213696:ℚ)⟩ node77 node367
def node390 : BoxExpr 3 := .neg ⟨(-2622204329598085522035/4722366482869645213696:ℚ),(-1311102164799042761013/2361183241434822606848:ℚ)⟩ node389
def node391 : BoxExpr 3 := .add ⟨(-64570742973989166317/4722366482869645213696:ℚ),(-64570742973989165879/4722366482869645213696:ℚ)⟩ node388 node390
def node392 : BoxExpr 3 := .mul ⟨(-364772753699465974591/1180591620717411303424:ℚ),(-1459091014797863898355/4722366482869645213696:ℚ)⟩ node98 node347
def node393 : BoxExpr 3 := .mul ⟨(-4380354218834055224073/4722366482869645213696:ℚ),(-1095088554708513806015/1180591620717411303424:ℚ)⟩ node68 node345
def node394 : BoxExpr 3 := .add ⟨(-5839445233631919122437/4722366482869645213696:ℚ),(-5839445233631919122415/4722366482869645213696:ℚ)⟩ node392 node393
def node395 : BoxExpr 3 := .mul ⟨(-3474285940332694683879/2361183241434822606848:ℚ),(-434285742541586835483/295147905179352825856:ℚ)⟩ node394 node349
def node396 : BoxExpr 3 := .mul ⟨(3335122253056120841147/4722366482869645213696:ℚ),(1667561126528060420575/2361183241434822606848:ℚ)⟩ node54 node54
def node397 : BoxExpr 3 := .inv ⟨(6686635003588086928419/4722366482869645213696:ℚ),(3343317501794043464213/2361183241434822606848:ℚ)⟩ node396
def node398 : BoxExpr 3 := .mul ⟨(-5342941333799670338881/4722366482869645213696:ℚ),(-667867666724958792359/590295810358705651712:ℚ)⟩ node85 node397
def node399 : BoxExpr 3 := .neg ⟨(667867666724958792359/590295810358705651712:ℚ),(5342941333799670338881/4722366482869645213696:ℚ)⟩ node398
def node400 : BoxExpr 3 := .mul ⟨(910944474000159837949/1180591620717411303424:ℚ),(3643777896000639351817/4722366482869645213696:ℚ)⟩ node348 node399
def node401 : BoxExpr 3 := .add ⟨(-1652396992332375007981/2361183241434822606848:ℚ),(-3304793984664750015911/4722366482869645213696:ℚ)⟩ node395 node400
def node402 : BoxExpr 3 := .lit (-1886104779486749201381471199754505392441916025864035703364771907920146519389705837816997363452447960883131061278435345/87249633722590366961151712098082294743029816242940153137618546520800179000055345485015585781855158150105026956024086528:ℚ)
def node403 : BoxExpr 3 := .mul ⟨(-111358628465766203533/4722366482869645213696:ℚ),(-111358628465766203531/4722366482869645213696:ℚ)⟩ node402 node69
def node404 : BoxExpr 3 := .mul ⟨(25502971438714585063/4722366482869645213696:ℚ),(3187871429839323133/590295810358705651712:ℚ)⟩ node353 node103
def node405 : BoxExpr 3 := .add ⟨(-42927828513525809235/2361183241434822606848:ℚ),(-85855657027051618467/4722366482869645213696:ℚ)⟩ node403 node404
def node406 : BoxExpr 3 := .add ⟨(-26489450325717200269/36893488147419103232:ℚ),(-1695324820845900817189/2361183241434822606848:ℚ)⟩ node401 node405
def node407 : BoxExpr 3 := .mul ⟨(17026592217487914599/590295810358705651712:ℚ),(17026592217487914605/590295810358705651712:ℚ)⟩ node264 node382
def node408 : BoxExpr 3 := .mul ⟨(214611489749779220183/4722366482869645213696:ℚ),(53652872437444805065/1180591620717411303424:ℚ)⟩ node407 node313
def node409 : BoxExpr 3 := .mul ⟨(160958617312334415137/2361183241434822606848:ℚ),(160958617312334415195/2361183241434822606848:ℚ)⟩ node408 node315
def node410 : BoxExpr 3 := .add ⟨(-1534366203533566402079/2361183241434822606848:ℚ),(-767183101766783200997/1180591620717411303424:ℚ)⟩ node406 node409
def node411 : BoxExpr 3 := .mul ⟨(1985879505045154496735/2361183241434822606848:ℚ),(1985879505045154496741/2361183241434822606848:ℚ)⟩ node68 node51
def node412 : BoxExpr 3 := .mul ⟨(4726142958811166820663/4722366482869645213696:ℚ),(590767869851395852585/590295810358705651712:ℚ)⟩ node411 node349
def node413 : BoxExpr 3 := .mul ⟨(-27839657116441550883/590295810358705651712:ℚ),(-111358628465766203531/2361183241434822606848:ℚ)⟩ node308 node69
def node414 : BoxExpr 3 := .add ⟨(4503425701879634413599/4722366482869645213696:ℚ),(2251712850939817206809/2361183241434822606848:ℚ)⟩ node412 node413
def node415 : BoxExpr 3 := .add ⟨(-2080792731514437422285/2361183241434822606848:ℚ),(-520198182878609355571/590295810358705651712:ℚ)⟩ node345 node345
def node416 : BoxExpr 3 := .neg ⟨(520198182878609355571/590295810358705651712:ℚ),(2080792731514437422285/2361183241434822606848:ℚ)⟩ node415
def node417 : BoxExpr 3 := .mul ⟨(1059806786842751277661/590295810358705651712:ℚ),(2119613573685502555323/1180591620717411303424:ℚ)⟩ node86 node367
def node418 : BoxExpr 3 := .inv ⟨(2630284297499914706491/4722366482869645213696:ℚ),(2630284297499914706493/4722366482869645213696:ℚ)⟩ node417
def node419 : BoxExpr 3 := .mul ⟨(1158969018585899917547/2361183241434822606848:ℚ),(1158969018585899917549/2361183241434822606848:ℚ)⟩ node416 node418
def node420 : BoxExpr 3 := .mul ⟨(2871234200717319771431/2361183241434822606848:ℚ),(5742468401434639542877/4722366482869645213696:ℚ)⟩ node50 node419
def node421 : BoxExpr 3 := .add ⟨(284819939693861444545/147573952589676412928:ℚ),(569639879387722889091/295147905179352825856:ℚ)⟩ node420 node335
def node422 : BoxExpr 3 := .lit (-1/1:ℚ)
def node423 : BoxExpr 3 := .mul ⟨(-1962733569442696291943/4722366482869645213696:ℚ),(-1962733569442696291941/4722366482869645213696:ℚ)⟩ node422 node370
def node424 : BoxExpr 3 := .mul ⟨(-1962733569442696291943/4722366482869645213696:ℚ),(-1962733569442696291941/4722366482869645213696:ℚ)⟩ node370 node422
def node425 : BoxExpr 3 := .add ⟨(-1962733569442696291943/2361183241434822606848:ℚ),(-1962733569442696291941/2361183241434822606848:ℚ)⟩ node423 node424
def node426 : BoxExpr 3 := .mul ⟨(-1621217928359667137145/2361183241434822606848:ℚ),(-3242435856719334274285/4722366482869645213696:ℚ)⟩ node425 node340
def node427 : BoxExpr 3 := .add ⟨(2935901106742115975575/2361183241434822606848:ℚ),(5871802213484231951171/4722366482869645213696:ℚ)⟩ node421 node426
def node428 : BoxExpr 3 := .neg ⟨(-5871802213484231951171/4722366482869645213696:ℚ),(-2935901106742115975575/2361183241434822606848:ℚ)⟩ node427
def node429 : BoxExpr 3 := .add ⟨(-342094127901149384393/1180591620717411303424:ℚ),(-342094127901149384383/1180591620717411303424:ℚ)⟩ node414 node428
def node430 : BoxExpr 3 := .mul ⟨(3183722793348747094785/2361183241434822606848:ℚ),(464287863030155616787/295147905179352825856:ℚ)⟩ node112 node302
def node431 : BoxExpr 3 := .mul ⟨(118164279677958224375/73786976294838206464:ℚ),(276764272412587595733/147573952589676412928:ℚ)⟩ node430 node304
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
def node449 : BoxExpr 3 := .add ⟨(18888724818252110522723/4722366482869645213696:ℚ),(43182806329863621477737/4722366482869645213696:ℚ)⟩ node431 node448
def node450 : BoxExpr 3 := .mul ⟨(20121271553514796620729/4722366482869645213696:ℚ),(1342451360625357146873/295147905179352825856:ℚ)⟩ node111 node330
def node451 : BoxExpr 3 := .neg ⟨(-1342451360625357146873/295147905179352825856:ℚ),(-20121271553514796620729/4722366482869645213696:ℚ)⟩ node450
def node452 : BoxExpr 3 := .add ⟨(-2590496951753603827245/4722366482869645213696:ℚ),(1441345923521801553563/295147905179352825856:ℚ)⟩ node449 node451
def node453 : BoxExpr 3 := .mul ⟨(-228439773462153684491/2361183241434822606848:ℚ),(-369641990007743989753/4722366482869645213696:ℚ)⟩ node131 node302
def node454 : BoxExpr 3 := .mul ⟨(-1372146493047348603437/4722366482869645213696:ℚ),(-497799285790076319587/2361183241434822606848:ℚ)⟩ node118 node299
def node455 : BoxExpr 3 := .add ⟨(-1829026039971655972419/4722366482869645213696:ℚ),(-1365240561587896628927/4722366482869645213696:ℚ)⟩ node453 node454
def node456 : BoxExpr 3 := .mul ⟨(-2180582787035091256551/4722366482869645213696:ℚ),(-1621474511629629315909/4722366482869645213696:ℚ)⟩ node455 node304
def node457 : BoxExpr 3 := .mul ⟨(195358008071175382081/1180591620717411303424:ℚ),(956232434291691638465/4722366482869645213696:ℚ)⟩ node118 node302
def node458 : BoxExpr 3 := .mul ⟨(3322418266985942863501/4722366482869645213696:ℚ),(3347786862908889618591/4722366482869645213696:ℚ)⟩ node16 node16
def node459 : BoxExpr 3 := .inv ⟨(1665334899721895791211/1180591620717411303424:ℚ),(6712202801232966340575/4722366482869645213696:ℚ)⟩ node458
def node460 : BoxExpr 3 := .mul ⟨(-5390220038781927845849/4722366482869645213696:ℚ),(-1324020934155944627541/1180591620717411303424:ℚ)⟩ node127 node459
def node461 : BoxExpr 3 := .neg ⟨(1324020934155944627541/1180591620717411303424:ℚ),(5390220038781927845849/4722366482869645213696:ℚ)⟩ node460
def node462 : BoxExpr 3 := .mul ⟨(876367705147909402437/4722366482869645213696:ℚ),(272866540946657888421/1180591620717411303424:ℚ)⟩ node457 node461
def node463 : BoxExpr 3 := .add ⟨(-652107540943590927057/2361183241434822606848:ℚ),(-530008347842997762225/4722366482869645213696:ℚ)⟩ node456 node462
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
def node477 : BoxExpr 3 := .add ⟨(-4061515806781652696073/4722366482869645213696:ℚ),(883565532728662010679/4722366482869645213696:ℚ)⟩ node463 node476
def node478 : BoxExpr 3 := .mul ⟨(259524100115899746407/1180591620717411303424:ℚ),(550949646635346069789/2361183241434822606848:ℚ)⟩ node118 node13
def node479 : BoxExpr 3 := .mul ⟨(1232930592106363975947/4722366482869645213696:ℚ),(656847573364630350863/2361183241434822606848:ℚ)⟩ node478 node304
def node480 : BoxExpr 3 := .add ⟨(-1/1:ℚ),(-1800402221594052237721/2361183241434822606848:ℚ)⟩ node299 node299
def node481 : BoxExpr 3 := .neg ⟨(1800402221594052237721/2361183241434822606848:ℚ),(1/1:ℚ)⟩ node480
def node482 : BoxExpr 3 := .mul ⟨(2044844670072641933001/1180591620717411303424:ℚ),(272855967606779907901/147573952589676412928:ℚ)⟩ node86 node330
def node483 : BoxExpr 3 := .inv ⟨(79815265445559276501/147573952589676412928:ℚ),(2726459560096855910669/4722366482869645213696:ℚ)⟩ node482
def node484 : BoxExpr 3 := .mul ⟨(1947492476871646346623/4722366482869645213696:ℚ),(2726459560096855910669/4722366482869645213696:ℚ)⟩ node481 node483
def node485 : BoxExpr 3 := .mul ⟨(1175890438015253656929/4722366482869645213696:ℚ),(863356820678759372853/2361183241434822606848:ℚ)⟩ node117 node484
def node486 : BoxExpr 3 := .neg ⟨(-863356820678759372853/2361183241434822606848:ℚ),(-1175890438015253656929/4722366482869645213696:ℚ)⟩ node485
def node487 : BoxExpr 3 := .add ⟨(-493783049251154769759/4722366482869645213696:ℚ),(137804708714007044797/4722366482869645213696:ℚ)⟩ node479 node486
def node488 : BoxExpr 3 := .mul ⟨(-1066036936173269434493/4722366482869645213696:ℚ),(307821252238552030869/2361183241434822606848:ℚ)⟩ node290 node433
def node489 : BoxExpr 3 := .mul ⟨(-100658848064542979319/4722366482869645213696:ℚ),(-8758717586159332837/2361183241434822606848:ℚ)⟩ node468 node444
def node490 : BoxExpr 3 := .add ⟨(-291673946059453103453/1180591620717411303424:ℚ),(18691408415774543627/147573952589676412928:ℚ)⟩ node488 node489
def node491 : BoxExpr 3 := .mul ⟨(-1838200483262980561305/4722366482869645213696:ℚ),(58898911690485823871/295147905179352825856:ℚ)⟩ node490 node313
def node492 : BoxExpr 3 := .mul ⟨(-1378650362447235420979/2361183241434822606848:ℚ),(176696735071457471613/590295810358705651712:ℚ)⟩ node491 node315
def node493 : BoxExpr 3 := .add ⟨(-507689475847706587009/590295810358705651712:ℚ),(883565532728662010679/4722366482869645213696:ℚ)⟩ node463 node492
def node494 : BoxExpr 3 := .mul ⟨(-1690592041951130033105/4722366482869645213696:ℚ),(-177390030817281988915/590295810358705651712:ℚ)⟩ node175 node302
def node495 : BoxExpr 3 := .mul ⟨(1696207277512312942135/4722366482869645213696:ℚ),(1139752031930485233243/2361183241434822606848:ℚ)⟩ node148 node299
def node496 : BoxExpr 3 := .add ⟨(2807617780591454515/2361183241434822606848:ℚ),(430191908661357277583/2361183241434822606848:ℚ)⟩ node494 node495
def node497 : BoxExpr 3 := .add ⟨(1701822513073495851165/4722366482869645213696:ℚ),(784971970295921255413/1180591620717411303424:ℚ)⟩ node496 node495
def node498 : BoxExpr 3 := .mul ⟨(252653443091437190789/590295810358705651712:ℚ),(3743405133278108240037/4722366482869645213696:ℚ)⟩ node497 node304
def node499 : BoxExpr 3 := .mul ⟨(-1588559043081971751159/4722366482869645213696:ℚ),(-332832613936669796139/1180591620717411303424:ℚ)⟩ node148 node302
def node500 : BoxExpr 3 := .mul ⟨(-2493963853455259341605/2361183241434822606848:ℚ),(-3776964157685970485367/4722366482869645213696:ℚ)⟩ node36 node299
def node501 : BoxExpr 3 := .add ⟨(-6576486749992490434369/4722366482869645213696:ℚ),(-5108294613432649669923/4722366482869645213696:ℚ)⟩ node499 node500
def node502 : BoxExpr 3 := .mul ⟨(-3753278233824432296899/2361183241434822606848:ℚ),(-5728898026491921620245/4722366482869645213696:ℚ)⟩ node501 node461
def node503 : BoxExpr 3 := .add ⟨(-2742664461458683533743/2361183241434822606848:ℚ),(-124093305825863336263/295147905179352825856:ℚ)⟩ node498 node502
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
def node515 : BoxExpr 3 := .mul ⟨(14618234882559898295921/4722366482869645213696:ℚ),(2188444874554035218691/590295810358705651712:ℚ)⟩ node303 node514
def node516 : BoxExpr 3 := .add ⟨(7111678414911033702123/4722366482869645213696:ℚ),(11778660969940360129283/4722366482869645213696:ℚ)⟩ node502 node515
def node517 : BoxExpr 3 := .add ⟨(1626349491993666634637/4722366482869645213696:ℚ),(9793168076726546749075/4722366482869645213696:ℚ)⟩ node503 node516
def node518 : BoxExpr 3 := .mul ⟨(-6669793209887575063/590295810358705651712:ℚ),(-26263136035815392967/2361183241434822606848:ℚ)⟩ node402 node136
def node519 : BoxExpr 3 := .mul ⟨(18629751143920146049/1180591620717411303424:ℚ),(63143969147846851131/2361183241434822606848:ℚ)⟩ node309 node189
def node520 : BoxExpr 3 := .add ⟨(5290164724144995923/1180591620717411303424:ℚ),(9220208278007864541/590295810358705651712:ℚ)⟩ node518 node519
def node521 : BoxExpr 3 := .add ⟨(-8049421695630154203/1180591620717411303424:ℚ),(10617697076216065197/2361183241434822606848:ℚ)⟩ node518 node520
def node522 : BoxExpr 3 := .add ⟨(1594151805211146017825/4722366482869645213696:ℚ),(9814403470878978879469/4722366482869645213696:ℚ)⟩ node517 node521
def node523 : BoxExpr 3 := .mul ⟨(4710600635840625837895/4722366482869645213696:ℚ),(3510962798386249577057/2361183241434822606848:ℚ)⟩ node298 node433
def node524 : BoxExpr 3 := .mul ⟨(-12281483268977163869/4722366482869645213696:ℚ),(-367720260249431685/2361183241434822606848:ℚ)⟩ node468 node472
def node525 : BoxExpr 3 := .add ⟨(2349159576285824337013/2361183241434822606848:ℚ),(877648769531500036343/590295810358705651712:ℚ)⟩ node523 node524
def node526 : BoxExpr 3 := .mul ⟨(7402488852244380914349/4722366482869645213696:ℚ),(11062314026218297649695/4722366482869645213696:ℚ)⟩ node525 node313
def node527 : BoxExpr 3 := .mul ⟨(11103733278366571371523/4722366482869645213696:ℚ),(16593471039327446474543/4722366482869645213696:ℚ)⟩ node526 node315
def node528 : BoxExpr 3 := .add ⟨(3174471270894429347337/1180591620717411303424:ℚ),(6601968627551606338503/1180591620717411303424:ℚ)⟩ node522 node527
def node529 : BoxExpr 3 := .mul ⟨(-57204713784735629119/147573952589676412928:ℚ),(-884305542157928933957/2361183241434822606848:ℚ)⟩ node148 node13
def node530 : BoxExpr 3 := .add ⟨(8076240392163136551127/4722366482869645213696:ℚ),(8207244329505179498505/4722366482869645213696:ℚ)⟩ node529 node36
def node531 : BoxExpr 3 := .mul ⟨(9592022324955733713563/4722366482869645213696:ℚ),(9784757200169600967561/4722366482869645213696:ℚ)⟩ node530 node304
def node532 : BoxExpr 3 := .mul ⟨(984546635736655182275/1180591620717411303424:ℚ),(4005544628783559212985/4722366482869645213696:ℚ)⟩ node36 node13
def node533 : BoxExpr 3 := .mul ⟨(1104158570578370606741/1180591620717411303424:ℚ),(4572022735343567862705/4722366482869645213696:ℚ)⟩ node532 node461
def node534 : BoxExpr 3 := .add ⟨(14008656607269216140527/4722366482869645213696:ℚ),(7178389967756584415133/2361183241434822606848:ℚ)⟩ node531 node533
def node535 : BoxExpr 3 := .mul ⟨(-106716691358201201007/4722366482869645213696:ℚ),(-26263136035815392967/1180591620717411303424:ℚ)⟩ node308 node136
def node536 : BoxExpr 3 := .add ⟨(108608905593054804215/36893488147419103232:ℚ),(7125863695684953629199/2361183241434822606848:ℚ)⟩ node534 node535
def node537 : BoxExpr 3 := .mul ⟨(-2726459560096855910669/2361183241434822606848:ℚ),(-79815265445559276501/73786976294838206464:ℚ)⟩ node6 node483
def node538 : BoxExpr 3 := .mul ⟨(1947492476871646346623/2361183241434822606848:ℚ),(2726459560096855910669/2361183241434822606848:ℚ)⟩ node86 node484
def node539 : BoxExpr 3 := .mul ⟨(7083549724304467820541/2361183241434822606848:ℚ),(16143852543547651192265/4722366482869645213696:ℚ)⟩ node482 node482
def node540 : BoxExpr 3 := .inv ⟨(1381376913495394184727/4722366482869645213696:ℚ),(1574122160956548404567/4722366482869645213696:ℚ)⟩ node539
def node541 : BoxExpr 3 := .mul ⟨(569676486675740967063/2361183241434822606848:ℚ),(908819853365618636891/2361183241434822606848:ℚ)⟩ node538 node540
def node542 : BoxExpr 3 := .neg ⟨(-908819853365618636891/2361183241434822606848:ℚ),(-569676486675740967063/2361183241434822606848:ℚ)⟩ node541
def node543 : BoxExpr 3 := .mul ⟨(-908819853365618636891/2361183241434822606848:ℚ),(-434378321090252487385/2361183241434822606848:ℚ)⟩ node481 node542
def node544 : BoxExpr 3 := .add ⟨(-454409926682809318445/295147905179352825856:ℚ),(-2988466815348149335417/2361183241434822606848:ℚ)⟩ node537 node543
def node545 : BoxExpr 3 := .mul ⟨(-4506440622795078238859/1180591620717411303424:ℚ),(-14796318935059032947113/4722366482869645213696:ℚ)⟩ node11 node544
def node546 : BoxExpr 3 := .lit (413/250:ℚ)
def node547 : BoxExpr 3 := .add ⟨(-10224413061479659062411/4722366482869645213696:ℚ),(-6994969505358379054087/4722366482869645213696:ℚ)⟩ node545 node546
def node548 : BoxExpr 3 := .neg ⟨(6994969505358379054087/4722366482869645213696:ℚ),(10224413061479659062411/4722366482869645213696:ℚ)⟩ node547
def cert_iv0 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-141/320:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/320:ℚ)],
    whole := node344, centerValue := node378, gradient := ![node391, node410, node429],
    hessian := ![![node452, node477, node487], ![node493, node528, node536], ![node487, node536, node548]] }
def node549 : BoxExpr 3 := .var 2
def node550 : BoxExpr 3 := .mul ⟨(-361452283999863923383/2361183241434822606848:ℚ),(-604241022857993595859/4722366482869645213696:ℚ)⟩ node13 node549
def node551 : BoxExpr 3 := .add ⟨(819139336717547380041/2361183241434822606848:ℚ),(1756942218576829010989/4722366482869645213696:ℚ)⟩ node550 node301
def node552 : BoxExpr 3 := .mul ⟨(1718427070254097653277/2361183241434822606848:ℚ),(1855743471683052573571/2361183241434822606848:ℚ)⟩ node36 node551
def node553 : BoxExpr 3 := .mul ⟨(510237128332640226175/590295810358705651712:ℚ),(2212435571211176450311/2361183241434822606848:ℚ)⟩ node552 node304
def node554 : BoxExpr 3 := .add ⟨(-861775389969984515999/4722366482869645213696:ℚ),(-285970073541930020503/2361183241434822606848:ℚ)⟩ node549 node306
def node555 : BoxExpr 3 := .mul ⟨(12363823192943897069/2361183241434822606848:ℚ),(37258578919296997803/4722366482869645213696:ℚ)⟩ node554 node308
def node556 : BoxExpr 3 := .mul ⟨(26948416644735056577/4722366482869645213696:ℚ),(40682031515753004299/4722366482869645213696:ℚ)⟩ node555 node37
def node557 : BoxExpr 3 := .add ⟨(4108845443305856865977/4722366482869645213696:ℚ),(4465553173938105904921/4722366482869645213696:ℚ)⟩ node553 node556
def node558 : BoxExpr 3 := .add ⟨(1852911212305655403223/590295810358705651712:ℚ),(15307317170797896402163/4722366482869645213696:ℚ)⟩ node557 node316
def node559 : BoxExpr 3 := .add ⟨(2515335866370855468355/1180591620717411303424:ℚ),(5279747067099575786449/2361183241434822606848:ℚ)⟩ node558 node323
def node560 : BoxExpr 3 := .add ⟨(2515332324595993316121/1180591620717411303424:ℚ),(10559479967099702963963/4722366482869645213696:ℚ)⟩ node559 node325
def node561 : BoxExpr 3 := .mul ⟨(489253769694961582735/4722366482869645213696:ℚ),(42900209186420775977/295147905179352825856:ℚ)⟩ node549 node549
def node562 : BoxExpr 3 := .neg ⟨(-42900209186420775977/295147905179352825856:ℚ),(-489253769694961582735/4722366482869645213696:ℚ)⟩ node561
def node563 : BoxExpr 3 := .add ⟨(252247695992932049879/295147905179352825856:ℚ),(4233112713174683630961/4722366482869645213696:ℚ)⟩ node12 node562
def node564 : BoxExpr 3 := .sqrt ⟨(2182847740854239263207/2361183241434822606848:ℚ),(4471052403506976566363/4722366482869645213696:ℚ)⟩ node563
def node565 : BoxExpr 3 := .mul ⟨(5403792873736454661787/2361183241434822606848:ℚ),(2771249453782515376523/1180591620717411303424:ℚ)⟩ node11 node564
def node566 : BoxExpr 3 := .neg ⟨(760005855836833526579/2361183241434822606848:ℚ),(900201110797026118861/2361183241434822606848:ℚ)⟩ node549
def node567 : BoxExpr 3 := .add ⟨(1401952549601925922815/4722366482869645213696:ℚ),(420585764880577776845/1180591620717411303424:ℚ)⟩ node332 node566
def node568 : BoxExpr 3 := .mul ⟨(1000994120415775108889/4722366482869645213696:ℚ),(600596472249465065335/2361183241434822606848:ℚ)⟩ node567 node335
def node569 : BoxExpr 3 := .neg ⟨(-600596472249465065335/2361183241434822606848:ℚ),(-1000994120415775108889/4722366482869645213696:ℚ)⟩ node568
def node570 : BoxExpr 3 := .add ⟨(1200799100371747399113/590295810358705651712:ℚ),(10084003694714286397203/4722366482869645213696:ℚ)⟩ node565 node569
def node571 : BoxExpr 3 := .mul ⟨(416204663163071758335/4722366482869645213696:ℚ),(599334714954823332005/4722366482869645213696:ℚ)⟩ node567 node567
def node572 : BoxExpr 3 := .mul ⟨(5371641433948394881/73786976294838206464:ℚ),(495050474552684072237/4722366482869645213696:ℚ)⟩ node571 node340
def node573 : BoxExpr 3 := .add ⟨(1243772231843334558161/590295810358705651712:ℚ),(165297721394796413585/73786976294838206464:ℚ)⟩ node570 node572
def node574 : BoxExpr 3 := .neg ⟨(-165297721394796413585/73786976294838206464:ℚ),(-1243772231843334558161/590295810358705651712:ℚ)⟩ node573
def node575 : BoxExpr 3 := .add ⟨(-129431217720749301239/1180591620717411303424:ℚ),(609302112353026498675/4722366482869645213696:ℚ)⟩ node560 node574
def node576 : BoxExpr 3 := .var 2
def node577 : BoxExpr 3 := .mul ⟨(-663292404918940336129/4722366482869645213696:ℚ),(-663292404918940336127/4722366482869645213696:ℚ)⟩ node51 node576
def node578 : BoxExpr 3 := .add ⟨(1697890836515882270719/4722366482869645213696:ℚ),(1697890836515882270721/4722366482869645213696:ℚ)⟩ node577 node301
def node579 : BoxExpr 3 := .mul ⟨(3574293189422564296607/4722366482869645213696:ℚ),(3574293189422564296621/4722366482869645213696:ℚ)⟩ node68 node578
def node580 : BoxExpr 3 := .mul ⟨(4253183676804212661029/4722366482869645213696:ℚ),(531647959600526582631/590295810358705651712:ℚ)⟩ node579 node349
def node581 : BoxExpr 3 := .add ⟨(-716857768526922278503/4722366482869645213696:ℚ),(-358428884263461139251/2361183241434822606848:ℚ)⟩ node576 node351
def node582 : BoxExpr 3 := .mul ⟨(15496556326296197985/2361183241434822606848:ℚ),(30993112652592395971/4722366482869645213696:ℚ)⟩ node581 node308
def node583 : BoxExpr 3 := .mul ⟨(2113037451608330725/295147905179352825856:ℚ),(33808599225733291603/4722366482869645213696:ℚ)⟩ node582 node69
def node584 : BoxExpr 3 := .add ⟨(4286992276029945952629/4722366482869645213696:ℚ),(4286992276029945952651/4722366482869645213696:ℚ)⟩ node580 node583
def node585 : BoxExpr 3 := .add ⟨(15065994788946207904525/4722366482869645213696:ℚ),(1883249348618275988075/590295810358705651712:ℚ)⟩ node584 node358
def node586 : BoxExpr 3 := .add ⟨(2577777538541481203427/1180591620717411303424:ℚ),(2577777538541481203447/1180591620717411303424:ℚ)⟩ node585 node361
def node587 : BoxExpr 3 := .add ⟨(2577773996766619051193/1180591620717411303424:ℚ),(10311095987066476204853/4722366482869645213696:ℚ)⟩ node586 node325
def node588 : BoxExpr 3 := .mul ⟨(2025/16384:ℚ),(2025/16384:ℚ)⟩ node576 node576
def node589 : BoxExpr 3 := .neg ⟨(-2025/16384:ℚ),(-2025/16384:ℚ)⟩ node588
def node590 : BoxExpr 3 := .add ⟨(14359/16384:ℚ),(14359/16384:ℚ)⟩ node12 node589
def node591 : BoxExpr 3 := .sqrt ⟨(4420911447481279463439/4722366482869645213696:ℚ),(276306965467579966465/295147905179352825856:ℚ)⟩ node590
def node592 : BoxExpr 3 := .mul ⟨(2738095657172683921805/1180591620717411303424:ℚ),(10952382628690735687231/4722366482869645213696:ℚ)⟩ node50 node591
def node593 : BoxExpr 3 := .neg ⟨(45/128:ℚ),(45/128:ℚ)⟩ node576
def node594 : BoxExpr 3 := .add ⟨(1542147804562118515097/4722366482869645213696:ℚ),(771073902281059257549/2361183241434822606848:ℚ)⟩ node332 node593
def node595 : BoxExpr 3 := .mul ⟨(550546766228676309889/2361183241434822606848:ℚ),(275273383114338154945/1180591620717411303424:ℚ)⟩ node594 node335
def node596 : BoxExpr 3 := .neg ⟨(-275273383114338154945/1180591620717411303424:ℚ),(-550546766228676309889/2361183241434822606848:ℚ)⟩ node595
def node597 : BoxExpr 3 := .add ⟨(615705568514586441715/295147905179352825856:ℚ),(9851289096233383067453/4722366482869645213696:ℚ)⟩ node592 node596
def node598 : BoxExpr 3 := .mul ⟨(251803821213658413793/2361183241434822606848:ℚ),(503607642427316827587/4722366482869645213696:ℚ)⟩ node594 node594
def node599 : BoxExpr 3 := .mul ⟨(415979912644963699585/4722366482869645213696:ℚ),(415979912644963699587/4722366482869645213696:ℚ)⟩ node598 node340
def node600 : BoxExpr 3 := .add ⟨(10267269008878346767025/4722366482869645213696:ℚ),(160426078263724168235/73786976294838206464:ℚ)⟩ node597 node599
def node601 : BoxExpr 3 := .neg ⟨(-160426078263724168235/73786976294838206464:ℚ),(-10267269008878346767025/4722366482869645213696:ℚ)⟩ node600
def node602 : BoxExpr 3 := .add ⟨(10956744547032359433/1180591620717411303424:ℚ),(10956744547032359457/1180591620717411303424:ℚ)⟩ node587 node601
def node603 : BoxExpr 3 := .mul ⟨(962781251390620578911/4722366482869645213696:ℚ),(240695312847655144729/1180591620717411303424:ℚ)⟩ node78 node578
def node604 : BoxExpr 3 := .mul ⟨(1145649023663125762697/4722366482869645213696:ℚ),(1145649023663125762705/4722366482869645213696:ℚ)⟩ node603 node349
def node605 : BoxExpr 3 := .add ⟨(2512440180472248375145/2361183241434822606848:ℚ),(2512440180472248375359/2361183241434822606848:ℚ)⟩ node604 node385
def node606 : BoxExpr 3 := .add ⟨(333876787553967862691/590295810358705651712:ℚ),(1335507150215871450979/2361183241434822606848:ℚ)⟩ node605 node387
def node607 : BoxExpr 3 := .mul ⟨(1367293227675280870713/2361183241434822606848:ℚ),(2734586455350561741435/4722366482869645213696:ℚ)⟩ node77 node591
def node608 : BoxExpr 3 := .neg ⟨(-2734586455350561741435/4722366482869645213696:ℚ),(-1367293227675280870713/2361183241434822606848:ℚ)⟩ node607
def node609 : BoxExpr 3 := .add ⟨(-63572154918818839907/4722366482869645213696:ℚ),(-15893038729704709867/1180591620717411303424:ℚ)⟩ node606 node608
def node610 : BoxExpr 3 := .mul ⟨(-202419053818096266207/590295810358705651712:ℚ),(-809676215272385064823/2361183241434822606848:ℚ)⟩ node98 node578
def node611 : BoxExpr 3 := .mul ⟨(-3494963472473980231973/4722366482869645213696:ℚ),(-873740868118495057991/1180591620717411303424:ℚ)⟩ node68 node576
def node612 : BoxExpr 3 := .add ⟨(-5114315903018750361629/4722366482869645213696:ℚ),(-2557157951509375180805/2361183241434822606848:ℚ)⟩ node610 node611
def node613 : BoxExpr 3 := .mul ⟨(-6085713668120676500609/4722366482869645213696:ℚ),(-6085713668120676500583/4722366482869645213696:ℚ)⟩ node612 node349
def node614 : BoxExpr 3 := .mul ⟨(4043997620718253745675/4722366482869645213696:ℚ),(4043997620718253745699/4722366482869645213696:ℚ)⟩ node579 node399
def node615 : BoxExpr 3 := .add ⟨(-1020858023701211377467/2361183241434822606848:ℚ),(-510429011850605688721/1180591620717411303424:ℚ)⟩ node613 node614
def node616 : BoxExpr 3 := .mul ⟨(16072888595704088515/4722366482869645213696:ℚ),(16072888595704088517/4722366482869645213696:ℚ)⟩ node582 node103
def node617 : BoxExpr 3 := .add ⟨(-47642869935031057509/2361183241434822606848:ℚ),(-47642869935031057507/2361183241434822606848:ℚ)⟩ node403 node616
def node618 : BoxExpr 3 := .add ⟨(-33390652926132576093/73786976294838206464:ℚ),(-1068500893636242434949/2361183241434822606848:ℚ)⟩ node615 node617
def node619 : BoxExpr 3 := .add ⟨(-907542276323908019839/2361183241434822606848:ℚ),(-453771138161954009877/1180591620717411303424:ℚ)⟩ node618 node409
def node620 : BoxExpr 3 := .add ⟨(-45/64:ℚ),(-45/64:ℚ)⟩ node576 node576
def node621 : BoxExpr 3 := .neg ⟨(45/64:ℚ),(45/64:ℚ)⟩ node620
def node622 : BoxExpr 3 := .mul ⟨(4420911447481279463439/2361183241434822606848:ℚ),(276306965467579966465/147573952589676412928:ℚ)⟩ node86 node591
def node623 : BoxExpr 3 := .inv ⟨(2522188632757618313565/4722366482869645213696:ℚ),(2522188632757618313567/4722366482869645213696:ℚ)⟩ node622
def node624 : BoxExpr 3 := .mul ⟨(1773413882407700376725/4722366482869645213696:ℚ),(1773413882407700376727/4722366482869645213696:ℚ)⟩ node621 node623
def node625 : BoxExpr 3 := .mul ⟨(4393462214726557389675/4722366482869645213696:ℚ),(1098365553681639347421/1180591620717411303424:ℚ)⟩ node50 node624
def node626 : BoxExpr 3 := .add ⟨(7765231883495484072253/4722366482869645213696:ℚ),(7765231883495484072263/4722366482869645213696:ℚ)⟩ node625 node335
def node627 : BoxExpr 3 := .mul ⟨(-771073902281059257549/2361183241434822606848:ℚ),(-1542147804562118515097/4722366482869645213696:ℚ)⟩ node422 node594
def node628 : BoxExpr 3 := .mul ⟨(-771073902281059257549/2361183241434822606848:ℚ),(-1542147804562118515097/4722366482869645213696:ℚ)⟩ node594 node422
def node629 : BoxExpr 3 := .add ⟨(-771073902281059257549/1180591620717411303424:ℚ),(-1542147804562118515097/2361183241434822606848:ℚ)⟩ node627 node628
def node630 : BoxExpr 3 := .mul ⟨(-1273814086568309893471/2361183241434822606848:ℚ),(-2547628173136619786939/4722366482869645213696:ℚ)⟩ node629 node340
def node631 : BoxExpr 3 := .add ⟨(5217603710358864285311/4722366482869645213696:ℚ),(1304400927589716071331/1180591620717411303424:ℚ)⟩ node626 node630
def node632 : BoxExpr 3 := .neg ⟨(-1304400927589716071331/1180591620717411303424:ℚ),(-5217603710358864285311/4722366482869645213696:ℚ)⟩ node631
def node633 : BoxExpr 3 := .add ⟨(-714178008479229871725/4722366482869645213696:ℚ),(-714178008479229871693/4722366482869645213696:ℚ)⟩ node414 node632
def node634 : BoxExpr 3 := .mul ⟨(7382042396136127105181/4722366482869645213696:ℚ),(1982951620616578556683/1180591620717411303424:ℚ)⟩ node112 node551
def node635 : BoxExpr 3 := .mul ⟨(2191883600202682773385/1180591620717411303424:ℚ),(4728188748484803144443/2361183241434822606848:ℚ)⟩ node634 node304
def node636 : BoxExpr 3 := .add ⟨(20093745319673515256263/4722366482869645213696:ℚ),(43782727109630424703167/4722366482869645213696:ℚ)⟩ node635 node448
def node637 : BoxExpr 3 := .mul ⟨(5369805442501428587489/1180591620717411303424:ℚ),(21997577825254324706507/4722366482869645213696:ℚ)⟩ node111 node564
def node638 : BoxExpr 3 := .neg ⟨(-21997577825254324706507/4722366482869645213696:ℚ),(-5369805442501428587489/1180591620717411303424:ℚ)⟩ node637
def node639 : BoxExpr 3 := .add ⟨(-475958126395202362561/1180591620717411303424:ℚ),(22303505339624710353211/4722366482869645213696:ℚ)⟩ node636 node638
def node640 : BoxExpr 3 := .mul ⟨(-487827762763034179311/4722366482869645213696:ℚ),(-428541210831854573179/4722366482869645213696:ℚ)⟩ node131 node551
def node641 : BoxExpr 3 := .mul ⟨(-1046261700948603310121/4722366482869645213696:ℚ),(-840546335022587883893/4722366482869645213696:ℚ)⟩ node118 node549
def node642 : BoxExpr 3 := .add ⟨(-191761182963954686179/590295810358705651712:ℚ),(-79317971615902653567/295147905179352825856:ℚ)⟩ node640 node641
def node643 : BoxExpr 3 := .mul ⟨(-1828956507581122771591/4722366482869645213696:ℚ),(-1507275103397294194097/4722366482869645213696:ℚ)⟩ node642 node304
def node644 : BoxExpr 3 := .mul ⟨(905946397732214425909/4722366482869645213696:ℚ),(1021005935245441493665/4722366482869645213696:ℚ)⟩ node118 node551
def node645 : BoxExpr 3 := .mul ⟨(508004620213941119699/2361183241434822606848:ℚ),(291350039849669670777/1180591620717411303424:ℚ)⟩ node644 node461
def node646 : BoxExpr 3 := .add ⟨(-812947267153240532193/4722366482869645213696:ℚ),(-341874943998615510989/4722366482869645213696:ℚ)⟩ node643 node645
def node647 : BoxExpr 3 := .add ⟨(-446280999005963921769/590295810358705651712:ℚ),(1071698936573044261915/4722366482869645213696:ℚ)⟩ node646 node476
def node648 : BoxExpr 3 := .add ⟨(-900201110797026118861/1180591620717411303424:ℚ),(-760005855836833526579/1180591620717411303424:ℚ)⟩ node549 node549
def node649 : BoxExpr 3 := .neg ⟨(760005855836833526579/1180591620717411303424:ℚ),(900201110797026118861/1180591620717411303424:ℚ)⟩ node648
def node650 : BoxExpr 3 := .mul ⟨(2182847740854239263207/1180591620717411303424:ℚ),(4471052403506976566363/2361183241434822606848:ℚ)⟩ node86 node564
def node651 : BoxExpr 3 := .inv ⟨(2493903357187057556815/4722366482869645213696:ℚ),(1277044247128948424017/2361183241434822606848:ℚ)⟩ node650
def node652 : BoxExpr 3 := .mul ⟨(1605450286189168302199/4722366482869645213696:ℚ),(1947492476871646346627/4722366482869645213696:ℚ)⟩ node649 node651
def node653 : BoxExpr 3 := .mul ⟨(969366332686027194277/4722366482869645213696:ℚ),(1233380415932504657089/4722366482869645213696:ℚ)⟩ node117 node652
def node654 : BoxExpr 3 := .neg ⟨(-1233380415932504657089/4722366482869645213696:ℚ),(-969366332686027194277/4722366482869645213696:ℚ)⟩ node653
def node655 : BoxExpr 3 := .add ⟨(-224911913070340571/2361183241434822606848:ℚ),(344328814043233507449/4722366482869645213696:ℚ)⟩ node479 node654
def node656 : BoxExpr 3 := .add ⟨(-3570247992047711374151/4722366482869645213696:ℚ),(1071698936573044261915/4722366482869645213696:ℚ)⟩ node646 node492
def node657 : BoxExpr 3 := .mul ⟨(-1805109769351620584625/4722366482869645213696:ℚ),(-822622328100175265181/2361183241434822606848:ℚ)⟩ node175 node551
def node658 : BoxExpr 3 := .mul ⟨(44751370282727518709/147573952589676412928:ℚ),(217265231086748747587/590295810358705651712:ℚ)⟩ node148 node549
def node659 : BoxExpr 3 := .add ⟨(-373065920304339985937/4722366482869645213696:ℚ),(46438596246819725167/2361183241434822606848:ℚ)⟩ node657 node658
def node660 : BoxExpr 3 := .add ⟨(1058977928742940612751/4722366482869645213696:ℚ),(915499520593814715515/2361183241434822606848:ℚ)⟩ node659 node658
def node661 : BoxExpr 3 := .mul ⟨(1257731251287955296013/4722366482869645213696:ℚ),(1091467509219653866193/2361183241434822606848:ℚ)⟩ node660 node304
def node662 : BoxExpr 3 := .mul ⟨(-212020654355329435689/590295810358705651712:ℚ),(-1543466329436907565119/4722366482869645213696:ℚ)⟩ node148 node551
def node663 : BoxExpr 3 := .mul ⟨(-3803294876519270495949/4722366482869645213696:ℚ),(-1594374214105143278659/2361183241434822606848:ℚ)⟩ node36 node549
def node664 : BoxExpr 3 := .add ⟨(-5499460111361905981461/4722366482869645213696:ℚ),(-4732214757647194122437/4722366482869645213696:ℚ)⟩ node662 node663
def node665 : BoxExpr 3 := .mul ⟨(-3138606480699425085633/2361183241434822606848:ℚ),(-2653564235971449262785/2361183241434822606848:ℚ)⟩ node664 node461
def node666 : BoxExpr 3 := .add ⟨(-5019481710110894875253/4722366482869645213696:ℚ),(-97631045421987212287/147573952589676412928:ℚ)⟩ node661 node665
def node667 : BoxExpr 3 := .mul ⟨(16947522863042239353463/4722366482869645213696:ℚ),(18693490208013954622851/4722366482869645213696:ℚ)⟩ node552 node514
def node668 : BoxExpr 3 := .add ⟨(10670309901643389182197/4722366482869645213696:ℚ),(13386361736071056097281/4722366482869645213696:ℚ)⟩ node665 node667
def node669 : BoxExpr 3 := .add ⟨(44147095246347611773/36893488147419103232:ℚ),(10262168282567465304097/4722366482869645213696:ℚ)⟩ node666 node668
def node670 : BoxExpr 3 := .mul ⟨(25002274696629451483/2361183241434822606848:ℚ),(76504408909700015093/4722366482869645213696:ℚ)⟩ node555 node189
def node671 : BoxExpr 3 := .add ⟨(-1676898142920848769/2361183241434822606848:ℚ),(23978136838069229159/4722366482869645213696:ℚ)⟩ node518 node670
def node672 : BoxExpr 3 := .add ⟨(-28356070982471149021/2361183241434822606848:ℚ),(-28548135233561556775/4722366482869645213696:ℚ)⟩ node518 node671
def node673 : BoxExpr 3 := .add ⟨(2797058024783776004451/2361183241434822606848:ℚ),(5116810073666951873661/2361183241434822606848:ℚ)⟩ node669 node672
def node674 : BoxExpr 3 := .add ⟨(16697849327934123380425/4722366482869645213696:ℚ),(26827091186661350221865/4722366482869645213696:ℚ)⟩ node673 node527
def node675 : BoxExpr 3 := .mul ⟨(-1277044247128948424017/1180591620717411303424:ℚ),(-2493903357187057556815/2361183241434822606848:ℚ)⟩ node6 node651
def node676 : BoxExpr 3 := .mul ⟨(1605450286189168302199/2361183241434822606848:ℚ),(1947492476871646346627/2361183241434822606848:ℚ)⟩ node86 node652
def node677 : BoxExpr 3 := .mul ⟨(16143852543547651192249/4722366482869645213696:ℚ),(4233112713174683630963/1180591620717411303424:ℚ)⟩ node650 node650
def node678 : BoxExpr 3 := .inv ⟨(1317041779275341999439/4722366482869645213696:ℚ),(1381376913495394184729/4722366482869645213696:ℚ)⟩ node677
def node679 : BoxExpr 3 := .mul ⟨(223875583262208215055/1180591620717411303424:ℚ),(1139352973351481934131/4722366482869645213696:ℚ)⟩ node676 node678
def node680 : BoxExpr 3 := .neg ⟨(-1139352973351481934131/4722366482869645213696:ℚ),(-223875583262208215055/1180591620717411303424:ℚ)⟩ node679
def node681 : BoxExpr 3 := .mul ⟨(-108594580272563121847/590295810358705651712:ℚ),(-288239813450093076883/2361183241434822606848:ℚ)⟩ node649 node680
def node682 : BoxExpr 3 := .add ⟨(-1494233407674074667711/1180591620717411303424:ℚ),(-1391071585318575316849/1180591620717411303424:ℚ)⟩ node675 node681
def node683 : BoxExpr 3 := .mul ⟨(-3704625346455217096987/1180591620717411303424:ℚ),(-6887390795896785788767/2361183241434822606848:ℚ)⟩ node11 node682
def node684 : BoxExpr 3 := .add ⟨(-7017151956120214494923/4722366482869645213696:ℚ),(-1493358040523229421127/1180591620717411303424:ℚ)⟩ node683 node546
def node685 : BoxExpr 3 := .neg ⟨(1493358040523229421127/1180591620717411303424:ℚ),(7017151956120214494923/4722366482869645213696:ℚ)⟩ node684
def cert_iv1 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-45/128:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/640:ℚ)],
    whole := node575, centerValue := node602, gradient := ![node609, node619, node633],
    hessian := ![![node639, node647, node655], ![node656, node674, node536], ![node655, node536, node685]] }
def node686 : BoxExpr 3 := .var 2
def node687 : BoxExpr 3 := .mul ⟨(-610321069704688264073/4722366482869645213696:ℚ),(-30798692912664722119/295147905179352825856:ℚ)⟩ node13 node686
def node688 : BoxExpr 3 := .add ⟨(1750862171730134342775/4722366482869645213696:ℚ),(116775259677011690809/295147905179352825856:ℚ)⟩ node687 node301
def node689 : BoxExpr 3 := .mul ⟨(3673036829413553648057/4722366482869645213696:ℚ),(3946946890039346479039/4722366482869645213696:ℚ)⟩ node36 node688
def node690 : BoxExpr 3 := .mul ⟨(4362407451653745108469/4722366482869645213696:ℚ),(4705588800635588189647/4722366482869645213696:ℚ)⟩ node689 node304
def node691 : BoxExpr 3 := .add ⟨(-145346220012399832859/1180591620717411303424:ℚ),(-291549637163474856443/4722366482869645213696:ℚ)⟩ node686 node306
def node692 : BoxExpr 3 := .mul ⟨(12605053812834083873/4722366482869645213696:ℚ),(12567993173121643769/2361183241434822606848:ℚ)⟩ node691 node308
def node693 : BoxExpr 3 := .mul ⟨(26830280610169781/9223372036854775808:ℚ),(13722785709733409879/2361183241434822606848:ℚ)⟩ node692 node37
def node694 : BoxExpr 3 := .add ⟨(4376144555326152036341/4722366482869645213696:ℚ),(4733034372055055009405/4722366482869645213696:ℚ)⟩ node690 node693
def node695 : BoxExpr 3 := .add ⟨(3772647202616384599037/1180591620717411303424:ℚ),(15574798368914845506647/4722366482869645213696:ℚ)⟩ node694 node316
def node696 : BoxExpr 3 := .add ⟨(1291080322187964630473/590295810358705651712:ℚ),(5413487666158050338691/2361183241434822606848:ℚ)⟩ node695 node323
def node697 : BoxExpr 3 := .add ⟨(322769637825133388589/147573952589676412928:ℚ),(10826961165216652068447/4722366482869645213696:ℚ)⟩ node696 node325
def node698 : BoxExpr 3 := .mul ⟨(162700282730118245253/2361183241434822606848:ℚ),(30578360605935098921/295147905179352825856:ℚ)⟩ node686 node686
def node699 : BoxExpr 3 := .neg ⟨(-30578360605935098921/295147905179352825856:ℚ),(-162700282730118245253/2361183241434822606848:ℚ)⟩ node698
def node700 : BoxExpr 3 := .add ⟨(264569544573417726935/295147905179352825856:ℚ),(2198482958704704361595/2361183241434822606848:ℚ)⟩ node12 node699
def node701 : BoxExpr 3 := .sqrt ⟨(4471052403506976566361/4722366482869645213696:ℚ),(2278381249631762813519/2361183241434822606848:ℚ)⟩ node700
def node702 : BoxExpr 3 := .mul ⟨(11068404206112049806475/4722366482869645213696:ℚ),(2824374318940140461887/1180591620717411303424:ℚ)⟩ node11 node701
def node703 : BoxExpr 3 := .neg ⟨(1239621201753281868595/4722366482869645213696:ℚ),(1520011711673667053159/4722366482869645213696:ℚ)⟩ node686
def node704 : BoxExpr 3 := .add ⟨(280390509920385184563/1180591620717411303424:ℚ),(1401952549601925922817/4722366482869645213696:ℚ)⟩ node332 node703
def node705 : BoxExpr 3 := .mul ⟨(800795296332620087111/4722366482869645213696:ℚ),(250248530103943777223/1180591620717411303424:ℚ)⟩ node704 node335
def node706 : BoxExpr 3 := .neg ⟨(-250248530103943777223/1180591620717411303424:ℚ),(-800795296332620087111/4722366482869645213696:ℚ)⟩ node705
def node707 : BoxExpr 3 := .add ⟨(10067410085696274697583/4722366482869645213696:ℚ),(10496701979427941760437/4722366482869645213696:ℚ)⟩ node702 node706
def node708 : BoxExpr 3 := .mul ⟨(133185492212182962667/2361183241434822606848:ℚ),(416204663163071758337/4722366482869645213696:ℚ)⟩ node704 node704
def node709 : BoxExpr 3 := .mul ⟨(220022433134526254325/4722366482869645213696:ℚ),(343785051772697272387/4722366482869645213696:ℚ)⟩ node708 node340
def node710 : BoxExpr 3 := .add ⟨(2571858129707700237977/1180591620717411303424:ℚ),(1355060878900079879103/590295810358705651712:ℚ)⟩ node707 node709
def node711 : BoxExpr 3 := .neg ⟨(-1355060878900079879103/590295810358705651712:ℚ),(-2571858129707700237977/1180591620717411303424:ℚ)⟩ node710
def node712 : BoxExpr 3 := .add ⟨(-63982327599546324747/590295810358705651712:ℚ),(539528646385851116539/4722366482869645213696:ℚ)⟩ node697 node711
def node713 : BoxExpr 3 := .var 2
def node714 : BoxExpr 3 := .mul ⟨(-551269687643741523805/4722366482869645213696:ℚ),(-551269687643741523803/4722366482869645213696:ℚ)⟩ node51 node713
def node715 : BoxExpr 3 := .add ⟨(1809913553791081083043/4722366482869645213696:ℚ),(1809913553791081083045/4722366482869645213696:ℚ)⟩ node714 node301
def node716 : BoxExpr 3 := .mul ⟨(3810116380646676393095/4722366482869645213696:ℚ),(3810116380646676393109/4722366482869645213696:ℚ)⟩ node68 node715
def node717 : BoxExpr 3 := .mul ⟨(4533798414983625691007/4722366482869645213696:ℚ),(2266899207491812845513/2361183241434822606848:ℚ)⟩ node716 node349
def node718 : BoxExpr 3 := .add ⟨(-109116814651634273485/1180591620717411303424:ℚ),(-218233629303268546969/2361183241434822606848:ℚ)⟩ node713 node351
def node719 : BoxExpr 3 := .mul ⟨(18870520079538685705/4722366482869645213696:ℚ),(9435260039769342853/2361183241434822606848:ℚ)⟩ node718 node308
def node720 : BoxExpr 3 := .mul ⟨(20584762095423554931/4722366482869645213696:ℚ),(20584762095423554933/4722366482869645213696:ℚ)⟩ node719 node69
def node721 : BoxExpr 3 := .add ⟨(2277191588539524622969/2361183241434822606848:ℚ),(4554383177079049245959/4722366482869645213696:ℚ)⟩ node717 node720
def node722 : BoxExpr 3 := .add ⟨(7666692844997655598917/2361183241434822606848:ℚ),(3833346422498827799477/1180591620717411303424:ℚ)⟩ node721 node358
def node723 : BoxExpr 3 := .add ⟨(10578501055215028107017/4722366482869645213696:ℚ),(1322312631901878513387/590295810358705651712:ℚ)⟩ node722 node361
def node724 : BoxExpr 3 := .add ⟨(10578486888115579498081/4722366482869645213696:ℚ),(10578486888115579498161/4722366482869645213696:ℚ)⟩ node723 node325
def node725 : BoxExpr 3 := .mul ⟨(100791280236492079759/1180591620717411303424:ℚ),(201582560472984159519/2361183241434822606848:ℚ)⟩ node713 node713
def node726 : BoxExpr 3 := .neg ⟨(-201582560472984159519/2361183241434822606848:ℚ),(-100791280236492079759/1180591620717411303424:ℚ)⟩ node725
def node727 : BoxExpr 3 := .add ⟨(2159600680961838447329/2361183241434822606848:ℚ),(1079800340480919223665/1180591620717411303424:ℚ)⟩ node12 node726
def node728 : BoxExpr 3 := .sqrt ⟨(1129071846261158428969/1180591620717411303424:ℚ),(2258143692522316857939/2361183241434822606848:ℚ)⟩ node727
def node729 : BoxExpr 3 := .mul ⟨(2797166833680817129785/1180591620717411303424:ℚ),(5594333667361634259577/2361183241434822606848:ℚ)⟩ node50 node728
def node730 : BoxExpr 3 := .neg ⟨(344954114178368615219/1180591620717411303424:ℚ),(1379816456713474460877/4722366482869645213696:ℚ)⟩ node713
def node731 : BoxExpr 3 := .add ⟨(1261757294641733330533/4722366482869645213696:ℚ),(1261757294641733330535/4722366482869645213696:ℚ)⟩ node332 node730
def node732 : BoxExpr 3 := .mul ⟨(56305919273387349875/295147905179352825856:ℚ),(900894708374197598003/4722366482869645213696:ℚ)⟩ node731 node335
def node733 : BoxExpr 3 := .neg ⟨(-900894708374197598003/4722366482869645213696:ℚ),(-56305919273387349875/295147905179352825856:ℚ)⟩ node732
def node734 : BoxExpr 3 := .add ⟨(10287772626349070921137/4722366482869645213696:ℚ),(5143886313174535460577/2361183241434822606848:ℚ)⟩ node729 node733
def node735 : BoxExpr 3 := .mul ⟨(337125777162088124251/4722366482869645213696:ℚ),(337125777162088124253/4722366482869645213696:ℚ)⟩ node731 node731
def node736 : BoxExpr 3 := .mul ⟨(278465891935884790631/4722366482869645213696:ℚ),(278465891935884790633/4722366482869645213696:ℚ)⟩ node735 node340
def node737 : BoxExpr 3 := .add ⟨(1320779814785619463971/590295810358705651712:ℚ),(10566238518284955711787/4722366482869645213696:ℚ)⟩ node734 node736
def node738 : BoxExpr 3 := .neg ⟨(-10566238518284955711787/4722366482869645213696:ℚ),(-1320779814785619463971/590295810358705651712:ℚ)⟩ node737
def node739 : BoxExpr 3 := .add ⟨(6124184915311893147/2361183241434822606848:ℚ),(12248369830623786393/4722366482869645213696:ℚ)⟩ node724 node738
def node740 : BoxExpr 3 := .mul ⟨(1026303222063194339127/4722366482869645213696:ℚ),(1026303222063194339133/4722366482869645213696:ℚ)⟩ node78 node715
def node741 : BoxExpr 3 := .mul ⟨(1221236166201556793237/4722366482869645213696:ℚ),(610618083100778396623/2361183241434822606848:ℚ)⟩ node740 node349
def node742 : BoxExpr 3 := .add ⟨(2550233751741463890415/2361183241434822606848:ℚ),(5100467503482927781259/4722366482869645213696:ℚ)⟩ node741 node385
def node743 : BoxExpr 3 := .add ⟨(686650360742543483017/1180591620717411303424:ℚ),(2746601442970173932499/4722366482869645213696:ℚ)⟩ node742 node387
def node744 : BoxExpr 3 := .mul ⟨(2793581924978369486537/4722366482869645213696:ℚ),(1396790962489184743273/2361183241434822606848:ℚ)⟩ node77 node728
def node745 : BoxExpr 3 := .neg ⟨(-1396790962489184743273/2361183241434822606848:ℚ),(-2793581924978369486537/4722366482869645213696:ℚ)⟩ node744
def node746 : BoxExpr 3 := .add ⟨(-23490241004097777239/2361183241434822606848:ℚ),(-23490241004097777019/2361183241434822606848:ℚ)⟩ node743 node745
def node747 : BoxExpr 3 := .mul ⟨(-1726193374376040950517/4722366482869645213696:ℚ),(-1726193374376040950507/4722366482869645213696:ℚ)⟩ node98 node715
def node748 : BoxExpr 3 := .mul ⟨(-2904702974900596903907/4722366482869645213696:ℚ),(-2904702974900596903897/4722366482869645213696:ℚ)⟩ node68 node713
def node749 : BoxExpr 3 := .add ⟨(-578862043659579731803/590295810358705651712:ℚ),(-1157724087319159463601/1180591620717411303424:ℚ)⟩ node747 node748
def node750 : BoxExpr 3 := .mul ⟨(-5510474859757534589177/4722366482869645213696:ℚ),(-2755237429878767294575/2361183241434822606848:ℚ)⟩ node749 node349
def node751 : BoxExpr 3 := .mul ⟨(269425673158124792183/295147905179352825856:ℚ),(538851346316249584369/590295810358705651712:ℚ)⟩ node716 node399
def node752 : BoxExpr 3 := .add ⟨(-1199664089227537914249/4722366482869645213696:ℚ),(-599832044613768957099/2361183241434822606848:ℚ)⟩ node750 node751
def node753 : BoxExpr 3 := .mul ⟨(2446541675090939371/1180591620717411303424:ℚ),(9786166700363757485/4722366482869645213696:ℚ)⟩ node719 node103
def node754 : BoxExpr 3 := .add ⟨(-101572461765402446049/4722366482869645213696:ℚ),(-50786230882701223023/2361183241434822606848:ℚ)⟩ node403 node753
def node755 : BoxExpr 3 := .add ⟨(-650618275496470180149/2361183241434822606848:ℚ),(-325309137748235090061/1180591620717411303424:ℚ)⟩ node752 node754
def node756 : BoxExpr 3 := .add ⟨(-122414914546033941253/590295810358705651712:ℚ),(-489659658184135764927/2361183241434822606848:ℚ)⟩ node755 node409
def node757 : BoxExpr 3 := .add ⟨(-1379816456713474460877/2361183241434822606848:ℚ),(-344954114178368615219/590295810358705651712:ℚ)⟩ node713 node713
def node758 : BoxExpr 3 := .neg ⟨(344954114178368615219/590295810358705651712:ℚ),(1379816456713474460877/2361183241434822606848:ℚ)⟩ node757
def node759 : BoxExpr 3 := .mul ⟨(1129071846261158428969/590295810358705651712:ℚ),(2258143692522316857939/1180591620717411303424:ℚ)⟩ node86 node728
def node760 : BoxExpr 3 := .inv ⟨(2468924505599218924785/4722366482869645213696:ℚ),(2468924505599218924787/4722366482869645213696:ℚ)⟩ node759
def node761 : BoxExpr 3 := .mul ⟨(721388878979771779585/2361183241434822606848:ℚ),(1442777757959543559173/4722366482869645213696:ℚ)⟩ node758 node760
def node762 : BoxExpr 3 := .mul ⟨(1787171518934205626829/2361183241434822606848:ℚ),(3574343037868411253669/4722366482869645213696:ℚ)⟩ node50 node761
def node763 : BoxExpr 3 := .add ⟨(1736528176659334484059/1180591620717411303424:ℚ),(868264088329667242031/590295810358705651712:ℚ)⟩ node762 node335
def node764 : BoxExpr 3 := .mul ⟨(-1261757294641733330535/4722366482869645213696:ℚ),(-1261757294641733330533/4722366482869645213696:ℚ)⟩ node422 node731
def node765 : BoxExpr 3 := .mul ⟨(-1261757294641733330535/4722366482869645213696:ℚ),(-1261757294641733330533/4722366482869645213696:ℚ)⟩ node731 node422
def node766 : BoxExpr 3 := .add ⟨(-1261757294641733330535/2361183241434822606848:ℚ),(-1261757294641733330533/2361183241434822606848:ℚ)⟩ node764 node765
def node767 : BoxExpr 3 := .mul ⟨(-521105762687035865511/1180591620717411303424:ℚ),(-260552881343517932755/590295810358705651712:ℚ)⟩ node766 node340
def node768 : BoxExpr 3 := .add ⟨(303855603493074654637/295147905179352825856:ℚ),(151927801746537327319/147573952589676412928:ℚ)⟩ node763 node767
def node769 : BoxExpr 3 := .neg ⟨(-151927801746537327319/147573952589676412928:ℚ),(-303855603493074654637/295147905179352825856:ℚ)⟩ node768
def node770 : BoxExpr 3 := .add ⟨(-358263954009560060609/4722366482869645213696:ℚ),(-179131977004780030287/2361183241434822606848:ℚ)⟩ node414 node769
def node771 : BoxExpr 3 := .mul ⟨(3944670400427721781493/2361183241434822606848:ℚ),(8435007156450138584877/4722366482869645213696:ℚ)⟩ node112 node688
def node772 : BoxExpr 3 := .mul ⟨(4685022325760716730155/2361183241434822606848:ℚ),(10056298276736409514321/4722366482869645213696:ℚ)⟩ node771 node304
def node773 : BoxExpr 3 := .add ⟨(20696255570384217623033/4722366482869645213696:ℚ),(22191323944698613964301/2361183241434822606848:ℚ)⟩ node772 node448
def node774 : BoxExpr 3 := .mul ⟨(21997577825254324706495/4722366482869645213696:ℚ),(5604817874094136521257/1180591620717411303424:ℚ)⟩ node111 node701
def node775 : BoxExpr 3 := .neg ⟨(-5604817874094136521257/1180591620717411303424:ℚ),(-21997577825254324706495/4722366482869645213696:ℚ)⟩ node774
def node776 : BoxExpr 3 := .add ⟨(-1723015925992328461995/4722366482869645213696:ℚ),(22385070064142903222107/4722366482869645213696:ℚ)⟩ node773 node775
def node777 : BoxExpr 3 := .mul ⟨(-64846997325220123705/590295810358705651712:ℚ),(-457990821243909864891/4722366482869645213696:ℚ)⟩ node131 node688
def node778 : BoxExpr 3 := .mul ⟨(-883319304899230663463/4722366482869645213696:ℚ),(-171373524616255782153/1180591620717411303424:ℚ)⟩ node118 node686
def node779 : BoxExpr 3 := .add ⟨(-1402095283500991653103/4722366482869645213696:ℚ),(-1143484919708932993503/4722366482869645213696:ℚ)⟩ node777 node778
def node780 : BoxExpr 3 := .mul ⟨(-835795875555912922975/2361183241434822606848:ℚ),(-1358098861042018420931/4722366482869645213696:ℚ)⟩ node779 node304
def node781 : BoxExpr 3 := .mul ⟨(484101790227985437351/2361183241434822606848:ℚ),(542889718099595674433/2361183241434822606848:ℚ)⟩ node118 node688
def node782 : BoxExpr 3 := .mul ⟨(1085830008067868657879/4722366482869645213696:ℚ),(309833538752681453133/1180591620717411303424:ℚ)⟩ node781 node461
def node783 : BoxExpr 3 := .add ⟨(-585761743043957188071/4722366482869645213696:ℚ),(-118764706031292608399/4722366482869645213696:ℚ)⟩ node780 node782
def node784 : BoxExpr 3 := .add ⟨(-1671531233969214015015/2361183241434822606848:ℚ),(1294809174540367164505/4722366482869645213696:ℚ)⟩ node783 node476
def node785 : BoxExpr 3 := .add ⟨(-1520011711673667053159/2361183241434822606848:ℚ),(-1239621201753281868595/2361183241434822606848:ℚ)⟩ node686 node686
def node786 : BoxExpr 3 := .neg ⟨(1239621201753281868595/2361183241434822606848:ℚ),(1520011711673667053159/2361183241434822606848:ℚ)⟩ node785
def node787 : BoxExpr 3 := .mul ⟨(4471052403506976566361/2361183241434822606848:ℚ),(2278381249631762813519/1180591620717411303424:ℚ)⟩ node86 node701
def node788 : BoxExpr 3 := .inv ⟨(2446994461762591375485/4722366482869645213696:ℚ),(2493903357187057556817/4722366482869645213696:ℚ)⟩ node787
def node789 : BoxExpr 3 := .mul ⟨(1284672092425360472129/4722366482869645213696:ℚ),(802725143094584151101/2361183241434822606848:ℚ)⟩ node786 node788
def node790 : BoxExpr 3 := .mul ⟨(96960171053820654421/590295810358705651712:ℚ),(254189806283582860641/1180591620717411303424:ℚ)⟩ node117 node789
def node791 : BoxExpr 3 := .neg ⟨(-254189806283582860641/1180591620717411303424:ℚ),(-96960171053820654421/590295810358705651712:ℚ)⟩ node790
def node792 : BoxExpr 3 := .add ⟨(216171366972032533383/4722366482869645213696:ℚ),(269006889149347733179/2361183241434822606848:ℚ)⟩ node479 node791
def node793 : BoxExpr 3 := .add ⟨(-3343062467938428030029/4722366482869645213696:ℚ),(1294809174540367164505/4722366482869645213696:ℚ)⟩ node783 node492
def node794 : BoxExpr 3 := .mul ⟨(-1919627496752111136147/4722366482869645213696:ℚ),(-1758306861031397839883/4722366482869645213696:ℚ)⟩ node175 node688
def node795 : BoxExpr 3 := .mul ⟨(1167880420582248255241/4722366482869645213696:ℚ),(1467430741110499737801/4722366482869645213696:ℚ)⟩ node148 node686
def node796 : BoxExpr 3 := .add ⟨(-375873538084931440453/2361183241434822606848:ℚ),(-145438059960449051041/2361183241434822606848:ℚ)⟩ node794 node795
def node797 : BoxExpr 3 := .add ⟨(416133344412385374335/4722366482869645213696:ℚ),(1176554621189601635719/4722366482869645213696:ℚ)⟩ node796 node795
def node798 : BoxExpr 3 := .mul ⟨(30889684865275816607/295147905179352825856:ℚ),(43834373781872108705/147573952589676412928:ℚ)⟩ node797 node304
def node799 : BoxExpr 3 := .mul ⟨(-1803771426603299219867/4722366482869645213696:ℚ),(-206191783285252719425/590295810358705651712:ℚ)⟩ node148 node688
def node800 : BoxExpr 3 := .mul ⟨(-1605489230661823201159/2361183241434822606848:ℚ),(-1300266349367301314635/2361183241434822606848:ℚ)⟩ node36 node686
def node801 : BoxExpr 3 := .add ⟨(-5014749887926945622185/4722366482869645213696:ℚ),(-2125033482508312192335/2361183241434822606848:ℚ)⟩ node799 node800
def node802 : BoxExpr 3 := .mul ⟨(-2861976662912186125515/2361183241434822606848:ℚ),(-4654692241613645115/4611686018427387904:ℚ)⟩ node801 node461
def node803 : BoxExpr 3 := .add ⟨(-2614859183989979592659/2361183241434822606848:ℚ),(-105115777949764534975/147573952589676412928:ℚ)⟩ node798 node802
def node804 : BoxExpr 3 := .mul ⟨(18112166853283409882237/4722366482869645213696:ℚ),(2484927677449453437023/590295810358705651712:ℚ)⟩ node689 node514
def node805 : BoxExpr 3 := .add ⟨(12388213527459037631207/4722366482869645213696:ℚ),(1889127070522906862303/590295810358705651712:ℚ)⟩ node802 node804
def node806 : BoxExpr 3 := .add ⟨(7158495159479078445889/4722366482869645213696:ℚ),(1468663958723848722403/590295810358705651712:ℚ)⟩ node803 node805
def node807 : BoxExpr 3 := .mul ⟨(12745047105418610869/2361183241434822606848:ℚ),(25806322108351585755/2361183241434822606848:ℚ)⟩ node692 node189
def node808 : BoxExpr 3 := .add ⟨(-13934125734131689383/2361183241434822606848:ℚ),(-114203481865951803/590295810358705651712:ℚ)⟩ node518 node807
def node809 : BoxExpr 3 := .add ⟨(-40613298573681989635/2361183241434822606848:ℚ),(-26719949963279200179/2361183241434822606848:ℚ)⟩ node518 node808
def node810 : BoxExpr 3 := .add ⟨(7077268562331714466619/4722366482869645213696:ℚ),(5847935884932115689433/2361183241434822606848:ℚ)⟩ node806 node809
def node811 : BoxExpr 3 := .add ⟨(9090500920349142919071/2361183241434822606848:ℚ),(28289342809191677853409/4722366482869645213696:ℚ)⟩ node810 node527
def node812 : BoxExpr 3 := .mul ⟨(-2493903357187057556817/2361183241434822606848:ℚ),(-2446994461762591375485/2361183241434822606848:ℚ)⟩ node6 node788
def node813 : BoxExpr 3 := .mul ⟨(1284672092425360472129/2361183241434822606848:ℚ),(802725143094584151101/1180591620717411303424:ℚ)⟩ node86 node789
def node814 : BoxExpr 3 := .mul ⟨(4233112713174683630959/1180591620717411303424:ℚ),(17587863669637634892763/4722366482869645213696:ℚ)⟩ node787 node787
def node815 : BoxExpr 3 := .inv ⟨(1267962136699350955179/4722366482869645213696:ℚ),(1317041779275341999441/4722366482869645213696:ℚ)⟩ node814
def node816 : BoxExpr 3 := .mul ⟨(344936289290246141199/2361183241434822606848:ℚ),(13992223953888013441/73786976294838206464:ℚ)⟩ node813 node815
def node817 : BoxExpr 3 := .neg ⟨(-13992223953888013441/73786976294838206464:ℚ),(-344936289290246141199/2361183241434822606848:ℚ)⟩ node816
def node818 : BoxExpr 3 := .mul ⟨(-288239813450093076885/2361183241434822606848:ℚ),(-181091551877379224129/2361183241434822606848:ℚ)⟩ node786 node817
def node819 : BoxExpr 3 := .add ⟨(-1391071585318575316851/1180591620717411303424:ℚ),(-1314043006819985299807/1180591620717411303424:ℚ)⟩ node812 node818
def node820 : BoxExpr 3 := .mul ⟨(-13795432566928406965581/4722366482869645213696:ℚ),(-813251435629016298971/295147905179352825856:ℚ)⟩ node11 node819
def node821 : BoxExpr 3 := .add ⟨(-1498520784306938268139/1180591620717411303424:ℚ),(-2605336770181803445255/2361183241434822606848:ℚ)⟩ node820 node546
def node822 : BoxExpr 3 := .neg ⟨(2605336770181803445255/2361183241434822606848:ℚ),(1498520784306938268139/1180591620717411303424:ℚ)⟩ node821
def cert_iv2 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-187/640:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/640:ℚ)],
    whole := node712, centerValue := node739, gradient := ![node746, node756, node770],
    hessian := ![![node776, node784, node792], ![node793, node811, node536], ![node792, node536, node822]] }
def node823 : BoxExpr 3 := .var 2
def node824 : BoxExpr 3 := .mul ⟨(-124434392852412170345/1180591620717411303424:ℚ),(-58114200317349505427/590295810358705651712:ℚ)⟩ node13 node823
def node825 : BoxExpr 3 := .add ⟨(465861417506293481367/1180591620717411303424:ℚ),(237033704862003320429/590295810358705651712:ℚ)⟩ node824 node301
def node826 : BoxExpr 3 := .mul ⟨(3909219518318911989559/4722366482869645213696:ℚ),(4005811876707656812011/4722366482869645213696:ℚ)⟩ node36 node825
def node827 : BoxExpr 3 := .mul ⟨(290182367290398025471/295147905179352825856:ℚ),(4775768215188897011901/4722366482869645213696:ℚ)⟩ node826 node304
def node828 : BoxExpr 3 := .add ⟨(-300994370129214146873/4722366482869645213696:ℚ),(-110726004841689280151/2361183241434822606848:ℚ)⟩ node823 node306
def node829 : BoxExpr 3 := .mul ⟨(9574405669570656307/4722366482869645213696:ℚ),(13013393773189577273/4722366482869645213696:ℚ)⟩ node828 node308
def node830 : BoxExpr 3 := .mul ⟨(652142214332805981/295147905179352825856:ℚ),(14209111323180635217/4722366482869645213696:ℚ)⟩ node829 node37
def node831 : BoxExpr 3 := .add ⟨(72708627376182707863/73786976294838206464:ℚ),(2394988663256038823559/2361183241434822606848:ℚ)⟩ node827 node830
def node832 : BoxExpr 3 := .add ⟨(15367796407215079663039/4722366482869645213696:ℚ),(1953967665421483518045/590295810358705651712:ℚ)⟩ node831 node316
def node833 : BoxExpr 3 := .add ⟨(10605850174253258310675/4722366482869645213696:ℚ),(10883918286773123315095/4722366482869645213696:ℚ)⟩ node832 node323
def node834 : BoxExpr 3 := .add ⟨(10605836007153809701739/4722366482869645213696:ℚ),(680244007479604669135/295147905179352825856:ℚ)⟩ node833 node325
def node835 : BoxExpr 3 := .mul ⟨(289639822691093614427/4722366482869645213696:ℚ),(325400565460236490507/4722366482869645213696:ℚ)⟩ node823 node823
def node836 : BoxExpr 3 := .neg ⟨(-325400565460236490507/4722366482869645213696:ℚ),(-289639822691093614427/4722366482869645213696:ℚ)⟩ node835
def node837 : BoxExpr 3 := .add ⟨(4396965917409408723189/4722366482869645213696:ℚ),(4432726660178551599269/4722366482869645213696:ℚ)⟩ node12 node836
def node838 : BoxExpr 3 := .sqrt ⟨(4556762499263525627037/4722366482869645213696:ℚ),(2287627581565118726709/2361183241434822606848:ℚ)⟩ node837
def node839 : BoxExpr 3 := .mul ⟨(5640292783589531859429/2361183241434822606848:ℚ),(11343345796434943910877/4722366482869645213696:ℚ)⟩ node11 node838
def node840 : BoxExpr 3 := .neg ⟨(584761787136592786227/2361183241434822606848:ℚ),(309905300438320467149/1180591620717411303424:ℚ)⟩ node823
def node841 : BoxExpr 3 := .add ⟨(1051464412201444442111/4722366482869645213696:ℚ),(560781019840770369127/2361183241434822606848:ℚ)⟩ node332 node840
def node842 : BoxExpr 3 := .mul ⟨(750745590311831331667/4722366482869645213696:ℚ),(400397648166310043557/2361183241434822606848:ℚ)⟩ node841 node335
def node843 : BoxExpr 3 := .neg ⟨(-400397648166310043557/2361183241434822606848:ℚ),(-750745590311831331667/4722366482869645213696:ℚ)⟩ node842
def node844 : BoxExpr 3 := .add ⟨(81873361490987840873/36893488147419103232:ℚ),(5296300103061556289605/2361183241434822606848:ℚ)⟩ node839 node843
def node845 : BoxExpr 3 := .mul ⟨(234115123029227864063/4722366482869645213696:ℚ),(33296373053045740667/590295810358705651712:ℚ)⟩ node841 node841
def node846 : BoxExpr 3 := .mul ⟨(193379091622142215715/4722366482869645213696:ℚ),(27502804141815781791/590295810358705651712:ℚ)⟩ node845 node340
def node847 : BoxExpr 3 := .add ⟨(10673169362468585847459/4722366482869645213696:ℚ),(5406311319628819416769/2361183241434822606848:ℚ)⟩ node844 node846
def node848 : BoxExpr 3 := .neg ⟨(-5406311319628819416769/2361183241434822606848:ℚ),(-10673169362468585847459/4722366482869645213696:ℚ)⟩ node847
def node849 : BoxExpr 3 := .add ⟨(-206786632103829131799/4722366482869645213696:ℚ),(210734757205088858701/4722366482869645213696:ℚ)⟩ node834 node848
def node850 : BoxExpr 3 := .var 2
def node851 : BoxExpr 3 := .mul ⟨(-481255489346742266103/4722366482869645213696:ℚ),(-481255489346742266101/4722366482869645213696:ℚ)⟩ node51 node850
def node852 : BoxExpr 3 := .add ⟨(1879927752088080340745/4722366482869645213696:ℚ),(1879927752088080340747/4722366482869645213696:ℚ)⟩ node851 node301
def node853 : BoxExpr 3 := .mul ⟨(3957505875161746453399/4722366482869645213696:ℚ),(3957505875161746453413/4722366482869645213696:ℚ)⟩ node68 node852
def node854 : BoxExpr 3 := .mul ⟨(4709182626345758834741/4722366482869645213696:ℚ),(4709182626345758834761/4722366482869645213696:ℚ)⟩ node853 node349
def node855 : BoxExpr 3 := .add ⟨(-65305797476574088397/1180591620717411303424:ℚ),(-130611594953148176793/2361183241434822606848:ℚ)⟩ node850 node351
def node856 : BoxExpr 3 := .mul ⟨(11293899721380116789/4722366482869645213696:ℚ),(11293899721380116791/4722366482869645213696:ℚ)⟩ node855 node308
def node857 : BoxExpr 3 := .mul ⟨(12319863888979969513/4722366482869645213696:ℚ),(3079965972244992379/1180591620717411303424:ℚ)⟩ node856 node69
def node858 : BoxExpr 3 := .add ⟨(2360751245117369402127/2361183241434822606848:ℚ),(4721502490234738804277/4722366482869645213696:ℚ)⟩ node854 node857
def node859 : BoxExpr 3 := .add ⟨(7750252501575500378075/2361183241434822606848:ℚ),(7750252501575500378113/2361183241434822606848:ℚ)⟩ node858 node358
def node860 : BoxExpr 3 := .add ⟨(10745620368370717665333/4722366482869645213696:ℚ),(5372810184185358832707/2361183241434822606848:ℚ)⟩ node859 node361
def node861 : BoxExpr 3 := .add ⟨(10745606201271269056397/4722366482869645213696:ℚ),(10745606201271269056479/4722366482869645213696:ℚ)⟩ node860 node325
def node862 : BoxExpr 3 := .mul ⟨(307260066161188132617/4722366482869645213696:ℚ),(307260066161188132619/4722366482869645213696:ℚ)⟩ node850 node850
def node863 : BoxExpr 3 := .neg ⟨(-307260066161188132619/4722366482869645213696:ℚ),(-307260066161188132617/4722366482869645213696:ℚ)⟩ node862
def node864 : BoxExpr 3 := .add ⟨(4415106416708457081077/4722366482869645213696:ℚ),(4415106416708457081079/4722366482869645213696:ℚ)⟩ node12 node863
def node865 : BoxExpr 3 := .sqrt ⟨(4566152708853123612191/4722366482869645213696:ℚ),(4566152708853123612193/4722366482869645213696:ℚ)⟩ node864
def node866 : BoxExpr 3 := .mul ⟨(11312203875262956849631/4722366482869645213696:ℚ),(2828050968815739212411/1180591620717411303424:ℚ)⟩ node50 node865
def node867 : BoxExpr 3 := .neg ⟨(301143097003308430131/1180591620717411303424:ℚ),(1204572388013233720525/4722366482869645213696:ℚ)⟩ node850
def node868 : BoxExpr 3 := .add ⟨(1086513225941492590181/4722366482869645213696:ℚ),(1086513225941492590183/4722366482869645213696:ℚ)⟩ node332 node867
def node869 : BoxExpr 3 := .mul ⟨(775770443322225709389/4722366482869645213696:ℚ),(775770443322225709391/4722366482869645213696:ℚ)⟩ node868 node335
def node870 : BoxExpr 3 := .neg ⟨(-775770443322225709391/4722366482869645213696:ℚ),(-775770443322225709389/4722366482869645213696:ℚ)⟩ node869
def node871 : BoxExpr 3 := .add ⟨(658527089496295696265/295147905179352825856:ℚ),(10536433431940731140255/4722366482869645213696:ℚ)⟩ node866 node870
def node872 : BoxExpr 3 := .mul ⟨(249982925812319974849/4722366482869645213696:ℚ),(249982925812319974851/4722366482869645213696:ℚ)⟩ node868 node868
def node873 : BoxExpr 3 := .mul ⟨(206485896720976299225/4722366482869645213696:ℚ),(206485896720976299227/4722366482869645213696:ℚ)⟩ node872 node340
def node874 : BoxExpr 3 := .add ⟨(10742919328661707439465/4722366482869645213696:ℚ),(5371459664330853719741/2361183241434822606848:ℚ)⟩ node871 node873
def node875 : BoxExpr 3 := .neg ⟨(-5371459664330853719741/2361183241434822606848:ℚ),(-10742919328661707439465/4722366482869645213696:ℚ)⟩ node874
def node876 : BoxExpr 3 := .add ⟨(2686872609561616915/4722366482869645213696:ℚ),(1343436304780808507/2361183241434822606848:ℚ)⟩ node861 node875
def node877 : BoxExpr 3 := .mul ⟨(533002226866776469631/2361183241434822606848:ℚ),(266501113433388234817/1180591620717411303424:ℚ)⟩ node78 node852
def node878 : BoxExpr 3 := .mul ⟨(1268478130288076187325/4722366482869645213696:ℚ),(634239065144038093667/2361183241434822606848:ℚ)⟩ node877 node349
def node879 : BoxExpr 3 := .add ⟨(2573854733784723587459/2361183241434822606848:ℚ),(5147709467569447175347/4722366482869645213696:ℚ)⟩ node878 node385
def node880 : BoxExpr 3 := .add ⟨(698460851764173331539/1180591620717411303424:ℚ),(2793843407056693326587/4722366482869645213696:ℚ)⟩ node879 node387
def node881 : BoxExpr 3 := .mul ⟨(2824426478346669855735/4722366482869645213696:ℚ),(2758228982760419781/4611686018427387904:ℚ)⟩ node77 node865
def node882 : BoxExpr 3 := .neg ⟨(-2758228982760419781/4611686018427387904:ℚ),(-2824426478346669855735/4722366482869645213696:ℚ)⟩ node881
def node883 : BoxExpr 3 := .add ⟨(-7645767822494132397/1180591620717411303424:ℚ),(-7645767822494132287/1180591620717411303424:ℚ)⟩ node880 node882
def node884 : BoxExpr 3 := .mul ⟨(-1792968964270585213555/4722366482869645213696:ℚ),(-224121120533823151693/590295810358705651712:ℚ)⟩ node98 node852
def node885 : BoxExpr 3 := .mul ⟨(-2535790163917232323865/4722366482869645213696:ℚ),(-158486885244827020241/295147905179352825856:ℚ)⟩ node68 node850
def node886 : BoxExpr 3 := .add ⟨(-1082189782046954384355/1180591620717411303424:ℚ),(-541094891023477192175/590295810358705651712:ℚ)⟩ node884 node885
def node887 : BoxExpr 3 := .mul ⟨(-5150950604530570894531/4722366482869645213696:ℚ),(-643868825566321361813/590295810358705651712:ℚ)⟩ node886 node349
def node888 : BoxExpr 3 := .mul ⟨(4477568989162336005711/4722366482869645213696:ℚ),(4477568989162336005735/4722366482869645213696:ℚ)⟩ node853 node399
def node889 : BoxExpr 3 := .add ⟨(-168345403842058722205/1180591620717411303424:ℚ),(-673381615368234888769/4722366482869645213696:ℚ)⟩ node887 node888
def node890 : BoxExpr 3 := .mul ⟨(5856965515776050589/4722366482869645213696:ℚ),(5856965515776050591/4722366482869645213696:ℚ)⟩ node856 node103
def node891 : BoxExpr 3 := .add ⟨(-6593853934374384559/295147905179352825856:ℚ),(-26375415737497538235/1180591620717411303424:ℚ)⟩ node403 node890
def node892 : BoxExpr 3 := .add ⟨(-194720819579556260441/1180591620717411303424:ℚ),(-778883278318225041709/4722366482869645213696:ℚ)⟩ node889 node891
def node893 : BoxExpr 3 := .add ⟨(-228483021846778105745/2361183241434822606848:ℚ),(-456966043693556211319/4722366482869645213696:ℚ)⟩ node892 node409
def node894 : BoxExpr 3 := .add ⟨(-1204572388013233720525/2361183241434822606848:ℚ),(-301143097003308430131/590295810358705651712:ℚ)⟩ node850 node850
def node895 : BoxExpr 3 := .neg ⟨(301143097003308430131/590295810358705651712:ℚ),(1204572388013233720525/2361183241434822606848:ℚ)⟩ node894
def node896 : BoxExpr 3 := .mul ⟨(4566152708853123612191/2361183241434822606848:ℚ),(4566152708853123612193/2361183241434822606848:ℚ)⟩ node86 node865
def node897 : BoxExpr 3 := .inv ⟨(152622641398500506313/295147905179352825856:ℚ),(1220981131188004050505/2361183241434822606848:ℚ)⟩ node896
def node898 : BoxExpr 3 := .mul ⟨(1245782310415260382779/4722366482869645213696:ℚ),(622891155207630191391/2361183241434822606848:ℚ)⟩ node895 node897
def node899 : BoxExpr 3 := .mul ⟨(3086305776039881849019/4722366482869645213696:ℚ),(3086305776039881849029/4722366482869645213696:ℚ)⟩ node50 node898
def node900 : BoxExpr 3 := .add ⟨(6458075444808808531597/4722366482869645213696:ℚ),(807259430601101066451/590295810358705651712:ℚ)⟩ node899 node335
def node901 : BoxExpr 3 := .mul ⟨(-1086513225941492590183/4722366482869645213696:ℚ),(-1086513225941492590181/4722366482869645213696:ℚ)⟩ node422 node868
def node902 : BoxExpr 3 := .mul ⟨(-1086513225941492590183/4722366482869645213696:ℚ),(-1086513225941492590181/4722366482869645213696:ℚ)⟩ node868 node422
def node903 : BoxExpr 3 := .add ⟨(-1086513225941492590183/2361183241434822606848:ℚ),(-1086513225941492590181/2361183241434822606848:ℚ)⟩ node901 node902
def node904 : BoxExpr 3 := .mul ⟨(-1794919849255345758983/4722366482869645213696:ℚ),(-897459924627672879489/2361183241434822606848:ℚ)⟩ node903 node340
def node905 : BoxExpr 3 := .add ⟨(2331577797776731386307/2361183241434822606848:ℚ),(2331577797776731386315/2361183241434822606848:ℚ)⟩ node900 node904
def node906 : BoxExpr 3 := .neg ⟨(-2331577797776731386315/2361183241434822606848:ℚ),(-2331577797776731386307/2361183241434822606848:ℚ)⟩ node905
def node907 : BoxExpr 3 := .add ⟨(-159729893673828359031/4722366482869645213696:ℚ),(-39932473418457089749/1180591620717411303424:ℚ)⟩ node414 node906
def node908 : BoxExpr 3 := .mul ⟨(1049579900696845002599/590295810358705651712:ℚ),(4280403662473047337205/2361183241434822606848:ℚ)⟩ node112 node825
def node909 : BoxExpr 3 := .mul ⟨(1246569362779016978385/590295810358705651712:ℚ),(2551569617919527580169/1180591620717411303424:ℚ)⟩ node908 node304
def node910 : BoxExpr 3 := .add ⟨(21298765821094919989803/4722366482869645213696:ℚ),(44532628084338928734957/4722366482869645213696:ℚ)⟩ node909 node448
def node911 : BoxExpr 3 := .mul ⟨(22419271496376546085021/4722366482869645213696:ℚ),(11255127701300384135409/2361183241434822606848:ℚ)⟩ node111 node838
def node912 : BoxExpr 3 := .neg ⟨(-11255127701300384135409/2361183241434822606848:ℚ),(-22419271496376546085021/4722366482869645213696:ℚ)⟩ node911
def node913 : BoxExpr 3 := .add ⟨(-1211489581505848281015/4722366482869645213696:ℚ),(1382084786747648915621/295147905179352825856:ℚ)⟩ node910 node912
def node914 : BoxExpr 3 := .mul ⟨(-526513032561442692223/4722366482869645213696:ℚ),(-121860107913991289151/1180591620717411303424:ℚ)⟩ node131 node825
def node915 : BoxExpr 3 := .mul ⟨(-720376908849858016805/4722366482869645213696:ℚ),(-646731039325631939791/4722366482869645213696:ℚ)⟩ node118 node823
def node916 : BoxExpr 3 := .add ⟨(-311722485352825177257/1180591620717411303424:ℚ),(-1134171470981597096395/4722366482869645213696:ℚ)⟩ node914 node915
def node917 : BoxExpr 3 := .mul ⟨(-371638604938999486263/1180591620717411303424:ℚ),(-1347037426045404966153/4722366482869645213696:ℚ)⟩ node916 node304
def node918 : BoxExpr 3 := .mul ⟨(1030460763179727323495/4722366482869645213696:ℚ),(550986405718814406333/2361183241434822606848:ℚ)⟩ node118 node825
def node919 : BoxExpr 3 := .mul ⟨(144456346963481884545/590295810358705651712:ℚ),(157227206739217199361/590295810358705651712:ℚ)⟩ node918 node461
def node920 : BoxExpr 3 := .add ⟨(-82725911012035717173/1180591620717411303424:ℚ),(-89219772131667371265/4722366482869645213696:ℚ)⟩ node917 node919
def node921 : BoxExpr 3 := .add ⟨(-3088204368942613710651/4722366482869645213696:ℚ),(1324354108439992401639/4722366482869645213696:ℚ)⟩ node920 node476
def node922 : BoxExpr 3 := .add ⟨(-309905300438320467149/590295810358705651712:ℚ),(-584761787136592786227/1180591620717411303424:ℚ)⟩ node823 node823
def node923 : BoxExpr 3 := .neg ⟨(584761787136592786227/1180591620717411303424:ℚ),(309905300438320467149/590295810358705651712:ℚ)⟩ node922
def node924 : BoxExpr 3 := .mul ⟨(4556762499263525627037/2361183241434822606848:ℚ),(2287627581565118726709/1180591620717411303424:ℚ)⟩ node86 node838
def node925 : BoxExpr 3 := .inv ⟨(2437103986925310061399/4722366482869645213696:ℚ),(2446994461762591375487/4722366482869645213696:ℚ)⟩ node924
def node926 : BoxExpr 3 := .mul ⟨(603564034261971319893/2361183241434822606848:ℚ),(321168023106340118033/1180591620717411303424:ℚ)⟩ node923 node925
def node927 : BoxExpr 3 := .mul ⟨(364430253285819997145/2361183241434822606848:ℚ),(25425152768717558641/147573952589676412928:ℚ)⟩ node117 node926
def node928 : BoxExpr 3 := .neg ⟨(-25425152768717558641/147573952589676412928:ℚ),(-364430253285819997145/2361183241434822606848:ℚ)⟩ node927
def node929 : BoxExpr 3 := .add ⟨(419325703507402099435/4722366482869645213696:ℚ),(146208660039405176859/1180591620717411303424:ℚ)⟩ node479 node928
def node930 : BoxExpr 3 := .add ⟨(-1544102184471306855325/2361183241434822606848:ℚ),(1324354108439992401639/4722366482869645213696:ℚ)⟩ node920 node492
def node931 : BoxExpr 3 := .mul ⟨(-974128464301116887013/2361183241434822606848:ℚ),(-467842266465611287351/1180591620717411303424:ℚ)⟩ node175 node825
def node932 : BoxExpr 3 := .mul ⟨(1101839563465990169379/4722366482869645213696:ℚ),(598369816763504747453/2361183241434822606848:ℚ)⟩ node148 node823
def node933 : BoxExpr 3 := .add ⟨(-846417365136243604647/4722366482869645213696:ℚ),(-337314716167717827249/2361183241434822606848:ℚ)⟩ node931 node932
def node934 : BoxExpr 3 := .add ⟨(63855549582436641183/1180591620717411303424:ℚ),(65263775148946730051/590295810358705651712:ℚ)⟩ node933 node932
def node935 : BoxExpr 3 := .mul ⟨(303360884483527508137/4722366482869645213696:ℚ),(311232451800253612367/2361183241434822606848:ℚ)⟩ node934 node304
def node936 : BoxExpr 3 := .mul ⟨(-1830672974543465153455/4722366482869645213696:ℚ),(-1755602203127135945681/4722366482869645213696:ℚ)⟩ node148 node825
def node937 : BoxExpr 3 := .mul ⟨(-2618662046128022308687/4722366482869645213696:ℚ),(-2453478766365681647257/4722366482869645213696:ℚ)⟩ node36 node823
def node938 : BoxExpr 3 := .add ⟨(-2224667510335743731071/2361183241434822606848:ℚ),(-2104540484746408796469/2361183241434822606848:ℚ)⟩ node936 node937
def node939 : BoxExpr 3 := .mul ⟨(-5078575513924100394249/4722366482869645213696:ℚ),(-4720439497765868240657/4722366482869645213696:ℚ)⟩ node938 node461
def node940 : BoxExpr 3 := .add ⟨(-149225457170017902691/147573952589676412928:ℚ),(-4097974594165361015923/4722366482869645213696:ℚ)⟩ node935 node939
def node941 : BoxExpr 3 := .mul ⟨(19276810843524580411005/4722366482869645213696:ℚ),(10087952111245522857253/2361183241434822606848:ℚ)⟩ node826 node514
def node942 : BoxExpr 3 := .add ⟨(3549558832400120004189/1180591620717411303424:ℚ),(15455464724725177473849/4722366482869645213696:ℚ)⟩ node939 node941
def node943 : BoxExpr 3 := .add ⟨(2355755175039976782661/1180591620717411303424:ℚ),(5678745065279908228963/2361183241434822606848:ℚ)⟩ node940 node942
def node944 : BoxExpr 3 := .mul ⟨(2420185051903975179/590295810358705651712:ℚ),(13360439761853163963/2361183241434822606848:ℚ)⟩ node829 node189
def node945 : BoxExpr 3 := .add ⟨(-1062402039495899971/147573952589676412928:ℚ),(-3225674068490557251/590295810358705651712:ℚ)⟩ node518 node944
def node946 : BoxExpr 3 := .add ⟨(-10919401367871174947/590295810358705651712:ℚ),(-39165832309777621971/2361183241434822606848:ℚ)⟩ node518 node945
def node947 : BoxExpr 3 := .add ⟨(2333916372304234432767/1180591620717411303424:ℚ),(352473702060633162937/147573952589676412928:ℚ)⟩ node943 node946
def node948 : BoxExpr 3 := .add ⟨(20439398767583509102591/4722366482869645213696:ℚ),(27872629505267707688527/4722366482869645213696:ℚ)⟩ node947 node527
def node949 : BoxExpr 3 := .mul ⟨(-2446994461762591375487/2361183241434822606848:ℚ),(-2437103986925310061399/2361183241434822606848:ℚ)⟩ node6 node925
def node950 : BoxExpr 3 := .mul ⟨(603564034261971319893/1180591620717411303424:ℚ),(321168023106340118033/590295810358705651712:ℚ)⟩ node86 node926
def node951 : BoxExpr 3 := .mul ⟨(17587863669637634892755/4722366482869645213696:ℚ),(17730906640714206397083/4722366482869645213696:ℚ)⟩ node924 node924
def node952 : BoxExpr 3 := .inv ⟨(314433233032244174001/1180591620717411303424:ℚ),(316990534174837738795/1180591620717411303424:ℚ)⟩ node951
def node953 : BoxExpr 3 := .mul ⟨(643001652068821804715/4722366482869645213696:ℚ),(689872578580492282401/4722366482869645213696:ℚ)⟩ node950 node952
def node954 : BoxExpr 3 := .neg ⟨(-689872578580492282401/4722366482869645213696:ℚ),(-643001652068821804715/4722366482869645213696:ℚ)⟩ node953
def node955 : BoxExpr 3 := .mul ⟨(-362183103754758448261/4722366482869645213696:ℚ),(-318486755790338300147/4722366482869645213696:ℚ)⟩ node923 node954
def node956 : BoxExpr 3 := .add ⟨(-5256172027279941199235/4722366482869645213696:ℚ),(-5192694729640958422945/4722366482869645213696:ℚ)⟩ node949 node955
def node957 : BoxExpr 3 := .mul ⟨(-1628941303412274434667/590295810358705651712:ℚ),(-3213720115510841081519/1180591620717411303424:ℚ)⟩ node11 node956
def node958 : BoxExpr 3 := .add ⟨(-5230180997597541584311/4722366482869645213696:ℚ),(-2526765516171355216525/2361183241434822606848:ℚ)⟩ node957 node546
def node959 : BoxExpr 3 := .neg ⟨(2526765516171355216525/2361183241434822606848:ℚ),(5230180997597541584311/4722366482869645213696:ℚ)⟩ node958
def cert_iv3 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-653/2560:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/2560:ℚ)],
    whole := node849, centerValue := node876, gradient := ![node883, node893, node907],
    hessian := ![![node913, node921, node929], ![node930, node948, node536], ![node929, node536, node959]] }

end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part1
end

section
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646CheckB4Part1
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part1

theorem cert_iv0_check : cert_iv0.check = true := by decide +kernel

theorem cert_iv0_lower_pos : 0 < cert_iv0.lower := by decide +kernel

theorem positive_iv0 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(1/2:ℝ)) ≤ r) (hrhi : r ≤ (-(61/160:ℝ))) :
    0 < node344.eval ![A,ρ,r] := by
  apply cert_iv0.positive_sound cert_iv0_check cert_iv0_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv0,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv0,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv0,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv1_check : cert_iv1.check = true := by decide +kernel

theorem cert_iv1_lower_pos : 0 < cert_iv1.lower := by decide +kernel

theorem positive_iv1 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(61/160:ℝ)) ≤ r) (hrhi : r ≤ (-(103/320:ℝ))) :
    0 < node575.eval ![A,ρ,r] := by
  apply cert_iv1.positive_sound cert_iv1_check cert_iv1_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv1,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv1,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv1,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv2_check : cert_iv2.check = true := by decide +kernel

theorem cert_iv2_lower_pos : 0 < cert_iv2.lower := by decide +kernel

theorem positive_iv2 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(103/320:ℝ)) ≤ r) (hrhi : r ≤ (-(21/80:ℝ))) :
    0 < node712.eval ![A,ρ,r] := by
  apply cert_iv2.positive_sound cert_iv2_check cert_iv2_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv2,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv2,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv2,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv3_check : cert_iv3.check = true := by decide +kernel

theorem cert_iv3_lower_pos : 0 < cert_iv3.lower := by decide +kernel

theorem positive_iv3 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(21/80:ℝ)) ≤ r) (hrhi : r ≤ (-(317/1280:ℝ))) :
    0 < node849.eval ![A,ρ,r] := by
  apply cert_iv3.positive_sound cert_iv3_check cert_iv3_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv3,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv3,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv3,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part1
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
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646BoundB4Part1
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part1
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate.CapacityCore
noncomputable section
namespace Parameters
def b : ℚ := (103531361122339324647880530522418473224550678173/6474633415922124204664207433178390079472570088576:ℚ)
def c : ℚ := (148022665013912365111/4722366482869645213696:ℚ)
def theta : ℚ := (105113898053531722649817636563532003778556764000751/182628568201966125342452015454275643968150995402752:ℚ)
end Parameters

theorem iv_shape0 : SplitDataB4Part1.node344.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound0 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(1/2:ℝ)) ≤ r) (hrhi : r ≤ (-(61/160:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part1.node344 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape0 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part1.positive_iv0 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part1.node344.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape1 : SplitDataB4Part1.node575.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound1 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(61/160:ℝ)) ≤ r) (hrhi : r ≤ (-(103/320:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part1.node575 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape1 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part1.positive_iv1 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part1.node575.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape2 : SplitDataB4Part1.node712.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound2 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(103/320:ℝ)) ≤ r) (hrhi : r ≤ (-(21/80:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part1.node712 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape2 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part1.positive_iv2 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part1.node712.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape3 : SplitDataB4Part1.node849.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound3 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(21/80:ℝ)) ≤ r) (hrhi : r ≤ (-(317/1280:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part1.node849 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape3 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part1.positive_iv3 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part1.node849.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem actual_bound (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (r : ℝ)
    (hrlo : (-(1/2:ℝ)) ≤ r) (hrhi : r ≤ (-(317/1280:ℝ))) : fA A r+3/10^6 ≤ l40Lhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) r := by
  have hc : 0 ≤ (Parameters.c:ℝ) := by norm_num [Parameters.c]
  have hθ : 0 ≤ (Parameters.theta:ℝ) := by norm_num [Parameters.theta]
  by_cases h0 : r ≤ (-(61/160:ℝ))
  · have h := iv_bound0 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  by_cases h1 : r ≤ (-(103/320:ℝ))
  · have h := iv_bound1 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  by_cases h2 : r ≤ (-(21/80:ℝ))
  · have h := iv_bound2 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  have h := iv_bound3 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
  exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
    (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
end
end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part1
end

section
-- Source module: Solutions.Sol_GaussLocalMaxCase1FamilyAdaptive0Seed25646B4Part1
set_option autoImplicit false
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate
open GaussLocalMaxColoring.Certificate.CapacityCore
theorem solution (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (r : ℝ)
    (hrlo : (-(1/2:ℝ)) ≤ r) (hrhi : r ≤ (-(317/1280:ℝ))) :
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
  have h := GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part1.actual_bound A ρ hAlo hAhi hρlo hρhi r hrlo hrhi
  simpa only [Case2Static,constructedA,constructedMu,constructedMass,constructedKappa,thresholdCapacity,
    GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part1.Parameters.b,GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part1.Parameters.c,GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part1.Parameters.theta,
    show ¬ (4:ℕ)=1 by decide,show ¬ (4:ℕ)=2 by decide,show ¬ (4:ℕ)=3 by decide,ite_false,and_assoc] using h
end

#print axioms solution
