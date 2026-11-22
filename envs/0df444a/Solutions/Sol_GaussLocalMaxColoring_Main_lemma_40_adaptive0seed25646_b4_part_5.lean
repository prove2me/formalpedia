-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_40_adaptive0seed25646_b4_part_5
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T14:29:10.600102+00:00
-- url     : https://prove2.me/submissions/2a99f066-8ab0-467b-8f7d-6a8b4a534d8b

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
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646DefsB4Part5
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part5

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
def node2604 : BoxExpr 3 := .var 2
def node2605 : BoxExpr 3 := .mul ⟨(-420336416331808968279/4722366482869645213696:ℚ),(-414407412673086930655/4722366482869645213696:ℚ)⟩ node13 node2604
def node2606 : BoxExpr 3 := .add ⟨(1940846825103013638569/4722366482869645213696:ℚ),(1946775828761735676193/4722366482869645213696:ℚ)⟩ node2605 node301
def node2607 : BoxExpr 3 := .mul ⟨(2035797558470672924671/2361183241434822606848:ℚ),(4112504665043969290527/4722366482869645213696:ℚ)⟩ node36 node2606
def node2608 : BoxExpr 3 := .mul ⟨(4835768793828796925645/4722366482869645213696:ℚ),(4902968404066769252241/4722366482869645213696:ℚ)⟩ node2607 node304
def node2609 : BoxExpr 3 := .add ⟨(-108225894558949332485/4722366482869645213696:ℚ),(-94400059875704023547/4722366482869645213696:ℚ)⟩ node2604 node306
def node2610 : BoxExpr 3 := .mul ⟨(4081355909905693843/4722366482869645213696:ℚ),(2339555689607575733/2361183241434822606848:ℚ)⟩ node2609 node308
def node2611 : BoxExpr 3 := .mul ⟨(555987404842339047/590295810358705651712:ℚ),(5109045006983883345/4722366482869645213696:ℚ)⟩ node2610 node37
def node2612 : BoxExpr 3 := .add ⟨(4840216693067535638021/4722366482869645213696:ℚ),(2454038724536876567793/2361183241434822606848:ℚ)⟩ node2608 node2611
def node2613 : BoxExpr 3 := .add ⟨(3888665237051730499457/1180591620717411303424:ℚ),(3937460361483385908207/1180591620717411303424:ℚ)⟩ node2612 node316
def node2614 : BoxExpr 3 := .add ⟨(1349089339405637580683/590295810358705651712:ℚ),(11002018409334798803563/4722366482869645213696:ℚ)⟩ node2613 node323
def node2615 : BoxExpr 3 := .add ⟨(674543784259103252283/295147905179352825856:ℚ),(2750501060558837548657/1180591620717411303424:ℚ)⟩ node2614 node325
def node2616 : BoxExpr 3 := .mul ⟨(230127647178153095331/4722366482869645213696:ℚ),(51529/1048576:ℚ)⟩ node2604 node2604
def node2617 : BoxExpr 3 := .neg ⟨(-51529/1048576:ℚ),(-230127647178153095331/4722366482869645213696:ℚ)⟩ node2616
def node2618 : BoxExpr 3 := .add ⟨(997047/1048576:ℚ),(4492238835691492118365/4722366482869645213696:ℚ)⟩ node12 node2617
def node2619 : BoxExpr 3 := .sqrt ⟨(575608978715882049333/590295810358705651712:ℚ),(1151466405033025205655/1180591620717411303424:ℚ)⟩ node2618
def node2620 : BoxExpr 3 := .mul ⟨(5699841796618109262447/2361183241434822606848:ℚ),(5709618869139176751277/2361183241434822606848:ℚ)⟩ node11 node2619
def node2621 : BoxExpr 3 := .neg ⟨(1042471624465511035699/4722366482869645213696:ℚ),(227/1024:ℚ)⟩ node2604
def node2622 : BoxExpr 3 := .add ⟨(231103115598442476339/1180591620717411303424:ℚ),(464396782055637961933/2361183241434822606848:ℚ)⟩ node332 node2621
def node2623 : BoxExpr 3 := .mul ⟨(660030498149151712423/4722366482869645213696:ℚ),(663158604775451009641/4722366482869645213696:ℚ)⟩ node2622 node335
def node2624 : BoxExpr 3 := .neg ⟨(-663158604775451009641/4722366482869645213696:ℚ),(-660030498149151712423/4722366482869645213696:ℚ)⟩ node2623
def node2625 : BoxExpr 3 := .add ⟨(10736524988460767515253/4722366482869645213696:ℚ),(10759207240129201790131/4722366482869645213696:ℚ)⟩ node2620 node2624
def node2626 : BoxExpr 3 := .mul ⟨(180955545006671071805/4722366482869645213696:ℚ),(182674827941416963933/4722366482869645213696:ℚ)⟩ node2622 node2622
def node2627 : BoxExpr 3 := .mul ⟨(74734640087755152655/2361183241434822606848:ℚ),(150889407879610412209/4722366482869645213696:ℚ)⟩ node2626 node340
def node2628 : BoxExpr 3 := .add ⟨(10885994268636277820563/4722366482869645213696:ℚ),(2727524162002203050585/1180591620717411303424:ℚ)⟩ node2625 node2627
def node2629 : BoxExpr 3 := .neg ⟨(-2727524162002203050585/1180591620717411303424:ℚ),(-10885994268636277820563/4722366482869645213696:ℚ)⟩ node2628
def node2630 : BoxExpr 3 := .add ⟨(-29349024965790041453/1180591620717411303424:ℚ),(116009973599072374065/4722366482869645213696:ℚ)⟩ node2615 node2629
def node2631 : BoxExpr 3 := .var 2
def node2632 : BoxExpr 3 := .mul ⟨(-417367533400730443449/4722366482869645213696:ℚ),(-52170941675091305431/590295810358705651712:ℚ)⟩ node51 node2631
def node2633 : BoxExpr 3 := .add ⟨(1943815708034092163399/4722366482869645213696:ℚ),(242976963504261520425/590295810358705651712:ℚ)⟩ node2632 node301
def node2634 : BoxExpr 3 := .mul ⟨(1022999697226686970857/1180591620717411303424:ℚ),(255749924306671742715/295147905179352825856:ℚ)⟩ node68 node2633
def node2635 : BoxExpr 3 := .mul ⟨(4869220719213705328401/4722366482869645213696:ℚ),(2434610359606852664209/2361183241434822606848:ℚ)⟩ node2634 node349
def node2636 : BoxExpr 3 := .add ⟨(-101312977217326678017/4722366482869645213696:ℚ),(-101312977217326678015/4722366482869645213696:ℚ)⟩ node2631 node351
def node2637 : BoxExpr 3 := .mul ⟨(2190116822280211327/2361183241434822606848:ℚ),(4380233644560422655/4722366482869645213696:ℚ)⟩ node2636 node308
def node2638 : BoxExpr 3 := .mul ⟨(4778144275600197819/4722366482869645213696:ℚ),(4778144275600197821/4722366482869645213696:ℚ)⟩ node2637 node69
def node2639 : BoxExpr 3 := .add ⟨(1218499715872326381555/1180591620717411303424:ℚ),(4873998863489305526239/4722366482869645213696:ℚ)⟩ node2635 node2638
def node2640 : BoxExpr 3 := .add ⟨(3913250344101391869529/1180591620717411303424:ℚ),(3913250344101391869547/1180591620717411303424:ℚ)⟩ node2639 node358
def node2641 : BoxExpr 3 := .add ⟨(10898116741625284387299/4722366482869645213696:ℚ),(681132296351580274211/295147905179352825856:ℚ)⟩ node2640 node361
def node2642 : BoxExpr 3 := .add ⟨(10898102574525835778363/4722366482869645213696:ℚ),(10898102574525835778441/4722366482869645213696:ℚ)⟩ node2641 node325
def node2643 : BoxExpr 3 := .mul ⟨(231095800063797766389/4722366482869645213696:ℚ),(115547900031898883195/2361183241434822606848:ℚ)⟩ node2631 node2631
def node2644 : BoxExpr 3 := .neg ⟨(-115547900031898883195/2361183241434822606848:ℚ),(-231095800063797766389/4722366482869645213696:ℚ)⟩ node2643
def node2645 : BoxExpr 3 := .add ⟨(2245635341402923723653/2361183241434822606848:ℚ),(4491270682805847447307/4722366482869645213696:ℚ)⟩ node12 node2644
def node2646 : BoxExpr 3 := .sqrt ⟨(2302684636352609605405/2361183241434822606848:ℚ),(4605369272705219210811/4722366482869645213696:ℚ)⟩ node2645
def node2647 : BoxExpr 3 := .mul ⟨(11409359137880881447755/4722366482869645213696:ℚ),(5704679568940440723883/2361183241434822606848:ℚ)⟩ node50 node2646
def node2648 : BoxExpr 3 := .neg ⟨(1044662175324264044953/4722366482869645213696:ℚ),(522331087662132022477/2361183241434822606848:ℚ)⟩ node2631
def node2649 : BoxExpr 3 := .add ⟨(463301506626261457305/2361183241434822606848:ℚ),(231650753313130728653/1180591620717411303424:ℚ)⟩ node332 node2648
def node2650 : BoxExpr 3 := .mul ⟨(661594551462301361031/4722366482869645213696:ℚ),(661594551462301361033/4722366482869645213696:ℚ)⟩ node2649 node335
def node2651 : BoxExpr 3 := .neg ⟨(-661594551462301361033/4722366482869645213696:ℚ),(-661594551462301361031/4722366482869645213696:ℚ)⟩ node2650
def node2652 : BoxExpr 3 := .add ⟨(5373882293209290043361/2361183241434822606848:ℚ),(10747764586418580086735/4722366482869645213696:ℚ)⟩ node2647 node2651
def node2653 : BoxExpr 3 := .mul ⟨(11363385646836130775/295147905179352825856:ℚ),(181814170349378092401/4722366482869645213696:ℚ)⟩ node2649 node2649
def node2654 : BoxExpr 3 := .mul ⟨(75089252354293152161/2361183241434822606848:ℚ),(37544626177146576081/1180591620717411303424:ℚ)⟩ node2653 node340
def node2655 : BoxExpr 3 := .add ⟨(2724485772781791597761/1180591620717411303424:ℚ),(10897943091127166391059/4722366482869645213696:ℚ)⟩ node2652 node2654
def node2656 : BoxExpr 3 := .neg ⟨(-10897943091127166391059/4722366482869645213696:ℚ),(-2724485772781791597761/1180591620717411303424:ℚ)⟩ node2655
def node2657 : BoxExpr 3 := .add ⟨(19935424833673413/590295810358705651712:ℚ),(159483398669387397/4722366482869645213696:ℚ)⟩ node2642 node2656
def node2658 : BoxExpr 3 := .mul ⟨(551115913816377580943/2361183241434822606848:ℚ),(1102231827632755161891/4722366482869645213696:ℚ)⟩ node78 node2633
def node2659 : BoxExpr 3 := .mul ⟨(1311586422517025134431/4722366482869645213696:ℚ),(655793211258512567219/2361183241434822606848:ℚ)⟩ node2658 node349
def node2660 : BoxExpr 3 := .add ⟨(648852219974799515253/590295810358705651712:ℚ),(5190817759798396122451/4722366482869645213696:ℚ)⟩ node2659 node385
def node2661 : BoxExpr 3 := .add ⟨(1418475849642821136631/2361183241434822606848:ℚ),(2836951699285642273691/4722366482869645213696:ℚ)⟩ node2660 node387
def node2662 : BoxExpr 3 := .mul ⟨(1424342082468356071941/2361183241434822606848:ℚ),(1424342082468356071945/2361183241434822606848:ℚ)⟩ node77 node2646
def node2663 : BoxExpr 3 := .neg ⟨(-1424342082468356071945/2361183241434822606848:ℚ),(-1424342082468356071941/2361183241434822606848:ℚ)⟩ node2662
def node2664 : BoxExpr 3 := .add ⟨(-2933116412767467657/1180591620717411303424:ℚ),(-11732465651069870191/4722366482869645213696:ℚ)⟩ node2661 node2663
def node2665 : BoxExpr 3 := .mul ⟨(-1853901690049356853577/4722366482869645213696:ℚ),(-1853901690049356853567/4722366482869645213696:ℚ)⟩ node98 node2633
def node2666 : BoxExpr 3 := .mul ⟨(-1099578611947456072289/2361183241434822606848:ℚ),(-1099578611947456072285/2361183241434822606848:ℚ)⟩ node68 node2631
def node2667 : BoxExpr 3 := .add ⟨(-4053058913944268998155/4722366482869645213696:ℚ),(-4053058913944268998137/4722366482869645213696:ℚ)⟩ node2665 node2666
def node2668 : BoxExpr 3 := .mul ⟨(-150715147551123953849/147573952589676412928:ℚ),(-602860590204495815393/590295810358705651712:ℚ)⟩ node2667 node349
def node2669 : BoxExpr 3 := .mul ⟨(4629735863664345645051/4722366482869645213696:ℚ),(4629735863664345645073/4722366482869645213696:ℚ)⟩ node2634 node399
def node2670 : BoxExpr 3 := .add ⟨(-193148857971620878117/4722366482869645213696:ℚ),(-193148857971620878071/4722366482869645213696:ℚ)⟩ node2668 node2669
def node2671 : BoxExpr 3 := .mul ⟨(141973089677485503/295147905179352825856:ℚ),(2271569434839768049/4722366482869645213696:ℚ)⟩ node2637 node103
def node2672 : BoxExpr 3 := .add ⟨(-109087059030926435485/4722366482869645213696:ℚ),(-54543529515463217741/2361183241434822606848:ℚ)⟩ node403 node2671
def node2673 : BoxExpr 3 := .add ⟨(-151117958501273656801/2361183241434822606848:ℚ),(-302235917002547313553/4722366482869645213696:ℚ)⟩ node2670 node2672
def node2674 : BoxExpr 3 := .add ⟨(153760293922824349/36893488147419103232:ℚ),(19681317622121516837/4722366482869645213696:ℚ)⟩ node2673 node409
def node2675 : BoxExpr 3 := .add ⟨(-522331087662132022477/1180591620717411303424:ℚ),(-1044662175324264044953/2361183241434822606848:ℚ)⟩ node2631 node2631
def node2676 : BoxExpr 3 := .neg ⟨(1044662175324264044953/2361183241434822606848:ℚ),(522331087662132022477/1180591620717411303424:ℚ)⟩ node2675
def node2677 : BoxExpr 3 := .mul ⟨(2302684636352609605405/1180591620717411303424:ℚ),(4605369272705219210811/2361183241434822606848:ℚ)⟩ node86 node2646
def node2678 : BoxExpr 3 := .inv ⟨(2421167975682332515835/4722366482869645213696:ℚ),(2421167975682332515837/4722366482869645213696:ℚ)⟩ node2677
def node2679 : BoxExpr 3 := .mul ⟨(1071201319709844478807/4722366482869645213696:ℚ),(1071201319709844478809/4722366482869645213696:ℚ)⟩ node2676 node2678
def node2680 : BoxExpr 3 := .mul ⟨(2653798173791711573459/4722366482869645213696:ℚ),(2653798173791711573467/4722366482869645213696:ℚ)⟩ node50 node2679
def node2681 : BoxExpr 3 := .add ⟨(6025567842560638256037/4722366482869645213696:ℚ),(3012783921280319128023/2361183241434822606848:ℚ)⟩ node2680 node335
def node2682 : BoxExpr 3 := .mul ⟨(-231650753313130728653/1180591620717411303424:ℚ),(-463301506626261457305/2361183241434822606848:ℚ)⟩ node422 node2649
def node2683 : BoxExpr 3 := .mul ⟨(-231650753313130728653/1180591620717411303424:ℚ),(-463301506626261457305/2361183241434822606848:ℚ)⟩ node2649 node422
def node2684 : BoxExpr 3 := .add ⟨(-231650753313130728653/590295810358705651712:ℚ),(-463301506626261457305/1180591620717411303424:ℚ)⟩ node2682 node2683
def node2685 : BoxExpr 3 := .mul ⟨(-382687044473291963735/1180591620717411303424:ℚ),(-1530748177893167854935/4722366482869645213696:ℚ)⟩ node2684 node340
def node2686 : BoxExpr 3 := .add ⟨(4494819664667470401097/4722366482869645213696:ℚ),(4494819664667470401111/4722366482869645213696:ℚ)⟩ node2681 node2685
def node2687 : BoxExpr 3 := .neg ⟨(-4494819664667470401111/4722366482869645213696:ℚ),(-4494819664667470401097/4722366482869645213696:ℚ)⟩ node2686
def node2688 : BoxExpr 3 := .add ⟨(1075754651520501561/590295810358705651712:ℚ),(8606037212164012521/4722366482869645213696:ℚ)⟩ node414 node2687
def node2689 : BoxExpr 3 := .mul ⟨(8745406858819290085531/4722366482869645213696:ℚ),(8788820130345015086695/4722366482869645213696:ℚ)⟩ node112 node2606
def node2690 : BoxExpr 3 := .mul ⟨(1298347587449467963029/590295810358705651712:ℚ),(5239058787504971516101/2361183241434822606848:ℚ)⟩ node2689 node304
def node2691 : BoxExpr 3 := .add ⟨(21712991618458527866955/4722366482869645213696:ℚ),(44804467187670761446483/4722366482869645213696:ℚ)⟩ node2690 node448
def node2692 : BoxExpr 3 := .mul ⟨(11327984701128558730873/2361183241434822606848:ℚ),(5665214712762484011823/1180591620717411303424:ℚ)⟩ node111 node2619
def node2693 : BoxExpr 3 := .neg ⟨(-5665214712762484011823/1180591620717411303424:ℚ),(-11327984701128558730873/2361183241434822606848:ℚ)⟩ node2692
def node2694 : BoxExpr 3 := .add ⟨(-947867232591408180337/4722366482869645213696:ℚ),(22148497785413643984737/4722366482869645213696:ℚ)⟩ node2691 node2693
def node2695 : BoxExpr 3 := .mul ⟨(-540536442863365778153/4722366482869645213696:ℚ),(-63460879851781646207/590295810358705651712:ℚ)⟩ node131 node2606
def node2696 : BoxExpr 3 := .mul ⟨(-608354011565914322227/4722366482869645213696:ℚ),(-576472994635485410055/4722366482869645213696:ℚ)⟩ node118 node2604
def node2697 : BoxExpr 3 := .add ⟨(-287222613607320025095/1180591620717411303424:ℚ),(-1084160033449738579711/4722366482869645213696:ℚ)⟩ node2695 node2696
def node2698 : BoxExpr 3 := .mul ⟨(-171214808753914422363/590295810358705651712:ℚ),(-1287639636725734846599/4722366482869645213696:ℚ)⟩ node2697 node304
def node2699 : BoxExpr 3 := .mul ⟨(134157822037788735255/590295810358705651712:ℚ),(282830826014324178951/1180591620717411303424:ℚ)⟩ node118 node2606
def node2700 : BoxExpr 3 := .mul ⟨(1203652553460345739065/4722366482869645213696:ℚ),(1291318995675446450409/4722366482869645213696:ℚ)⟩ node2699 node461
def node2701 : BoxExpr 3 := .add ⟨(-166065916570969639839/4722366482869645213696:ℚ),(1839679474855801905/2361183241434822606848:ℚ)⟩ node2698 node2700
def node2702 : BoxExpr 3 := .add ⟨(-1461683320732720240899/2361183241434822606848:ℚ),(708626619760685688357/2361183241434822606848:ℚ)⟩ node2701 node476
def node2703 : BoxExpr 3 := .add ⟨(-227/512:ℚ),(-1042471624465511035699/2361183241434822606848:ℚ)⟩ node2604 node2604
def node2704 : BoxExpr 3 := .neg ⟨(1042471624465511035699/2361183241434822606848:ℚ),(227/512:ℚ)⟩ node2703
def node2705 : BoxExpr 3 := .mul ⟨(575608978715882049333/295147905179352825856:ℚ),(1151466405033025205655/590295810358705651712:ℚ)⟩ node86 node2619
def node2706 : BoxExpr 3 := .inv ⟨(605226765112694915999/1180591620717411303424:ℚ),(1210714761623042315481/2361183241434822606848:ℚ)⟩ node2705
def node2707 : BoxExpr 3 := .mul ⟨(133604990482153013439/590295810358705651712:ℚ),(1073563480032932053181/4722366482869645213696:ℚ)⟩ node2704 node2706
def node2708 : BoxExpr 3 := .mul ⟨(322681258376818946637/2361183241434822606848:ℚ),(169976545128938299931/1180591620717411303424:ℚ)⟩ node117 node2707
def node2709 : BoxExpr 3 := .neg ⟨(-169976545128938299931/1180591620717411303424:ℚ),(-322681258376818946637/2361183241434822606848:ℚ)⟩ node2708
def node2710 : BoxExpr 3 := .add ⟨(553024411590610776223/4722366482869645213696:ℚ),(167083157493905702113/1180591620717411303424:ℚ)⟩ node479 node2709
def node2711 : BoxExpr 3 := .add ⟨(-2923366641465440481797/4722366482869645213696:ℚ),(708626619760685688357/2361183241434822606848:ℚ)⟩ node2701 node492
def node2712 : BoxExpr 3 := .mul ⟨(-2000147773830581055185/4722366482869645213696:ℚ),(-487274832920947543675/1180591620717411303424:ℚ)⟩ node175 node2606
def node2713 : BoxExpr 3 := .mul ⟨(491070254971386194377/2361183241434822606848:ℚ),(1010639497063359952915/4722366482869645213696:ℚ)⟩ node148 node2604
def node2714 : BoxExpr 3 := .add ⟨(-1018007263887808666431/4722366482869645213696:ℚ),(-938459834620430221785/4722366482869645213696:ℚ)⟩ node2712 node2713
def node2715 : BoxExpr 3 := .add ⟨(-35866753945036277677/4722366482869645213696:ℚ),(36089831221464865565/2361183241434822606848:ℚ)⟩ node2714 node2713
def node2716 : BoxExpr 3 := .mul ⟨(-42760695895057388577/4722366482869645213696:ℚ),(86053301624669550227/4722366482869645213696:ℚ)⟩ node2715 node304
def node2717 : BoxExpr 3 := .mul ⟨(-1879432030185015908085/4722366482869645213696:ℚ),(-1828523909708151951499/4722366482869645213696:ℚ)⟩ node148 node2606
def node2718 : BoxExpr 3 := .mul ⟨(-1105722255340515372157/2361183241434822606848:ℚ),(-2135687025338879265/4611686018427387904:ℚ)⟩ node36 node2604
def node2719 : BoxExpr 3 := .add ⟨(-4090876540866046652399/4722366482869645213696:ℚ),(-4015467423655164318859/4722366482869645213696:ℚ)⟩ node2717 node2718
def node2720 : BoxExpr 3 := .mul ⟨(-4669422584364836218915/4722366482869645213696:ℚ),(-2251651983651194203067/2361183241434822606848:ℚ)⟩ node2719 node461
def node2721 : BoxExpr 3 := .add ⟨(-1178045820064973401873/1180591620717411303424:ℚ),(-4417250665677718855907/4722366482869645213696:ℚ)⟩ node2716 node2720
def node2722 : BoxExpr 3 := .mul ⟨(627421987087980785923/147573952589676412928:ℚ),(5178319825684747808809/1180591620717411303424:ℚ)⟩ node2607 node514
def node2723 : BoxExpr 3 := .add ⟨(15408081002450548930621/4722366482869645213696:ℚ),(8104987667718301414551/2361183241434822606848:ℚ)⟩ node2720 node2722
def node2724 : BoxExpr 3 := .add ⟨(10695897722190655323129/4722366482869645213696:ℚ),(11792724669758883973195/4722366482869645213696:ℚ)⟩ node2721 node2723
def node2725 : BoxExpr 3 := .mul ⟨(8253367910696977125/4722366482869645213696:ℚ),(9607791297270997963/4722366482869645213696:ℚ)⟩ node2610 node189
def node2726 : BoxExpr 3 := .add ⟨(-45104977768403623379/4722366482869645213696:ℚ),(-42918480774359787971/4722366482869645213696:ℚ)⟩ node518 node2725
def node2727 : BoxExpr 3 := .add ⟨(-98463323447504223883/4722366482869645213696:ℚ),(-95444752845990573905/4722366482869645213696:ℚ)⟩ node518 node2726
def node2728 : BoxExpr 3 := .add ⟨(5298717199371575549623/2361183241434822606848:ℚ),(5848639958456446699645/2361183241434822606848:ℚ)⟩ node2724 node2727
def node2729 : BoxExpr 3 := .add ⟨(21701167677109722470769/4722366482869645213696:ℚ),(28290750956240339873833/4722366482869645213696:ℚ)⟩ node2728 node527
def node2730 : BoxExpr 3 := .mul ⟨(-1210714761623042315481/1180591620717411303424:ℚ),(-605226765112694915999/590295810358705651712:ℚ)⟩ node6 node2706
def node2731 : BoxExpr 3 := .mul ⟨(133604990482153013439/295147905179352825856:ℚ),(1073563480032932053181/2361183241434822606848:ℚ)⟩ node86 node2707
def node2732 : BoxExpr 3 := .mul ⟨(4490300497670870925311/1180591620717411303424:ℚ),(17968955342765968473463/4722366482869645213696:ℚ)⟩ node2705 node2705
def node2733 : BoxExpr 3 := .inv ⟨(310267691876542063425/1180591620717411303424:ℚ),(1241606503289594447303/4722366482869645213696:ℚ)⟩ node2732
def node2734 : BoxExpr 3 := .mul ⟨(280898568430597603029/2361183241434822606848:ℚ),(282261743839310423831/2361183241434822606848:ℚ)⟩ node2731 node2733
def node2735 : BoxExpr 3 := .neg ⟨(-282261743839310423831/2361183241434822606848:ℚ),(-280898568430597603029/2361183241434822606848:ℚ)⟩ node2734
def node2736 : BoxExpr 3 := .mul ⟨(-125143390335006769941/2361183241434822606848:ℚ),(-124017815222141773759/2361183241434822606848:ℚ)⟩ node2704 node2735
def node2737 : BoxExpr 3 := .add ⟨(-2546572913581091400903/2361183241434822606848:ℚ),(-2544924875672921437755/2361183241434822606848:ℚ)⟩ node2730 node2736
def node2738 : BoxExpr 3 := .mul ⟨(-6313671287094263502991/2361183241434822606848:ℚ),(-12600280495948964877859/4722366482869645213696:ℚ)⟩ node11 node2737
def node2739 : BoxExpr 3 := .add ⟨(-4825993144487873112957/4722366482869645213696:ℚ),(-4798931066248310984833/4722366482869645213696:ℚ)⟩ node2738 node546
def node2740 : BoxExpr 3 := .neg ⟨(4798931066248310984833/4722366482869645213696:ℚ),(4825993144487873112957/4722366482869645213696:ℚ)⟩ node2739
def cert_iv16 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-9061/40960:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/40960:ℚ)],
    whole := node2630, centerValue := node2657, gradient := ![node2664, node2674, node2688],
    hessian := ![![node2694, node2702, node2710], ![node2711, node2729, node536], ![node2710, node536, node2740]] }
def node2741 : BoxExpr 3 := .var 2
def node2742 : BoxExpr 3 := .mul ⟨(-418577299170948974799/4722366482869645213696:ℚ),(-412665819919096961249/4722366482869645213696:ℚ)⟩ node13 node2741
def node2743 : BoxExpr 3 := .add ⟨(1942605942263873632049/4722366482869645213696:ℚ),(1948517421515725645599/4722366482869645213696:ℚ)⟩ node2742 node301
def node2744 : BoxExpr 3 := .mul ⟨(1018821367863873018357/1180591620717411303424:ℚ),(4116183726710738686339/4722366482869645213696:ℚ)⟩ node36 node2743
def node2745 : BoxExpr 3 := .mul ⟨(4840151769219306664693/4722366482869645213696:ℚ),(4907354617476351053633/4722366482869645213696:ℚ)⟩ node2744 node304
def node2746 : BoxExpr 3 := .add ⟨(-103844792841443313977/4722366482869645213696:ℚ),(-45009479079099002519/2361183241434822606848:ℚ)⟩ node2741 node306
def node2747 : BoxExpr 3 := .mul ⟨(972985100237932405/1180591620717411303424:ℚ),(4489695870261187243/4722366482869645213696:ℚ)⟩ node2746 node308
def node2748 : BoxExpr 3 := .mul ⟨(4241472473546085365/4722366482869645213696:ℚ),(4902225317979411711/4722366482869645213696:ℚ)⟩ node2747 node37
def node2749 : BoxExpr 3 := .add ⟨(2422196620846426375029/2361183241434822606848:ℚ),(76754013168661413521/73786976294838206464:ℚ)⟩ node2745 node2748
def node2750 : BoxExpr 3 := .add ⟨(15558837496832239109865/4722366482869645213696:ℚ),(7877010419827060481293/2361183241434822606848:ℚ)⟩ node2749 node316
def node2751 : BoxExpr 3 := .add ⟨(10796891263870417757501/4722366482869645213696:ℚ),(11006197803055376133321/4722366482869645213696:ℚ)⟩ node2750 node323
def node2752 : BoxExpr 3 := .add ⟨(10796877096770969148565/4722366482869645213696:ℚ),(5503091817977963762193/2361183241434822606848:ℚ)⟩ node2751 node325
def node2753 : BoxExpr 3 := .mul ⟨(28524679769357413253/590295810358705651712:ℚ),(230127647178153095333/4722366482869645213696:ℚ)⟩ node2741 node2741
def node2754 : BoxExpr 3 := .neg ⟨(-230127647178153095333/4722366482869645213696:ℚ),(-28524679769357413253/590295810358705651712:ℚ)⟩ node2753
def node2755 : BoxExpr 3 := .add ⟨(4492238835691492118363/4722366482869645213696:ℚ),(561771130589348238459/590295810358705651712:ℚ)⟩ node12 node2754
def node2756 : BoxExpr 3 := .sqrt ⟨(2302932810066050411309/2361183241434822606848:ℚ),(4606855029747669064313/4722366482869645213696:ℚ)⟩ node2755
def node2757 : BoxExpr 3 := .mul ⟨(11402143791173187388755/4722366482869645213696:ℚ),(1427711345412722187835/590295810358705651712:ℚ)⟩ node11 node2756
def node2758 : BoxExpr 3 := .neg ⟨(519045261374002508595/2361183241434822606848:ℚ),(260617906116377758925/1180591620717411303424:ℚ)⟩ node2741
def node2759 : BoxExpr 3 := .add ⟨(920031360676263886847/4722366482869645213696:ℚ),(462206231196884952679/2361183241434822606848:ℚ)⟩ node332 node2758
def node2760 : BoxExpr 3 := .mul ⟨(82112798940356551901/590295810358705651712:ℚ),(330015249074575856213/2361183241434822606848:ℚ)⟩ node2759 node335
def node2761 : BoxExpr 3 := .neg ⟨(-330015249074575856213/2361183241434822606848:ℚ),(-82112798940356551901/590295810358705651712:ℚ)⟩ node2760
def node2762 : BoxExpr 3 := .add ⟨(10742113293024035676329/4722366482869645213696:ℚ),(672799273236182817967/295147905179352825856:ℚ)⟩ node2757 node2761
def node2763 : BoxExpr 3 := .mul ⟨(179244391069252583423/4722366482869645213696:ℚ),(90477772503335535903/2361183241434822606848:ℚ)⟩ node2759 node2759
def node2764 : BoxExpr 3 := .mul ⟨(148055867023202633907/4722366482869645213696:ℚ),(4670915005484697041/147573952589676412928:ℚ)⟩ node2763 node340
def node2765 : BoxExpr 3 := .add ⟨(2722542290011809577559/1180591620717411303424:ℚ),(682141103247152212049/295147905179352825856:ℚ)⟩ node2762 node2764
def node2766 : BoxExpr 3 := .neg ⟨(-682141103247152212049/295147905179352825856:ℚ),(-2722542290011809577559/1180591620717411303424:ℚ)⟩ node2765
def node2767 : BoxExpr 3 := .add ⟨(-117380555183466244219/4722366482869645213696:ℚ),(58007237954344607075/2361183241434822606848:ℚ)⟩ node2752 node2766
def node2768 : BoxExpr 3 := .var 2
def node2769 : BoxExpr 3 := .mul ⟨(-415617178443305462007/4722366482869645213696:ℚ),(-415617178443305462005/4722366482869645213696:ℚ)⟩ node51 node2768
def node2770 : BoxExpr 3 := .add ⟨(1945566062991517144841/4722366482869645213696:ℚ),(1945566062991517144843/4722366482869645213696:ℚ)⟩ node2769 node301
def node2771 : BoxExpr 3 := .mul ⟨(2047841763134812317467/2361183241434822606848:ℚ),(4095683526269624634949/4722366482869645213696:ℚ)⟩ node68 node2770
def node2772 : BoxExpr 3 := .mul ⟨(4873605324497758656993/4722366482869645213696:ℚ),(2436802662248879328507/2361183241434822606848:ℚ)⟩ node2771 node349
def node2773 : BoxExpr 3 := .add ⟨(-24232968874955164877/1180591620717411303424:ℚ),(-48465937749910329753/2361183241434822606848:ℚ)⟩ node2768 node351
def node2774 : BoxExpr 3 := .mul ⟨(4190818135606458431/4722366482869645213696:ℚ),(65481533368850913/73786976294838206464:ℚ)⟩ node2773 node308
def node2775 : BoxExpr 3 := .mul ⟨(4571521820439108183/4722366482869645213696:ℚ),(2285760910219554093/2361183241434822606848:ℚ)⟩ node2774 node69
def node2776 : BoxExpr 3 := .add ⟨(609772105789774720647/590295810358705651712:ℚ),(304886052894887360325/295147905179352825856:ℚ)⟩ node2772 node2775
def node2777 : BoxExpr 3 := .add ⟨(978573709952153732317/295147905179352825856:ℚ),(15657179359234459717149/4722366482869645213696:ℚ)⟩ node2776 node358
def node2778 : BoxExpr 3 := .add ⟨(10902294724454176626255/4722366482869645213696:ℚ),(10902294724454176626337/4722366482869645213696:ℚ)⟩ node2777 node361
def node2779 : BoxExpr 3 := .add ⟨(10902280557354728017319/4722366482869645213696:ℚ),(5451140278677364008701/2361183241434822606848:ℚ)⟩ node2778 node325
def node2780 : BoxExpr 3 := .mul ⟨(229161526541840275209/4722366482869645213696:ℚ),(229161526541840275211/4722366482869645213696:ℚ)⟩ node2768 node2768
def node2781 : BoxExpr 3 := .neg ⟨(-229161526541840275211/4722366482869645213696:ℚ),(-229161526541840275209/4722366482869645213696:ℚ)⟩ node2780
def node2782 : BoxExpr 3 := .add ⟨(4493204956327804938485/4722366482869645213696:ℚ),(4493204956327804938487/4722366482869645213696:ℚ)⟩ node12 node2781
def node2783 : BoxExpr 3 := .sqrt ⟨(4606360872361846774391/4722366482869645213696:ℚ),(4606360872361846774393/4722366482869645213696:ℚ)⟩ node2782
def node2784 : BoxExpr 3 := .mul ⟨(356619241581109425585/147573952589676412928:ℚ),(5705907865297750809367/2361183241434822606848:ℚ)⟩ node50 node2783
def node2785 : BoxExpr 3 := .neg ⟨(260070268401689506611/1180591620717411303424:ℚ),(1040281073606758026445/4722366482869645213696:ℚ)⟩ node2768
def node2786 : BoxExpr 3 := .add ⟨(922221911535016896101/4722366482869645213696:ℚ),(922221911535016896103/4722366482869645213696:ℚ)⟩ node332 node2785
def node2787 : BoxExpr 3 := .mul ⟨(658466444836002063815/4722366482869645213696:ℚ),(329233222418001031909/2361183241434822606848:ℚ)⟩ node2786 node335
def node2788 : BoxExpr 3 := .neg ⟨(-329233222418001031909/2361183241434822606848:ℚ),(-658466444836002063815/4722366482869645213696:ℚ)⟩ node2787
def node2789 : BoxExpr 3 := .add ⟨(5376674642879749777451/2361183241434822606848:ℚ),(10753349285759499554919/4722366482869645213696:ℚ)⟩ node2784 node2788
def node2790 : BoxExpr 3 := .mul ⟨(90049475956647951073/2361183241434822606848:ℚ),(180098951913295902147/4722366482869645213696:ℚ)⟩ node2786 node2786
def node2791 : BoxExpr 3 := .mul ⟨(37190433570095603793/1180591620717411303424:ℚ),(74380867140191207587/2361183241434822606848:ℚ)⟩ node2790 node340
def node2792 : BoxExpr 3 := .add ⟨(5451055510019940985037/2361183241434822606848:ℚ),(10902111020039881970093/4722366482869645213696:ℚ)⟩ node2789 node2791
def node2793 : BoxExpr 3 := .neg ⟨(-10902111020039881970093/4722366482869645213696:ℚ),(-5451055510019940985037/2361183241434822606848:ℚ)⟩ node2792
def node2794 : BoxExpr 3 := .add ⟨(84768657423023613/2361183241434822606848:ℚ),(5298041088938979/147573952589676412928:ℚ)⟩ node2779 node2793
def node2795 : BoxExpr 3 := .mul ⟨(1103224358424514126889/4722366482869645213696:ℚ),(551612179212257063447/2361183241434822606848:ℚ)⟩ node78 node2770
def node2796 : BoxExpr 3 := .mul ⟨(1312767471619188119283/4722366482869645213696:ℚ),(656383735809594059645/2361183241434822606848:ℚ)⟩ node2795 node349
def node2797 : BoxExpr 3 := .add ⟨(1297999702225139776719/1180591620717411303424:ℚ),(5191998808900559107303/4722366482869645213696:ℚ)⟩ node2796 node385
def node2798 : BoxExpr 3 := .add ⟨(1419066374193902629057/2361183241434822606848:ℚ),(2838132748387805258543/4722366482869645213696:ℚ)⟩ node2797 node387
def node2799 : BoxExpr 3 := .mul ⟨(89040547687811130911/147573952589676412928:ℚ),(2849297526009956189161/4722366482869645213696:ℚ)⟩ node77 node2783
def node2800 : BoxExpr 3 := .neg ⟨(-2849297526009956189161/4722366482869645213696:ℚ),(-89040547687811130911/147573952589676412928:ℚ)⟩ node2799
def node2801 : BoxExpr 3 := .add ⟨(-11164777622150931047/4722366482869645213696:ℚ),(-11164777622150930609/4722366482869645213696:ℚ)⟩ node2798 node2800
def node2802 : BoxExpr 3 := .mul ⟨(-927785539898360230077/2361183241434822606848:ℚ),(-927785539898360230071/2361183241434822606848:ℚ)⟩ node98 node2770
def node2803 : BoxExpr 3 := .mul ⟨(-547483600905082007519/1180591620717411303424:ℚ),(-547483600905082007517/1180591620717411303424:ℚ)⟩ node68 node2768
def node2804 : BoxExpr 3 := .add ⟨(-2022752741708524245115/2361183241434822606848:ℚ),(-2022752741708524245105/2361183241434822606848:ℚ)⟩ node2802 node2803
def node2805 : BoxExpr 3 := .mul ⟨(-2406948307627646215401/2361183241434822606848:ℚ),(-4813896615255292430775/4722366482869645213696:ℚ)⟩ node2804 node349
def node2806 : BoxExpr 3 := .mul ⟨(4633904819130154128319/4722366482869645213696:ℚ),(4633904819130154128345/4722366482869645213696:ℚ)⟩ node2771 node399
def node2807 : BoxExpr 3 := .add ⟨(-179991796125138302483/4722366482869645213696:ℚ),(-89995898062569151215/2361183241434822606848:ℚ)⟩ node2805 node2806
def node2808 : BoxExpr 3 := .mul ⟨(2173339405225075375/4722366482869645213696:ℚ),(2173339405225075377/4722366482869645213696:ℚ)⟩ node2774 node103
def node2809 : BoxExpr 3 := .add ⟨(-54592644530270564079/2361183241434822606848:ℚ),(-54592644530270564077/2361183241434822606848:ℚ)⟩ node403 node2808
def node2810 : BoxExpr 3 := .add ⟨(-289177085185679430641/4722366482869645213696:ℚ),(-36147135648209928823/590295810358705651712:ℚ)⟩ node2807 node2809
def node2811 : BoxExpr 3 := .add ⟨(32740149438989399633/4722366482869645213696:ℚ),(16370074719494699903/2361183241434822606848:ℚ)⟩ node2810 node409
def node2812 : BoxExpr 3 := .add ⟨(-1040281073606758026445/2361183241434822606848:ℚ),(-260070268401689506611/590295810358705651712:ℚ)⟩ node2768 node2768
def node2813 : BoxExpr 3 := .neg ⟨(260070268401689506611/590295810358705651712:ℚ),(1040281073606758026445/2361183241434822606848:ℚ)⟩ node2812
def node2814 : BoxExpr 3 := .mul ⟨(4606360872361846774391/2361183241434822606848:ℚ),(4606360872361846774393/2361183241434822606848:ℚ)⟩ node86 node2783
def node2815 : BoxExpr 3 := .inv ⟨(605161694243688010739/1180591620717411303424:ℚ),(1210323388487376021479/2361183241434822606848:ℚ)⟩ node2814
def node2816 : BoxExpr 3 := .mul ⟨(266619822615273287153/1180591620717411303424:ℚ),(533239645230546574307/2361183241434822606848:ℚ)⟩ node2813 node2815
def node2817 : BoxExpr 3 := .mul ⟨(2642099800790900040363/4722366482869645213696:ℚ),(1321049900395450020185/2361183241434822606848:ℚ)⟩ node50 node2816
def node2818 : BoxExpr 3 := .add ⟨(6013869469559826722941/4722366482869645213696:ℚ),(6013869469559826722949/4722366482869645213696:ℚ)⟩ node2817 node335
def node2819 : BoxExpr 3 := .mul ⟨(-922221911535016896103/4722366482869645213696:ℚ),(-922221911535016896101/4722366482869645213696:ℚ)⟩ node422 node2786
def node2820 : BoxExpr 3 := .mul ⟨(-922221911535016896103/4722366482869645213696:ℚ),(-922221911535016896101/4722366482869645213696:ℚ)⟩ node2786 node422
def node2821 : BoxExpr 3 := .add ⟨(-922221911535016896103/2361183241434822606848:ℚ),(-922221911535016896101/2361183241434822606848:ℚ)⟩ node2819 node2820
def node2822 : BoxExpr 3 := .mul ⟨(-1523510597855847912363/4722366482869645213696:ℚ),(-761755298927923956179/2361183241434822606848:ℚ)⟩ node2821 node340
def node2823 : BoxExpr 3 := .add ⟨(2245179435851989405289/2361183241434822606848:ℚ),(4490358871703978810591/4722366482869645213696:ℚ)⟩ node2818 node2822
def node2824 : BoxExpr 3 := .neg ⟨(-4490358871703978810591/4722366482869645213696:ℚ),(-2245179435851989405289/2361183241434822606848:ℚ)⟩ node2823
def node2825 : BoxExpr 3 := .add ⟨(204169221494618797/73786976294838206464:ℚ),(408338442989237595/147573952589676412928:ℚ)⟩ node414 node2824
def node2826 : BoxExpr 3 := .mul ⟨(4376666698196514702593/2361183241434822606848:ℚ),(8796682640876012342293/4722366482869645213696:ℚ)⟩ node112 node2743
def node2827 : BoxExpr 3 := .mul ⟨(10396194922263098428715/4722366482869645213696:ℚ),(5243745668596899666301/2361183241434822606848:ℚ)⟩ node2826 node304
def node2828 : BoxExpr 3 := .add ⟨(10861202920562941295719/2361183241434822606848:ℚ),(44813840949854617746883/4722366482869645213696:ℚ)⟩ node2827 node448
def node2829 : BoxExpr 3 := .mul ⟨(1416303678190621002955/295147905179352825856:ℚ),(22665726746358531796421/4722366482869645213696:ℚ)⟩ node111 node2756
def node2830 : BoxExpr 3 := .neg ⟨(-22665726746358531796421/4722366482869645213696:ℚ),(-1416303678190621002955/295147905179352825856:ℚ)⟩ node2829
def node2831 : BoxExpr 3 := .add ⟨(-943320905232649204983/4722366482869645213696:ℚ),(22152982098804681699603/4722366482869645213696:ℚ)⟩ node2828 node2830
def node2832 : BoxExpr 3 := .mul ⟨(-541020008735845884565/4722366482869645213696:ℚ),(-254073594488470766795/2361183241434822606848:ℚ)⟩ node131 node2743
def node2833 : BoxExpr 3 := .mul ⟨(-2366437643076729979/18446744073709551616:ℚ),(-574050303439273460753/4722366482869645213696:ℚ)⟩ node118 node2741
def node2834 : BoxExpr 3 := .add ⟨(-1146828045363488759189/4722366482869645213696:ℚ),(-1082197492416214994343/4722366482869645213696:ℚ)⟩ node2832 node2833
def node2835 : BoxExpr 3 := .mul ⟨(-1367259645711482614443/4722366482869645213696:ℚ),(-1285308757938933662643/4722366482869645213696:ℚ)⟩ node2834 node304
def node2836 : BoxExpr 3 := .mul ⟨(1074235344782368576553/4722366482869645213696:ℚ),(283083847502424764323/1180591620717411303424:ℚ)⟩ node118 node2743
def node2837 : BoxExpr 3 := .mul ⟨(1204743502954720526855/4722366482869645213696:ℚ),(1292474214356884686807/4722366482869645213696:ℚ)⟩ node2836 node461
def node2838 : BoxExpr 3 := .add ⟨(-40629035689190521897/1180591620717411303424:ℚ),(1791364104487756041/1180591620717411303424:ℚ)⟩ node2835 node2837
def node2839 : BoxExpr 3 := .add ⟨(-2919816867651232929547/4722366482869645213696:ℚ),(355184834247402699267/1180591620717411303424:ℚ)⟩ node2838 node476
def node2840 : BoxExpr 3 := .add ⟨(-260617906116377758925/590295810358705651712:ℚ),(-519045261374002508595/1180591620717411303424:ℚ)⟩ node2741 node2741
def node2841 : BoxExpr 3 := .neg ⟨(519045261374002508595/1180591620717411303424:ℚ),(260617906116377758925/590295810358705651712:ℚ)⟩ node2840
def node2842 : BoxExpr 3 := .mul ⟨(2302932810066050411309/1180591620717411303424:ℚ),(4606855029747669064313/2361183241434822606848:ℚ)⟩ node86 node2756
def node2843 : BoxExpr 3 := .inv ⟨(1210193562339647805095/2361183241434822606848:ℚ),(1210453530225389831999/2361183241434822606848:ℚ)⟩ node2842
def node2844 : BoxExpr 3 := .mul ⟨(266029854377592500905/1180591620717411303424:ℚ),(534419961928612053757/2361183241434822606848:ℚ)⟩ node2841 node2843
def node2845 : BoxExpr 3 := .mul ⟨(642512288400112964945/4722366482869645213696:ℚ),(676914671305903148933/4722366482869645213696:ℚ)⟩ node117 node2844
def node2846 : BoxExpr 3 := .neg ⟨(-676914671305903148933/4722366482869645213696:ℚ),(-642512288400112964945/4722366482869645213696:ℚ)⟩ node2845
def node2847 : BoxExpr 3 := .add ⟨(278007960400230413507/2361183241434822606848:ℚ),(671182858329147736781/4722366482869645213696:ℚ)⟩ node479 node2846
def node2848 : BoxExpr 3 := .add ⟨(-1459908433825616464773/2361183241434822606848:ℚ),(355184834247402699267/1180591620717411303424:ℚ)⟩ node2838 node492
def node2849 : BoxExpr 3 := .mul ⟨(-2001937113321213720053/4722366482869645213696:ℚ),(-1950865928634275288911/4722366482869645213696:ℚ)⟩ node175 node2743
def node2850 : BoxExpr 3 := .mul ⟨(244503239093251564597/1180591620717411303424:ℚ),(1006409948507367917871/4722366482869645213696:ℚ)⟩ node148 node2741
def node2851 : BoxExpr 3 := .add ⟨(-1023924156948207461665/4722366482869645213696:ℚ),(-29514249378965855345/147573952589676412928:ℚ)⟩ node2849 node2850
def node2852 : BoxExpr 3 := .add ⟨(-45911200575201203277/4722366482869645213696:ℚ),(61953968380460546831/4722366482869645213696:ℚ)⟩ node2851 node2850
def node2853 : BoxExpr 3 := .mul ⟨(-54735783700461015421/4722366482869645213696:ℚ),(4616383053280713829/295147905179352825856:ℚ)⟩ node2852 node304
def node2854 : BoxExpr 3 := .mul ⟨(-1881113376931276278935/4722366482869645213696:ℚ),(-1830181221221356860723/4722366482869645213696:ℚ)⟩ node148 node2743
def node2855 : BoxExpr 3 := .mul ⟨(-2202189566693599117853/4722366482869645213696:ℚ),(-68054770099186087687/147573952589676412928:ℚ)⟩ node36 node2741
def node2856 : BoxExpr 3 := .add ⟨(-1020825735906218849197/1180591620717411303424:ℚ),(-4007933864395311666707/4722366482869645213696:ℚ)⟩ node2854 node2855
def node2857 : BoxExpr 3 := .mul ⟨(-2330388951279492500707/2361183241434822606848:ℚ),(-280928447549631183657/295147905179352825856:ℚ)⟩ node2856 node461
def node2858 : BoxExpr 3 := .add ⟨(-4715513686259446016835/4722366482869645213696:ℚ),(-69078016124087617457/73786976294838206464:ℚ)⟩ node2853 node2857
def node2859 : BoxExpr 3 := .mul ⟨(2511962643645362929881/590295810358705651712:ℚ),(20731809477919954873887/4722366482869645213696:ℚ)⟩ node2744 node514
def node2860 : BoxExpr 3 := .add ⟨(7717461623301959218817/2361183241434822606848:ℚ),(16236954317125855935375/4722366482869645213696:ℚ)⟩ node2857 node2859
def node2861 : BoxExpr 3 := .add ⟨(10719409560344472420799/4722366482869645213696:ℚ),(11815961285184248418127/4722366482869645213696:ℚ)⟩ node2858 node2860
def node2862 : BoxExpr 3 := .mul ⟨(1967582387117909589/1180591620717411303424:ℚ),(4609428736971461141/2361183241434822606848:ℚ)⟩ node2747 node189
def node2863 : BoxExpr 3 := .add ⟨(-11372004032657240537/1180591620717411303424:ℚ),(-10826853649421965913/1180591620717411303424:ℚ)⟩ node518 node2862
def node2864 : BoxExpr 3 := .add ⟨(-24711590452432390663/1180591620717411303424:ℚ),(-47916843334659324793/2361183241434822606848:ℚ)⟩ node518 node2863
def node2865 : BoxExpr 3 := .add ⟨(10620563198534742858147/4722366482869645213696:ℚ),(11720127598514929768541/4722366482869645213696:ℚ)⟩ node2861 node2864
def node2866 : BoxExpr 3 := .add ⟨(10862148238450657114835/2361183241434822606848:ℚ),(7078399659460594060771/1180591620717411303424:ℚ)⟩ node2865 node527
def node2867 : BoxExpr 3 := .mul ⟨(-1210453530225389831999/1180591620717411303424:ℚ),(-1210193562339647805095/1180591620717411303424:ℚ)⟩ node6 node2843
def node2868 : BoxExpr 3 := .mul ⟨(266029854377592500905/590295810358705651712:ℚ),(534419961928612053757/1180591620717411303424:ℚ)⟩ node86 node2844
def node2869 : BoxExpr 3 := .mul ⟨(17968955342765968473447/4722366482869645213696:ℚ),(8988338089429571815345/2361183241434822606848:ℚ)⟩ node2842 node2842
def node2870 : BoxExpr 3 := .inv ⟨(155067217214191222925/590295810358705651712:ℚ),(620535383753084126851/2361183241434822606848:ℚ)⟩ node2869
def node2871 : BoxExpr 3 := .mul ⟨(559075751381827929961/4722366482869645213696:ℚ),(561797136861195206061/4722366482869645213696:ℚ)⟩ node2868 node2870
def node2872 : BoxExpr 3 := .neg ⟨(-561797136861195206061/4722366482869645213696:ℚ),(-559075751381827929961/4722366482869645213696:ℚ)⟩ node2871
def node2873 : BoxExpr 3 := .mul ⟨(-1937778362845965215/36893488147419103232:ℚ),(-245796780539159115301/4722366482869645213696:ℚ)⟩ node2841 node2872
def node2874 : BoxExpr 3 := .add ⟨(-1272462437836460718879/1180591620717411303424:ℚ),(-5086571029897750335681/4722366482869645213696:ℚ)⟩ node2867 node2873
def node2875 : BoxExpr 3 := .mul ⟨(-12619170674169199910881/4722366482869645213696:ℚ),(-12592163790754842759381/4722366482869645213696:ℚ)⟩ node11 node2874
def node2876 : BoxExpr 3 := .add ⟨(-75278456944821031529/73786976294838206464:ℚ),(-4790814361054188866355/4722366482869645213696:ℚ)⟩ node2875 node546
def node2877 : BoxExpr 3 := .neg ⟨(4790814361054188866355/4722366482869645213696:ℚ),(75278456944821031529/73786976294838206464:ℚ)⟩ node2876
def cert_iv17 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-9023/40960:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/40960:ℚ)],
    whole := node2767, centerValue := node2794, gradient := ![node2801, node2811, node2825],
    hessian := ![![node2831, node2839, node2847], ![node2848, node2866, node536], ![node2847, node536, node2877]] }
def node2878 : BoxExpr 3 := .var 2
def node2879 : BoxExpr 3 := .mul ⟨(-52102272751261122665/590295810358705651712:ℚ),(-102731056791276747961/1180591620717411303424:ℚ)⟩ node13 node2878
def node2880 : BoxExpr 3 := .add ⟨(243045632428091703191/590295810358705651712:ℚ),(487564753567428903751/1180591620717411303424:ℚ)⟩ node2879 node301
def node2881 : BoxExpr 3 := .mul ⟨(4078975825969638297513/4722366482869645213696:ℚ),(4119862788377508082149/4722366482869645213696:ℚ)⟩ node36 node2880
def node2882 : BoxExpr 3 := .mul ⟨(4844534744609816403739/4722366482869645213696:ℚ),(4911740830885932855023/4722366482869645213696:ℚ)⟩ node2881 node304
def node2883 : BoxExpr 3 := .add ⟨(-24865922780984323867/1180591620717411303424:ℚ),(-85637856440691986529/4722366482869645213696:ℚ)⟩ node2878 node306
def node2884 : BoxExpr 3 := .mul ⟨(3702524891997765397/4722366482869645213696:ℚ),(1075070090326805755/1180591620717411303424:ℚ)⟩ node2883 node308
def node2885 : BoxExpr 3 := .mul ⟨(2017522854176729177/2361183241434822606848:ℚ),(2347702814487470039/2361183241434822606848:ℚ)⟩ node2884 node37
def node2886 : BoxExpr 3 := .add ⟨(4848569790318169862093/4722366482869645213696:ℚ),(4916436236514907795101/4722366482869645213696:ℚ)⟩ node2882 node2885
def node2887 : BoxExpr 3 := .add ⟨(3890753511364389055475/1180591620717411303424:ℚ),(15758200233374698292343/4722366482869645213696:ℚ)⟩ node2886 node316
def node2888 : BoxExpr 3 := .add ⟨(337533369140491714673/147573952589676412928:ℚ),(5505188598387976731539/2361183241434822606848:ℚ)⟩ node2887 node323
def node2889 : BoxExpr 3 := .add ⟨(1350131705674535782575/590295810358705651712:ℚ),(11010363029676504854143/4722366482869645213696:ℚ)⟩ node2888 node325
def node2890 : BoxExpr 3 := .mul ⟨(226275358128892920463/4722366482869645213696:ℚ),(114098719077429653013/2361183241434822606848:ℚ)⟩ node2878 node2878
def node2891 : BoxExpr 3 := .neg ⟨(-114098719077429653013/2361183241434822606848:ℚ),(-226275358128892920463/4722366482869645213696:ℚ)⟩ node2890
def node2892 : BoxExpr 3 := .add ⟨(2247084522357392953835/2361183241434822606848:ℚ),(4496091124740752293233/4722366482869645213696:ℚ)⟩ node12 node2891
def node2893 : BoxExpr 3 := .sqrt ⟨(4606855029747669064311/4722366482869645213696:ℚ),(4607840061395730963593/4722366482869645213696:ℚ)⟩ node2892
def node2894 : BoxExpr 3 := .mul ⟨(11404593144158165468875/4722366482869645213696:ℚ),(5712066467055528102179/2361183241434822606848:ℚ)⟩ node11 node2893
def node2895 : BoxExpr 3 := .neg ⟨(1033709421030498998681/4722366482869645213696:ℚ),(1038090522748005017191/4722366482869645213696:ℚ)⟩ node2878
def node2896 : BoxExpr 3 := .add ⟨(457825129479378934169/2361183241434822606848:ℚ),(920031360676263886849/4722366482869645213696:ℚ)⟩ node332 node2895
def node2897 : BoxExpr 3 := .mul ⟨(653774284896553117993/4722366482869645213696:ℚ),(656902391522852415211/4722366482869645213696:ℚ)⟩ node2896 node335
def node2898 : BoxExpr 3 := .neg ⟨(-656902391522852415211/4722366482869645213696:ℚ),(-653774284896553117993/4722366482869645213696:ℚ)⟩ node2897
def node2899 : BoxExpr 3 := .add ⟨(335865336019853532927/147573952589676412928:ℚ),(10770358649214503086365/4722366482869645213696:ℚ)⟩ node2894 node2898
def node2900 : BoxExpr 3 := .mul ⟨(177541366129161498787/4722366482869645213696:ℚ),(179244391069252583425/4722366482869645213696:ℚ)⟩ node2896 node2896
def node2901 : BoxExpr 3 := .mul ⟨(73324584211343698999/2361183241434822606848:ℚ),(74027933511601316955/2361183241434822606848:ℚ)⟩ node2900 node340
def node2902 : BoxExpr 3 := .add ⟨(5447169960529000225831/2361183241434822606848:ℚ),(10918414516237705720275/4722366482869645213696:ℚ)⟩ node2899 node2901
def node2903 : BoxExpr 3 := .neg ⟨(-10918414516237705720275/4722366482869645213696:ℚ),(-5447169960529000225831/2361183241434822606848:ℚ)⟩ node2902
def node2904 : BoxExpr 3 := .add ⟨(-117360870841419459675/4722366482869645213696:ℚ),(116023108618504402481/4722366482869645213696:ℚ)⟩ node2889 node2903
def node2905 : BoxExpr 3 := .var 2
def node2906 : BoxExpr 3 := .mul ⟨(-103466705871470120141/1180591620717411303424:ℚ),(-413866823485880480563/4722366482869645213696:ℚ)⟩ node51 node2905
def node2907 : BoxExpr 3 := .add ⟨(486829104487235531571/1180591620717411303424:ℚ),(1947316417948942126285/4722366482869645213696:ℚ)⟩ node2906 node301
def node2908 : BoxExpr 3 := .mul ⟨(4099368263632501386443/4722366482869645213696:ℚ),(4099368263632501386455/4722366482869645213696:ℚ)⟩ node68 node2907
def node2909 : BoxExpr 3 := .mul ⟨(1219497482445452996397/1180591620717411303424:ℚ),(4877989929781811985605/4722366482869645213696:ℚ)⟩ node2908 node349
def node2910 : BoxExpr 3 := .add ⟨(-92550773782314640999/4722366482869645213696:ℚ),(-46275386891157320499/2361183241434822606848:ℚ)⟩ node2905 node351
def node2911 : BoxExpr 3 := .mul ⟨(31260958020722611/36893488147419103232:ℚ),(4001402626652494209/4722366482869645213696:ℚ)⟩ node2910 node308
def node2912 : BoxExpr 3 := .mul ⟨(1091224841319504637/1180591620717411303424:ℚ),(2182449682639009275/2361183241434822606848:ℚ)⟩ node2911 node69
def node2913 : BoxExpr 3 := .add ⟨(610294353643386250517/590295810358705651712:ℚ),(4882354829147090004155/4722366482869645213696:ℚ)⟩ node2909 node2912
def node2914 : BoxExpr 3 := .add ⟨(244708708469739874313/73786976294838206464:ℚ),(1957669667757918994513/590295810358705651712:ℚ)⟩ node2913 node358
def node2915 : BoxExpr 3 := .add ⟨(10906472707283068865215/4722366482869645213696:ℚ),(2726618176820767216323/1180591620717411303424:ℚ)⟩ node2914 node361
def node2916 : BoxExpr 3 := .add ⟨(10906458540183620256279/4722366482869645213696:ℚ),(10906458540183620256357/4722366482869645213696:ℚ)⟩ node2915 node325
def node2917 : BoxExpr 3 := .mul ⟨(3229209/67108864:ℚ),(3229209/67108864:ℚ)⟩ node2905 node2905
def node2918 : BoxExpr 3 := .neg ⟨(-3229209/67108864:ℚ),(-3229209/67108864:ℚ)⟩ node2917
def node2919 : BoxExpr 3 := .add ⟨(63879655/67108864:ℚ),(63879655/67108864:ℚ)⟩ node12 node2918
def node2920 : BoxExpr 3 := .sqrt ⟨(4607348092641847485665/4722366482869645213696:ℚ),(2303674046320923742833/2361183241434822606848:ℚ)⟩ node2919
def node2921 : BoxExpr 3 := .mul ⟨(11414261473826013765251/4722366482869645213696:ℚ),(11414261473826013765263/4722366482869645213696:ℚ)⟩ node50 node2920
def node2922 : BoxExpr 3 := .neg ⟨(1797/8192:ℚ),(1797/8192:ℚ)⟩ node2905
def node2923 : BoxExpr 3 := .add ⟨(917840809817510877593/4722366482869645213696:ℚ),(458920404908755438797/2361183241434822606848:ℚ)⟩ node332 node2922
def node2924 : BoxExpr 3 := .mul ⟨(655338338209702766601/4722366482869645213696:ℚ),(655338338209702766603/4722366482869645213696:ℚ)⟩ node2923 node335
def node2925 : BoxExpr 3 := .neg ⟨(-655338338209702766603/4722366482869645213696:ℚ),(-655338338209702766601/4722366482869645213696:ℚ)⟩ node2924
def node2926 : BoxExpr 3 := .add ⟨(1344865391952038874831/590295810358705651712:ℚ),(5379461567808155499331/2361183241434822606848:ℚ)⟩ node2921 node2925
def node2927 : BoxExpr 3 := .mul ⟨(178391862474541115637/4722366482869645213696:ℚ),(89195931237270557819/2361183241434822606848:ℚ)⟩ node2923 node2923
def node2928 : BoxExpr 3 := .mul ⟨(36837919600992740379/1180591620717411303424:ℚ),(147351678403970961517/4722366482869645213696:ℚ)⟩ node2927 node340
def node2929 : BoxExpr 3 := .add ⟨(2726568703505070490041/1180591620717411303424:ℚ),(10906274814020281960179/4722366482869645213696:ℚ)⟩ node2926 node2928
def node2930 : BoxExpr 3 := .neg ⟨(-10906274814020281960179/4722366482869645213696:ℚ),(-2726568703505070490041/1180591620717411303424:ℚ)⟩ node2929
def node2931 : BoxExpr 3 := .add ⟨(45931540834574025/1180591620717411303424:ℚ),(183726163338296193/4722366482869645213696:ℚ)⟩ node2916 node2930
def node2932 : BoxExpr 3 := .mul ⟨(276054222304068272973/1180591620717411303424:ℚ),(1104216889216273091897/4722366482869645213696:ℚ)⟩ node78 node2907
def node2933 : BoxExpr 3 := .mul ⟨(656974260360675552067/2361183241434822606848:ℚ),(656974260360675552071/2361183241434822606848:ℚ)⟩ node2932 node349
def node2934 : BoxExpr 3 := .add ⟨(5193179858002722091727/4722366482869645213696:ℚ),(5193179858002722092155/4722366482869645213696:ℚ)⟩ node2933 node385
def node2935 : BoxExpr 3 := .add ⟨(2839313797489968242965/4722366482869645213696:ℚ),(2839313797489968243395/4722366482869645213696:ℚ)⟩ node2934 node387
def node2936 : BoxExpr 3 := .mul ⟨(2849908178188405815481/4722366482869645213696:ℚ),(2849908178188405815489/4722366482869645213696:ℚ)⟩ node77 node2920
def node2937 : BoxExpr 3 := .neg ⟨(-2849908178188405815489/4722366482869645213696:ℚ),(-2849908178188405815481/4722366482869645213696:ℚ)⟩ node2936
def node2938 : BoxExpr 3 := .add ⟨(-2648595174609393131/1180591620717411303424:ℚ),(-5297190349218786043/2361183241434822606848:ℚ)⟩ node2935 node2937
def node2939 : BoxExpr 3 := .mul ⟨(-1857240469544084066729/4722366482869645213696:ℚ),(-1857240469544084066719/4722366482869645213696:ℚ)⟩ node98 node2907
def node2940 : BoxExpr 3 := .mul ⟨(-2180711583345743915575/4722366482869645213696:ℚ),(-2180711583345743915569/4722366482869645213696:ℚ)⟩ node68 node2905
def node2941 : BoxExpr 3 := .add ⟨(-126186001652807124447/147573952589676412928:ℚ),(-252372003305614248893/295147905179352825856:ℚ)⟩ node2939 node2940
def node2942 : BoxExpr 3 := .mul ⟨(-4804908508874618338435/4722366482869645213696:ℚ),(-4804908508874618338413/4722366482869645213696:ℚ)⟩ node2941 node349
def node2943 : BoxExpr 3 := .mul ⟨(2319036887297981305795/2361183241434822606848:ℚ),(1159518443648990652903/1180591620717411303424:ℚ)⟩ node2908 node399
def node2944 : BoxExpr 3 := .add ⟨(-166834734278655726845/4722366482869645213696:ℚ),(-166834734278655726801/4722366482869645213696:ℚ)⟩ node2942 node2943
def node2945 : BoxExpr 3 := .mul ⟨(2075109375610382703/4722366482869645213696:ℚ),(129694335975648919/295147905179352825856:ℚ)⟩ node2911 node103
def node2946 : BoxExpr 3 := .add ⟨(-54641759545077910415/2361183241434822606848:ℚ),(-109283519090155820827/4722366482869645213696:ℚ)⟩ node403 node2945
def node2947 : BoxExpr 3 := .add ⟨(-276118253368811547675/4722366482869645213696:ℚ),(-69029563342202886907/1180591620717411303424:ℚ)⟩ node2944 node2946
def node2948 : BoxExpr 3 := .add ⟨(45798981255857282599/4722366482869645213696:ℚ),(22899490627928641381/2361183241434822606848:ℚ)⟩ node2947 node409
def node2949 : BoxExpr 3 := .add ⟨(-1797/4096:ℚ),(-1797/4096:ℚ)⟩ node2905 node2905
def node2950 : BoxExpr 3 := .neg ⟨(1797/4096:ℚ),(1797/4096:ℚ)⟩ node2949
def node2951 : BoxExpr 3 := .mul ⟨(4607348092641847485665/2361183241434822606848:ℚ),(2303674046320923742833/1180591620717411303424:ℚ)⟩ node86 node2920
def node2952 : BoxExpr 3 := .inv ⟨(1210064051495586284961/2361183241434822606848:ℚ),(2420128102991172569923/4722366482869645213696:ℚ)⟩ node2951
def node2953 : BoxExpr 3 := .mul ⟨(132720037874607455693/590295810358705651712:ℚ),(1061760302996859645545/4722366482869645213696:ℚ)⟩ node2950 node2952
def node2954 : BoxExpr 3 := .mul ⟨(657602240879620124993/1180591620717411303424:ℚ),(1315204481759240249989/2361183241434822606848:ℚ)⟩ node50 node2953
def node2955 : BoxExpr 3 := .add ⟨(3001089316143703591275/2361183241434822606848:ℚ),(6002178632287407182557/4722366482869645213696:ℚ)⟩ node2954 node335
def node2956 : BoxExpr 3 := .mul ⟨(-458920404908755438797/2361183241434822606848:ℚ),(-917840809817510877593/4722366482869645213696:ℚ)⟩ node422 node2923
def node2957 : BoxExpr 3 := .mul ⟨(-458920404908755438797/2361183241434822606848:ℚ),(-917840809817510877593/4722366482869645213696:ℚ)⟩ node2923 node422
def node2958 : BoxExpr 3 := .add ⟨(-458920404908755438797/1180591620717411303424:ℚ),(-917840809817510877593/2361183241434822606848:ℚ)⟩ node2956 node2957
def node2959 : BoxExpr 3 := .mul ⟨(-758136508909263984893/2361183241434822606848:ℚ),(-1516273017818527969783/4722366482869645213696:ℚ)⟩ node2958 node340
def node2960 : BoxExpr 3 := .add ⟨(1121476403617219803191/1180591620717411303424:ℚ),(2242952807234439606387/2361183241434822606848:ℚ)⟩ node2955 node2959
def node2961 : BoxExpr 3 := .neg ⟨(-2242952807234439606387/2361183241434822606848:ℚ),(-1121476403617219803191/1180591620717411303424:ℚ)⟩ node2960
def node2962 : BoxExpr 3 := .add ⟨(17520087410755200825/4722366482869645213696:ℚ),(8760043705377600427/2361183241434822606848:ℚ)⟩ node414 node2961
def node2963 : BoxExpr 3 := .mul ⟨(8761259933966768724837/4722366482869645213696:ℚ),(4402272575703504798943/2361183241434822606848:ℚ)⟩ node112 node2880
def node2964 : BoxExpr 3 := .mul ⟨(10405609144930453153193/4722366482869645213696:ℚ),(2624216274844413908249/1180591620717411303424:ℚ)⟩ node2963 node304
def node2965 : BoxExpr 3 := .add ⟨(5432955015948309328979/1180591620717411303424:ℚ),(44823214712038474047277/4722366482869645213696:ℚ)⟩ node2964 node448
def node2966 : BoxExpr 3 := .mul ⟨(22665726746358531796409/4722366482869645213696:ℚ),(22670573102066996340879/4722366482869645213696:ℚ)⟩ node111 node2893
def node2967 : BoxExpr 3 := .neg ⟨(-22670573102066996340879/4722366482869645213696:ℚ),(-22665726746358531796409/4722366482869645213696:ℚ)⟩ node2966
def node2968 : BoxExpr 3 := .add ⟨(-938753038273759024963/4722366482869645213696:ℚ),(5539371991419985562717/1180591620717411303424:ℚ)⟩ node2965 node2967
def node2969 : BoxExpr 3 := .mul ⟨(-8460993353255093609/73786976294838206464:ℚ),(-254303669569814948761/2361183241434822606848:ℚ)⟩ node131 node2880
def node2970 : BoxExpr 3 := .mul ⟨(-150815515422342856755/1180591620717411303424:ℚ),(-142906903060765377863/1180591620717411303424:ℚ)⟩ node118 node2878
def node2971 : BoxExpr 3 := .add ⟨(-286191409074424354499/1180591620717411303424:ℚ),(-540117475691345704487/2361183241434822606848:ℚ)⟩ node2969 node2970
def node2972 : BoxExpr 3 := .mul ⟨(-341200205347912462495/1180591620717411303424:ℚ),(-1282977879152132478687/4722366482869645213696:ℚ)⟩ node2971 node304
def node2973 : BoxExpr 3 := .mul ⟨(1075208113262427271065/4722366482869645213696:ℚ),(1133347475962101398779/4722366482869645213696:ℚ)⟩ node118 node2880
def node2974 : BoxExpr 3 := .mul ⟨(1205834452449095314643/4722366482869645213696:ℚ),(1293629433038322923203/4722366482869645213696:ℚ)⟩ node2973 node461
def node2975 : BoxExpr 3 := .add ⟨(-158966368942554535337/4722366482869645213696:ℚ),(2662888471547611129/1180591620717411303424:ℚ)⟩ node2972 node2974
def node2976 : BoxExpr 3 := .add ⟨(-182266693364814086081/295147905179352825856:ℚ),(356056358614462554355/1180591620717411303424:ℚ)⟩ node2975 node476
def node2977 : BoxExpr 3 := .add ⟨(-1038090522748005017191/2361183241434822606848:ℚ),(-1033709421030498998681/2361183241434822606848:ℚ)⟩ node2878 node2878
def node2978 : BoxExpr 3 := .neg ⟨(1033709421030498998681/2361183241434822606848:ℚ),(1038090522748005017191/2361183241434822606848:ℚ)⟩ node2977
def node2979 : BoxExpr 3 := .mul ⟨(4606855029747669064311/2361183241434822606848:ℚ),(4607840061395730963593/2361183241434822606848:ℚ)⟩ node86 node2893
def node2980 : BoxExpr 3 := .inv ⟨(604967427834714411007/1180591620717411303424:ℚ),(151274195292455975637/295147905179352825856:ℚ)⟩ node2979
def node2981 : BoxExpr 3 := .mul ⟨(264850486228811006303/1180591620717411303424:ℚ),(1064119417510370003623/4722366482869645213696:ℚ)⟩ node2978 node2980
def node2982 : BoxExpr 3 := .mul ⟨(639663891817283318291/4722366482869645213696:ℚ),(673925093605019087457/4722366482869645213696:ℚ)⟩ node117 node2981
def node2983 : BoxExpr 3 := .neg ⟨(-673925093605019087457/4722366482869645213696:ℚ),(-639663891817283318291/4722366482869645213696:ℚ)⟩ node2982
def node2984 : BoxExpr 3 := .add ⟨(279502749250672444245/2361183241434822606848:ℚ),(674031254911977383435/4722366482869645213696:ℚ)⟩ node479 node2983
def node2985 : BoxExpr 3 := .add ⟨(-2916267093837025377295/4722366482869645213696:ℚ),(356056358614462554355/1180591620717411303424:ℚ)⟩ node2975 node492
def node2986 : BoxExpr 3 := .mul ⟨(-250465806601480798115/590295810358705651712:ℚ),(-976316262792380201561/2361183241434822606848:ℚ)⟩ node175 node2880
def node2987 : BoxExpr 3 := .mul ⟨(973885402803240128021/4722366482869645213696:ℚ),(1002180399951375882825/4722366482869645213696:ℚ)⟩ node148 node2878
def node2988 : BoxExpr 3 := .add ⟨(-1029841050008606256899/4722366482869645213696:ℚ),(-950452125633384520297/4722366482869645213696:ℚ)⟩ node2986 node2987
def node2989 : BoxExpr 3 := .add ⟨(-27977823602683064439/2361183241434822606848:ℚ),(1616508572437230079/147573952589676412928:ℚ)⟩ node2988 node2987
def node2990 : BoxExpr 3 := .mul ⟨(-66710871505864642265/4722366482869645213696:ℚ),(61670956080313292297/4722366482869645213696:ℚ)⟩ node2989 node304
def node2991 : BoxExpr 3 := .mul ⟨(-1882794723677536649783/4722366482869645213696:ℚ),(-1831838532734561769945/4722366482869645213696:ℚ)⟩ node148 node2880
def node2992 : BoxExpr 3 := .mul ⟨(-2192934622706167491389/4722366482869645213696:ℚ),(-2168561772400897244607/4722366482869645213696:ℚ)⟩ node36 node2878
def node2993 : BoxExpr 3 := .add ⟨(-1018932336595926035293/1180591620717411303424:ℚ),(-500050038141932376819/590295810358705651712:ℚ)⟩ node2991 node2992
def node2994 : BoxExpr 3 := .mul ⟨(-1163033305188283445977/1180591620717411303424:ℚ),(-560800794285726183861/590295810358705651712:ℚ)⟩ node2993 node461
def node2995 : BoxExpr 3 := .add ⟨(-4718844092258998426173/4722366482869645213696:ℚ),(-4424735398205496178591/4722366482869645213696:ℚ)⟩ node2990 node2994
def node2996 : BoxExpr 3 := .mul ⟨(20113898711510421728555/4722366482869645213696:ℚ),(20750339653100918512529/4722366482869645213696:ℚ)⟩ node2881 node514
def node2997 : BoxExpr 3 := .add ⟨(15461765490757287944647/4722366482869645213696:ℚ),(16263933298815109041641/4722366482869645213696:ℚ)⟩ node2994 node2996
def node2998 : BoxExpr 3 := .add ⟨(5371460699249144759237/2361183241434822606848:ℚ),(5919598950304806431525/2361183241434822606848:ℚ)⟩ node2995 node2997
def node2999 : BoxExpr 3 := .mul ⟨(3743645593123149793/2361183241434822606848:ℚ),(8829923650614846601/4722366482869645213696:ℚ)⟩ node2884 node189
def node3000 : BoxExpr 3 := .add ⟨(-22935527246427150459/2361183241434822606848:ℚ),(-43696348421015939333/4722366482869645213696:ℚ)⟩ node518 node2999
def node3001 : BoxExpr 3 := .add ⟨(-49614700085977450711/2361183241434822606848:ℚ),(-96222620492646725267/4722366482869645213696:ℚ)⟩ node518 node3000
def node3002 : BoxExpr 3 := .add ⟨(2660922999581583654263/1180591620717411303424:ℚ),(11742975280116966137783/4722366482869645213696:ℚ)⟩ node2998 node3001
def node3003 : BoxExpr 3 := .add ⟨(21747425276692905988575/4722366482869645213696:ℚ),(14168223159722206306163/2361183241434822606848:ℚ)⟩ node3002 node527
def node3004 : BoxExpr 3 := .mul ⟨(-151274195292455975637/147573952589676412928:ℚ),(-604967427834714411007/590295810358705651712:ℚ)⟩ node6 node2980
def node3005 : BoxExpr 3 := .mul ⟨(264850486228811006303/590295810358705651712:ℚ),(1064119417510370003623/2361183241434822606848:ℚ)⟩ node86 node2981
def node3006 : BoxExpr 3 := .mul ⟨(8988338089429571815337/2361183241434822606848:ℚ),(17984364498963009172933/4722366482869645213696:ℚ)⟩ node2979 node2979
def node3007 : BoxExpr 3 := .inv ⟨(310001851883847486641/1180591620717411303424:ℚ),(620268868856764891701/2361183241434822606848:ℚ)⟩ node3006
def node3008 : BoxExpr 3 := .mul ⟨(69544912705188057833/590295810358705651712:ℚ),(139768937845456982491/1180591620717411303424:ℚ)⟩ node3005 node3007
def node3009 : BoxExpr 3 := .neg ⟨(-139768937845456982491/1180591620717411303424:ℚ),(-69544912705188057833/590295810358705651712:ℚ)⟩ node3008
def node3010 : BoxExpr 3 := .mul ⟨(-245796780539159115303/4722366482869645213696:ℚ),(-243570190357310986925/4722366482869645213696:ℚ)⟩ node2978 node3009
def node3011 : BoxExpr 3 := .add ⟨(-5086571029897750335687/4722366482869645213696:ℚ),(-5083309613035026274981/4722366482869645213696:ℚ)⟩ node3004 node3010
def node3012 : BoxExpr 3 := .mul ⟨(-12611041800515198873909/4722366482869645213696:ℚ),(-12584089924277020916215/4722366482869645213696:ℚ)⟩ node11 node3011
def node3013 : BoxExpr 3 := .add ⟨(-1202423092703636245221/1180591620717411303424:ℚ),(-4782740494576367023189/4722366482869645213696:ℚ)⟩ node3012 node546
def node3014 : BoxExpr 3 := .neg ⟨(4782740494576367023189/4722366482869645213696:ℚ),(1202423092703636245221/1180591620717411303424:ℚ)⟩ node3013
def cert_iv18 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-1797/8192:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/40960:ℚ)],
    whole := node2904, centerValue := node2931, gradient := ![node2938, node2948, node2962],
    hessian := ![![node2968, node2976, node2984], ![node2985, node3003, node536], ![node2984, node536, node3014]] }
def node3015 : BoxExpr 3 := .var 2
def node3016 : BoxExpr 3 := .mul ⟨(-6485297888269202935/73786976294838206464:ℚ),(-204591317205558511219/2361183241434822606848:ℚ)⟩ node13 node3015
def node3017 : BoxExpr 3 := .add ⟨(30408190259149900297/73786976294838206464:ℚ),(976000303511852792205/2361183241434822606848:ℚ)⟩ node3016 node301
def node3018 : BoxExpr 3 := .mul ⟨(31895829535029566575/36893488147419103232:ℚ),(4123541850044277477961/4722366482869645213696:ℚ)⟩ node36 node3017
def node3019 : BoxExpr 3 := .mul ⟨(4848917720000326142789/4722366482869645213696:ℚ),(4916127044295514656415/4722366482869645213696:ℚ)⟩ node3018 node304
def node3020 : BoxExpr 3 := .add ⟨(-95082589406431276959/4722366482869645213696:ℚ),(-20314188680796492005/1180591620717411303424:ℚ)⟩ node3015 node306
def node3021 : BoxExpr 3 := .mul ⟨(1756554691521900587/2361183241434822606848:ℚ),(4110864852353258797/4722366482869645213696:ℚ)⟩ node3020 node308
def node3022 : BoxExpr 3 := .mul ⟨(3828618943160831343/4722366482869645213696:ℚ),(1122146484992617111/1180591620717411303424:ℚ)⟩ node3021 node37
def node3023 : BoxExpr 3 := .add ⟨(1213186584735871743533/1180591620717411303424:ℚ),(4920615630235485124859/4722366482869645213696:ℚ)⟩ node3019 node3022
def node3024 : BoxExpr 3 := .add ⟨(15567190594082873333939/4722366482869645213696:ℚ),(15762379627095275622101/4722366482869645213696:ℚ)⟩ node3023 node316
def node3025 : BoxExpr 3 := .add ⟨(10805244361121051981575/4722366482869645213696:ℚ),(2753639147624132698209/1180591620717411303424:ℚ)⟩ node3024 node323
def node3026 : BoxExpr 3 := .add ⟨(10805230194021603372639/4722366482869645213696:ℚ),(11014542423397082183901/4722366482869645213696:ℚ)⟩ node3025 node325
def node3027 : BoxExpr 3 := .mul ⟨(112180703550126969323/2361183241434822606848:ℚ),(14142209883055807529/295147905179352825856:ℚ)⟩ node3015 node3015
def node3028 : BoxExpr 3 := .neg ⟨(-14142209883055807529/295147905179352825856:ℚ),(-112180703550126969323/2361183241434822606848:ℚ)⟩ node3027
def node3029 : BoxExpr 3 := .add ⟨(281005695296297018327/295147905179352825856:ℚ),(2249002537884695637525/2361183241434822606848:ℚ)⟩ node12 node3028
def node3030 : BoxExpr 3 := .sqrt ⟨(575980007674466370449/590295810358705651712:ℚ),(4608820717883362438503/4722366482869645213696:ℚ)⟩ node3029
def node3031 : BoxExpr 3 := .mul ⟨(5703515829588568643765/2361183241434822606848:ℚ),(11426564257665721192143/4722366482869645213696:ℚ)⟩ node11 node3030
def node3032 : BoxExpr 3 := .neg ⟨(257332079828248245043/1180591620717411303424:ℚ),(516854710515249499341/2361183241434822606848:ℚ)⟩ node3015
def node3033 : BoxExpr 3 := .add ⟨(911269157241251849829/4722366482869645213696:ℚ),(228912564739689467085/1180591620717411303424:ℚ)⟩ node332 node3032
def node3034 : BoxExpr 3 := .mul ⟨(650646178270253820777/4722366482869645213696:ℚ),(653774284896553117995/4722366482869645213696:ℚ)⟩ node3033 node335
def node3035 : BoxExpr 3 := .neg ⟨(-653774284896553117995/4722366482869645213696:ℚ),(-650646178270253820777/4722366482869645213696:ℚ)⟩ node3034
def node3036 : BoxExpr 3 := .add ⟨(10753257374280584169535/4722366482869645213696:ℚ),(5387959039697733685683/2361183241434822606848:ℚ)⟩ node3031 node3035
def node3037 : BoxExpr 3 := .mul ⟨(21980808773299727237/590295810358705651712:ℚ),(177541366129161498789/4722366482869645213696:ℚ)⟩ node3033 node3033
def node3038 : BoxExpr 3 := .mul ⟨(72624592186982298791/2361183241434822606848:ℚ),(9165573026417962375/295147905179352825856:ℚ)⟩ node3037 node340
def node3039 : BoxExpr 3 := .add ⟨(10898506558654548767117/4722366482869645213696:ℚ),(5461283623909077384683/2361183241434822606848:ℚ)⟩ node3036 node3038
def node3040 : BoxExpr 3 := .neg ⟨(-5461283623909077384683/2361183241434822606848:ℚ),(-10898506558654548767117/4722366482869645213696:ℚ)⟩ node3039
def node3041 : BoxExpr 3 := .add ⟨(-117337053796551396727/4722366482869645213696:ℚ),(7252241546408338549/295147905179352825856:ℚ)⟩ node3026 node3040
def node3042 : BoxExpr 3 := .var 2
def node3043 : BoxExpr 3 := .mul ⟨(-206058234264227749561/2361183241434822606848:ℚ),(-25757279283028468695/295147905179352825856:ℚ)⟩ node51 node3042
def node3044 : BoxExpr 3 := .add ⟨(974533386453183553863/2361183241434822606848:ℚ),(121816673306647944233/295147905179352825856:ℚ)⟩ node3043 node301
def node3045 : BoxExpr 3 := .mul ⟨(4103053000995378137949/4722366482869645213696:ℚ),(1025763250248844534491/1180591620717411303424:ℚ)⟩ node68 node3044
def node3046 : BoxExpr 3 := .mul ⟨(4882374535065865314179/4722366482869645213696:ℚ),(610296816883233164275/590295810358705651712:ℚ)⟩ node3045 node349
def node3047 : BoxExpr 3 := .add ⟨(-88169672064808622491/4722366482869645213696:ℚ),(-88169672064808622489/4722366482869645213696:ℚ)⟩ node3042 node351
def node3048 : BoxExpr 3 := .mul ⟨(3811987117698529985/4722366482869645213696:ℚ),(1905993558849264993/2361183241434822606848:ℚ)⟩ node3047 node308
def node3049 : BoxExpr 3 := .mul ⟨(259892306882308057/295147905179352825856:ℚ),(2079138455058464457/2361183241434822606848:ℚ)⟩ node3048 node69
def node3050 : BoxExpr 3 := .add ⟨(4886532811975982243091/4722366482869645213696:ℚ),(2443266405987991121557/2361183241434822606848:ℚ)⟩ node3046 node3049
def node3051 : BoxExpr 3 := .add ⟨(15665535324892244194987/4722366482869645213696:ℚ),(15665535324892244195063/4722366482869645213696:ℚ)⟩ node3050 node358
def node3052 : BoxExpr 3 := .add ⟨(5455325345055980552085/2361183241434822606848:ℚ),(10910650690111961104251/4722366482869645213696:ℚ)⟩ node3051 node361
def node3053 : BoxExpr 3 := .add ⟨(5455318261506256247617/2361183241434822606848:ℚ),(2727659130753128123829/1180591620717411303424:ℚ)⟩ node3052 node325
def node3054 : BoxExpr 3 := .mul ⟨(112658683244953752043/2361183241434822606848:ℚ),(28164670811238438011/590295810358705651712:ℚ)⟩ node3042 node3042
def node3055 : BoxExpr 3 := .neg ⟨(-28164670811238438011/590295810358705651712:ℚ),(-112658683244953752043/2361183241434822606848:ℚ)⟩ node3054
def node3056 : BoxExpr 3 := .add ⟨(562131139547467213701/590295810358705651712:ℚ),(2248524558189868854805/2361183241434822606848:ℚ)⟩ node12 node3055
def node3057 : BoxExpr 3 := .sqrt ⟨(1152082734089934721853/1180591620717411303424:ℚ),(2304165468179869443707/2361183241434822606848:ℚ)⟩ node3056
def node3058 : BoxExpr 3 := .mul ⟨(713543523409069638847/295147905179352825856:ℚ),(5708348187272557110783/2361183241434822606848:ℚ)⟩ node50 node3057
def node3059 : BoxExpr 3 := .neg ⟨(1031518870171745989427/4722366482869645213696:ℚ),(257879717542936497357/1180591620717411303424:ℚ)⟩ node3042
def node3060 : BoxExpr 3 := .add ⟨(228364927025001214771/1180591620717411303424:ℚ),(456729854050002429543/2361183241434822606848:ℚ)⟩ node332 node3059
def node3061 : BoxExpr 3 := .mul ⟨(652210231583403469385/4722366482869645213696:ℚ),(163052557895850867347/1180591620717411303424:ℚ)⟩ node3060 node335
def node3062 : BoxExpr 3 := .neg ⟨(-163052557895850867347/1180591620717411303424:ℚ),(-652210231583403469385/4722366482869645213696:ℚ)⟩ node3061
def node3063 : BoxExpr 3 := .add ⟨(2691121535740427688041/1180591620717411303424:ℚ),(10764486142961710752181/4722366482869645213696:ℚ)⟩ node3058 node3062
def node3064 : BoxExpr 3 := .mul ⟨(176692902033113732873/4722366482869645213696:ℚ),(176692902033113732875/4722366482869645213696:ℚ)⟩ node3060 node3060
def node3065 : BoxExpr 3 := .mul ⟨(145948337079351943353/4722366482869645213696:ℚ),(145948337079351943355/4722366482869645213696:ℚ)⟩ node3064 node340
def node3066 : BoxExpr 3 := .add ⟨(10910434480041062695517/4722366482869645213696:ℚ),(681902155002566418471/295147905179352825856:ℚ)⟩ node3063 node3065
def node3067 : BoxExpr 3 := .neg ⟨(-681902155002566418471/295147905179352825856:ℚ),(-10910434480041062695517/4722366482869645213696:ℚ)⟩ node3066
def node3068 : BoxExpr 3 := .add ⟨(101021485724899849/2361183241434822606848:ℚ),(202042971449799799/4722366482869645213696:ℚ)⟩ node3053 node3067
def node3069 : BoxExpr 3 := .mul ⟨(1105209420008032056895/4722366482869645213696:ℚ),(1105209420008032056901/4722366482869645213696:ℚ)⟩ node78 node3044
def node3070 : BoxExpr 3 := .mul ⟨(657564784911757044493/2361183241434822606848:ℚ),(1315129569823514088995/4722366482869645213696:ℚ)⟩ node3069 node349
def node3071 : BoxExpr 3 := .add ⟨(5194360907104885076579/4722366482869645213696:ℚ),(324647556694055317313/295147905179352825856:ℚ)⟩ node3070 node385
def node3072 : BoxExpr 3 := .add ⟨(2840494846592131227817/4722366482869645213696:ℚ),(355061855824016403531/590295810358705651712:ℚ)⟩ node3071 node387
def node3073 : BoxExpr 3 := .mul ⟨(2850516123213001017315/4722366482869645213696:ℚ),(712629030803250254331/1180591620717411303424:ℚ)⟩ node77 node3057
def node3074 : BoxExpr 3 := .neg ⟨(-712629030803250254331/1180591620717411303424:ℚ),(-2850516123213001017315/4722366482869645213696:ℚ)⟩ node3073
def node3075 : BoxExpr 3 := .add ⟨(-10021276620869789507/4722366482869645213696:ℚ),(-10021276620869789067/4722366482869645213696:ℚ)⟩ node3072 node3074
def node3076 : BoxExpr 3 := .mul ⟨(-1858909859291447673305/4722366482869645213696:ℚ),(-929454929645723836647/2361183241434822606848:ℚ)⟩ node98 node3044
def node3077 : BoxExpr 3 := .mul ⟨(-542872190767789950269/1180591620717411303424:ℚ),(-2171488763071159801067/4722366482869645213696:ℚ)⟩ node68 node3042
def node3078 : BoxExpr 3 := .add ⟨(-4030398622362607474381/4722366482869645213696:ℚ),(-4030398622362607474361/4722366482869645213696:ℚ)⟩ node3076 node3077
def node3079 : BoxExpr 3 := .mul ⟨(-4795920402493944246071/4722366482869645213696:ℚ),(-1198980100623486061511/1180591620717411303424:ℚ)⟩ node3078 node349
def node3080 : BoxExpr 3 := .mul ⟨(2321121365030885547429/2361183241434822606848:ℚ),(4642242730061771094883/4722366482869645213696:ℚ)⟩ node3045 node399
def node3081 : BoxExpr 3 := .add ⟨(-153677672432173151213/4722366482869645213696:ℚ),(-153677672432173151161/4722366482869645213696:ℚ)⟩ node3079 node3080
def node3082 : BoxExpr 3 := .mul ⟨(1976879345995690031/4722366482869645213696:ℚ),(123554959124730627/295147905179352825856:ℚ)⟩ node3048 node103
def node3083 : BoxExpr 3 := .add ⟨(-54690874559885256751/2361183241434822606848:ℚ),(-109381749119770513499/4722366482869645213696:ℚ)⟩ node403 node3082
def node3084 : BoxExpr 3 := .add ⟨(-263059421551943664715/4722366482869645213696:ℚ),(-65764855387985916165/1180591620717411303424:ℚ)⟩ node3081 node3083
def node3085 : BoxExpr 3 := .add ⟨(58857813072725165559/4722366482869645213696:ℚ),(29428906536362582865/2361183241434822606848:ℚ)⟩ node3084 node409
def node3086 : BoxExpr 3 := .add ⟨(-257879717542936497357/590295810358705651712:ℚ),(-1031518870171745989427/2361183241434822606848:ℚ)⟩ node3042 node3042
def node3087 : BoxExpr 3 := .neg ⟨(1031518870171745989427/2361183241434822606848:ℚ),(257879717542936497357/590295810358705651712:ℚ)⟩ node3086
def node3088 : BoxExpr 3 := .mul ⟨(1152082734089934721853/590295810358705651712:ℚ),(2304165468179869443707/1180591620717411303424:ℚ)⟩ node86 node3057
def node3089 : BoxExpr 3 := .inv ⟨(151225746822033397313/295147905179352825856:ℚ),(1209805974576267178505/2361183241434822606848:ℚ)⟩ node3088
def node3090 : BoxExpr 3 := .mul ⟨(1057044341263072504499/4722366482869645213696:ℚ),(528522170631536252251/2361183241434822606848:ℚ)⟩ node3087 node3089
def node3091 : BoxExpr 3 := .mul ⟨(81835175693813624747/147573952589676412928:ℚ),(1309362811101017995957/2361183241434822606848:ℚ)⟩ node50 node3090
def node3092 : BoxExpr 3 := .add ⟨(2995247645485481337241/2361183241434822606848:ℚ),(5990495290970962674493/4722366482869645213696:ℚ)⟩ node3091 node335
def node3093 : BoxExpr 3 := .mul ⟨(-456729854050002429543/2361183241434822606848:ℚ),(-228364927025001214771/1180591620717411303424:ℚ)⟩ node422 node3060
def node3094 : BoxExpr 3 := .mul ⟨(-456729854050002429543/2361183241434822606848:ℚ),(-228364927025001214771/1180591620717411303424:ℚ)⟩ node3060 node422
def node3095 : BoxExpr 3 := .add ⟨(-456729854050002429543/1180591620717411303424:ℚ),(-228364927025001214771/590295810358705651712:ℚ)⟩ node3093 node3094
def node3096 : BoxExpr 3 := .mul ⟨(-1509035437781208027211/4722366482869645213696:ℚ),(-754517718890604013603/2361183241434822606848:ℚ)⟩ node3095 node340
def node3097 : BoxExpr 3 := .add ⟨(4481459853189754647271/4722366482869645213696:ℚ),(4481459853189754647287/4722366482869645213696:ℚ)⟩ node3092 node3096
def node3098 : BoxExpr 3 := .neg ⟨(-4481459853189754647287/4722366482869645213696:ℚ),(-4481459853189754647271/4722366482869645213696:ℚ)⟩ node3097
def node3099 : BoxExpr 3 := .add ⟨(2745731086234970789/590295810358705651712:ℚ),(21965848689879766347/4722366482869645213696:ℚ)⟩ node414 node3098
def node3100 : BoxExpr 3 := .mul ⟨(2192296617885127011123/1180591620717411303424:ℚ),(2203101915484501713371/1180591620717411303424:ℚ)⟩ node112 node3017
def node3101 : BoxExpr 3 := .mul ⟨(2603755841899451969419/1180591620717411303424:ℚ),(2626559715390377983349/1180591620717411303424:ℚ)⟩ node3100 node304
def node3102 : BoxExpr 3 := .add ⟨(21741234286460592040399/4722366482869645213696:ℚ),(44832588474222330347677/4722366482869645213696:ℚ)⟩ node3101 node448
def node3103 : BoxExpr 3 := .mul ⟨(2833821637758374542609/590295810358705651712:ℚ),(5668849482996535799359/1180591620717411303424:ℚ)⟩ node111 node3030
def node3104 : BoxExpr 3 := .neg ⟨(-5668849482996535799359/1180591620717411303424:ℚ),(-2833821637758374542609/590295810358705651712:ℚ)⟩ node3103
def node3105 : BoxExpr 3 := .add ⟨(-934163645525551157037/4722366482869645213696:ℚ),(22162015372155334006805/4722366482869645213696:ℚ)⟩ node3102 node3104
def node3106 : BoxExpr 3 := .mul ⟨(-541987140480806097387/4722366482869645213696:ℚ),(-509067489302318261455/4722366482869645213696:ℚ)⟩ node131 node3017
def node3107 : BoxExpr 3 := .mul ⟨(-75089510843887497427/590295810358705651712:ℚ),(-284602460523424781075/2361183241434822606848:ℚ)⟩ node118 node3015
def node3108 : BoxExpr 3 := .add ⟨(-1142703227231906076803/4722366482869645213696:ℚ),(-1078272410349167823605/4722366482869645213696:ℚ)⟩ node3106 node3107
def node3109 : BoxExpr 3 := .mul ⟨(-340585499267954271379/1180591620717411303424:ℚ),(-640323500182665647365/2361183241434822606848:ℚ)⟩ node3108 node304
def node3110 : BoxExpr 3 := .mul ⟨(1076180881742485965577/4722366482869645213696:ℚ),(1134359561914503740267/4722366482869645213696:ℚ)⟩ node118 node3017
def node3111 : BoxExpr 3 := .mul ⟨(1206925401943470102431/4722366482869645213696:ℚ),(1294784651719761159601/4722366482869645213696:ℚ)⟩ node3110 node461
def node3112 : BoxExpr 3 := .add ⟨(-155416595128346983085/4722366482869645213696:ℚ),(14137651354429864871/4722366482869645213696:ℚ)⟩ node3109 node3111
def node3113 : BoxExpr 3 := .add ⟨(-728179330005704456261/1180591620717411303424:ℚ),(1427711531926089637775/4722366482869645213696:ℚ)⟩ node3112 node476
def node3114 : BoxExpr 3 := .add ⟨(-516854710515249499341/1180591620717411303424:ℚ),(-257332079828248245043/590295810358705651712:ℚ)⟩ node3015 node3015
def node3115 : BoxExpr 3 := .neg ⟨(257332079828248245043/590295810358705651712:ℚ),(516854710515249499341/1180591620717411303424:ℚ)⟩ node3114
def node3116 : BoxExpr 3 := .mul ⟨(575980007674466370449/295147905179352825856:ℚ),(4608820717883362438503/2361183241434822606848:ℚ)⟩ node86 node3030
def node3117 : BoxExpr 3 := .inv ⟨(37802418997876427109/73786976294838206464:ℚ),(2419869711338857644029/4722366482869645213696:ℚ)⟩ node3116
def node3118 : BoxExpr 3 := .mul ⟨(263671872510188079085/1180591620717411303424:ℚ),(529700972457622012607/2361183241434822606848:ℚ)⟩ node3115 node3117
def node3119 : BoxExpr 3 := .mul ⟨(636817317325619917895/4722366482869645213696:ℚ),(10483397456737208155/73786976294838206464:ℚ)⟩ node117 node3118
def node3120 : BoxExpr 3 := .neg ⟨(-10483397456737208155/73786976294838206464:ℚ),(-636817317325619917895/4722366482869645213696:ℚ)⟩ node3119
def node3121 : BoxExpr 3 := .add ⟨(561993154875182654027/4722366482869645213696:ℚ),(676877829403640783831/4722366482869645213696:ℚ)⟩ node479 node3120
def node3122 : BoxExpr 3 := .add ⟨(-2912717320022817825043/4722366482869645213696:ℚ),(1427711531926089637775/4722366482869645213696:ℚ)⟩ node3112 node492
def node3123 : BoxExpr 3 := .mul ⟨(-501378948075619762447/1180591620717411303424:ℚ),(-977199561267622758667/2361183241434822606848:ℚ)⟩ node175 node3017
def node3124 : BoxExpr 3 := .mul ⟨(484878924616736998827/2361183241434822606848:ℚ),(249487712848845961945/1180591620717411303424:ℚ)⟩ node148 node3015
def node3125 : BoxExpr 3 := .add ⟨(-517878971534502526067/2361183241434822606848:ℚ),(-478224135569930834777/2361183241434822606848:ℚ)⟩ node3123 node3124
def node3126 : BoxExpr 3 := .add ⟨(-4125005864720690905/295147905179352825856:ℚ),(20751290127761089113/2361183241434822606848:ℚ)⟩ node3125 node3124
def node3127 : BoxExpr 3 := .mul ⟨(-78685959311268269111/4722366482869645213696:ℚ),(49479783308135163331/4722366482869645213696:ℚ)⟩ node3126 node304
def node3128 : BoxExpr 3 := .mul ⟨(-1884476070423797020633/4722366482869645213696:ℚ),(-1833495844247766679169/4722366482869645213696:ℚ)⟩ node148 node3017
def node3129 : BoxExpr 3 := .mul ⟨(-1091839839359367932463/2361183241434822606848:ℚ),(-2159370901627839683231/4722366482869645213696:ℚ)⟩ node36 node3015
def node3130 : BoxExpr 3 := .add ⟨(-4068155749142532885559/4722366482869645213696:ℚ),(-124777085808612698825/147573952589676412928:ℚ)⟩ node3128 node3129
def node3131 : BoxExpr 3 := .mul ⟨(-4643488538947282566405/4722366482869645213696:ℚ),(-2238978773888760001633/2361183241434822606848:ℚ)⟩ node3130 node461
def node3132 : BoxExpr 3 := .add ⟨(-1180543624564637708879/1180591620717411303424:ℚ),(-4428477764469384839935/4722366482869645213696:ℚ)⟩ node3127 node3131
def node3133 : BoxExpr 3 := .mul ⟨(2516512034232242502259/590295810358705651712:ℚ),(5192217457070470537795/1180591620717411303424:ℚ)⟩ node3018 node514
def node3134 : BoxExpr 3 := .add ⟨(15488607734910657451667/4722366482869645213696:ℚ),(8145456140252181073957/2361183241434822606848:ℚ)⟩ node3131 node3133
def node3135 : BoxExpr 3 := .add ⟨(10766433236652106616151/4722366482869645213696:ℚ),(11862434516034977307979/4722366482869645213696:ℚ)⟩ node3132 node3134
def node3136 : BoxExpr 3 := .mul ⟨(7104252824020960817/4722366482869645213696:ℚ),(1055123728410846365/590295810358705651712:ℚ)⟩ node3021 node189
def node3137 : BoxExpr 3 := .add ⟨(-46254092855079639687/4722366482869645213696:ℚ),(-22042641122172007507/2361183241434822606848:ℚ)⟩ node518 node3136
def node3138 : BoxExpr 3 := .add ⟨(-99612438534180240191/4722366482869645213696:ℚ),(-24152888578993700237/1180591620717411303424:ℚ)⟩ node518 node3137
def node3139 : BoxExpr 3 := .add ⟨(1333352599764740796995/590295810358705651712:ℚ),(11765822961719002507031/4722366482869645213696:ℚ)⟩ node3135 node3138
def node3140 : BoxExpr 3 := .add ⟨(21770554076484497747483/4722366482869645213696:ℚ),(14179647000523224490787/2361183241434822606848:ℚ)⟩ node3139 node527
def node3141 : BoxExpr 3 := .mul ⟨(-2419869711338857644029/2361183241434822606848:ℚ),(-37802418997876427109/36893488147419103232:ℚ)⟩ node6 node3117
def node3142 : BoxExpr 3 := .mul ⟨(263671872510188079085/590295810358705651712:ℚ),(529700972457622012607/1180591620717411303424:ℚ)⟩ node86 node3118
def node3143 : BoxExpr 3 := .mul ⟨(4496091124740752293231/1180591620717411303424:ℚ),(8996010151538782550101/2361183241434822606848:ℚ)⟩ node3116 node3116
def node3144 : BoxExpr 3 := .inv ⟨(619739885317827355303/2361183241434822606848:ℚ),(1240007407535389946565/4722366482869645213696:ℚ)⟩ node3143
def node3145 : BoxExpr 3 := .mul ⟨(553647758169594547559/4722366482869645213696:ℚ),(278179650820752231333/2361183241434822606848:ℚ)⟩ node3142 node3144
def node3146 : BoxExpr 3 := .neg ⟨(-278179650820752231333/2361183241434822606848:ℚ),(-553647758169594547559/4722366482869645213696:ℚ)⟩ node3145
def node3147 : BoxExpr 3 := .mul ⟨(-15223136897331936683/295147905179352825856:ℚ),(-60338954894264405769/1180591620717411303424:ℚ)⟩ node3115 node3146
def node3148 : BoxExpr 3 := .add ⟨(-2541654806517513137493/2361183241434822606848:ℚ),(-1270016362826310073257/1180591620717411303424:ℚ)⟩ node3141 node3147
def node3149 : BoxExpr 3 := .mul ⟨(-6301477914900374900423/2361183241434822606848:ℚ),(-1572007346761566884733/590295810358705651712:ℚ)⟩ node11 node3148
def node3150 : BoxExpr 3 := .add ⟨(-4801606400100095907821/4722366482869645213696:ℚ),(-2387354672195940592419/2361183241434822606848:ℚ)⟩ node3149 node546
def node3151 : BoxExpr 3 := .neg ⟨(2387354672195940592419/2361183241434822606848:ℚ),(4801606400100095907821/4722366482869645213696:ℚ)⟩ node3150
def cert_iv19 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-8947/40960:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/40960:ℚ)],
    whole := node3041, centerValue := node3068, gradient := ![node3075, node3085, node3099],
    hessian := ![![node3105, node3113, node3121], ![node3122, node3140, node536], ![node3121, node536, node3151]] }

end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part5
end

section
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646CheckB4Part5
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part5

theorem cert_iv16_check : cert_iv16.check = true := by decide +kernel

theorem cert_iv16_lower_pos : 0 < cert_iv16.lower := by decide +kernel

theorem positive_iv16 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(227/1024:ℝ)) ≤ r) (hrhi : r ≤ (-(4521/20480:ℝ))) :
    0 < node2630.eval ![A,ρ,r] := by
  apply cert_iv16.positive_sound cert_iv16_check cert_iv16_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv16,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv16,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv16,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv17_check : cert_iv17.check = true := by decide +kernel

theorem cert_iv17_lower_pos : 0 < cert_iv17.lower := by decide +kernel

theorem positive_iv17 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(4521/20480:ℝ)) ≤ r) (hrhi : r ≤ (-(2251/10240:ℝ))) :
    0 < node2767.eval ![A,ρ,r] := by
  apply cert_iv17.positive_sound cert_iv17_check cert_iv17_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv17,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv17,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv17,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv18_check : cert_iv18.check = true := by decide +kernel

theorem cert_iv18_lower_pos : 0 < cert_iv18.lower := by decide +kernel

theorem positive_iv18 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(2251/10240:ℝ)) ≤ r) (hrhi : r ≤ (-(4483/20480:ℝ))) :
    0 < node2904.eval ![A,ρ,r] := by
  apply cert_iv18.positive_sound cert_iv18_check cert_iv18_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv18,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv18,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv18,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv19_check : cert_iv19.check = true := by decide +kernel

theorem cert_iv19_lower_pos : 0 < cert_iv19.lower := by decide +kernel

theorem positive_iv19 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(4483/20480:ℝ)) ≤ r) (hrhi : r ≤ (-(279/1280:ℝ))) :
    0 < node3041.eval ![A,ρ,r] := by
  apply cert_iv19.positive_sound cert_iv19_check cert_iv19_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv19,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv19,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv19,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part5
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
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646BoundB4Part5
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part5
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate.CapacityCore
noncomputable section
namespace Parameters
def b : ℚ := (103531361122339324647880530522418473224550678173/6474633415922124204664207433178390079472570088576:ℚ)
def c : ℚ := (148022665013912365111/4722366482869645213696:ℚ)
def theta : ℚ := (105113898053531722649817636563532003778556764000751/182628568201966125342452015454275643968150995402752:ℚ)
end Parameters

theorem iv_shape16 : SplitDataB4Part5.node2630.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound16 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(227/1024:ℝ)) ≤ r) (hrhi : r ≤ (-(4521/20480:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part5.node2630 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape16 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part5.positive_iv16 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part5.node2630.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape17 : SplitDataB4Part5.node2767.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound17 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(4521/20480:ℝ)) ≤ r) (hrhi : r ≤ (-(2251/10240:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part5.node2767 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape17 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part5.positive_iv17 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part5.node2767.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape18 : SplitDataB4Part5.node2904.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound18 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(2251/10240:ℝ)) ≤ r) (hrhi : r ≤ (-(4483/20480:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part5.node2904 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape18 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part5.positive_iv18 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part5.node2904.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape19 : SplitDataB4Part5.node3041.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound19 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(4483/20480:ℝ)) ≤ r) (hrhi : r ≤ (-(279/1280:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part5.node3041 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape19 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part5.positive_iv19 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part5.node3041.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem actual_bound (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (r : ℝ)
    (hrlo : (-(227/1024:ℝ)) ≤ r) (hrhi : r ≤ (-(279/1280:ℝ))) : fA A r+3/10^6 ≤ l40Lhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) r := by
  have hc : 0 ≤ (Parameters.c:ℝ) := by norm_num [Parameters.c]
  have hθ : 0 ≤ (Parameters.theta:ℝ) := by norm_num [Parameters.theta]
  by_cases h0 : r ≤ (-(4521/20480:ℝ))
  · have h := iv_bound16 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  by_cases h1 : r ≤ (-(2251/10240:ℝ))
  · have h := iv_bound17 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  by_cases h2 : r ≤ (-(4483/20480:ℝ))
  · have h := iv_bound18 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  have h := iv_bound19 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
  exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
    (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
end
end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part5
end

section
-- Source module: Solutions.Sol_GaussLocalMaxCase1FamilyAdaptive0Seed25646B4Part5
set_option autoImplicit false
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate
open GaussLocalMaxColoring.Certificate.CapacityCore
theorem solution (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (r : ℝ)
    (hrlo : (-(227/1024:ℝ)) ≤ r) (hrhi : r ≤ (-(279/1280:ℝ))) :
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
  have h := GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part5.actual_bound A ρ hAlo hAhi hρlo hρhi r hrlo hrhi
  simpa only [Case2Static,constructedA,constructedMu,constructedMass,constructedKappa,thresholdCapacity,
    GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part5.Parameters.b,GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part5.Parameters.c,GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part5.Parameters.theta,
    show ¬ (4:ℕ)=1 by decide,show ¬ (4:ℕ)=2 by decide,show ¬ (4:ℕ)=3 by decide,ite_false,and_assoc] using h
end

#print axioms solution
