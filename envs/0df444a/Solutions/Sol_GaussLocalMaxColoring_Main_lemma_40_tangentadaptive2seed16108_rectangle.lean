-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_40_tangentadaptive2seed16108_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T14:52:18.482111+00:00
-- url     : https://prove2.me/submissions/5593f405-2a14-4b56-8960-d253c921ad9a

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Section5
import Definitions.Def_GaussLocalMaxColoring_Main_Bands

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
-- Source module: Solutions.GaussLocalMaxCase1FamilyTangentAdaptive2Seed16108Cells
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellTangentAdaptive2Seed16108.Data

def node0 : BoxExpr 3 := .lit (1769451672197/307399000000:ℚ)
def node1 : BoxExpr 3 := .var 0
def node2 : BoxExpr 3 := .lit (13/25:ℚ)
def node3 : BoxExpr 3 := .mul ⟨(1236990533198208360817/1180591620717411303424:ℚ),(2481347958109693368169/2361183241434822606848:ℚ)⟩ node1 node2
def node4 : BoxExpr 3 := .lit (713/500:ℚ)
def node5 : BoxExpr 3 := .add ⟨(5841028368682473758999/2361183241434822606848:ℚ),(11696790520791500811069/4722366482869645213696:ℚ)⟩ node3 node4
def node6 : BoxExpr 3 := .lit (-2/1:ℚ)
def node7 : BoxExpr 3 := .add ⟨(70578828093081578897/4722366482869645213696:ℚ),(24728256747574862545/1180591620717411303424:ℚ)⟩ node1 node6
def node8 : BoxExpr 3 := .mul ⟨(1054846334578786601/4722366482869645213696:ℚ),(2071797465079072777/4722366482869645213696:ℚ)⟩ node7 node7
def node9 : BoxExpr 3 := .lit (123/50:ℚ)
def node10 : BoxExpr 3 := .mul ⟨(1297460991531907519/2361183241434822606848:ℚ),(637077720511814879/590295810358705651712:ℚ)⟩ node8 node9
def node11 : BoxExpr 3 := .add ⟨(2921162914837002833259/1180591620717411303424:ℚ),(11701887142555595330101/4722366482869645213696:ℚ)⟩ node5 node10
def node12 : BoxExpr 3 := .lit (1/1:ℚ)
def node13 : BoxExpr 3 := .var 1
def node14 : BoxExpr 3 := .mul ⟨(736796300834405118203/4722366482869645213696:ℚ),(375897213051767334573/2361183241434822606848:ℚ)⟩ node13 node13
def node15 : BoxExpr 3 := .neg ⟨(-375897213051767334573/2361183241434822606848:ℚ),(-736796300834405118203/4722366482869645213696:ℚ)⟩ node14
def node16 : BoxExpr 3 := .add ⟨(1985286028383055272275/2361183241434822606848:ℚ),(3985570182035240095493/4722366482869645213696:ℚ)⟩ node12 node15
def node17 : BoxExpr 3 := .sqrt ⟨(1082546084431601424869/1180591620717411303424:ℚ),(2169177438729246072879/2361183241434822606848:ℚ)⟩ node16
def node18 : BoxExpr 3 := .mul ⟨(2678566762588037783381/1180591620717411303424:ℚ),(10750317525023023490121/4722366482869645213696:ℚ)⟩ node11 node17
def node19 : BoxExpr 3 := .lit (-1/50:ℚ)
def node20 : BoxExpr 3 := .add ⟨(442718399004515418243/1180591620717411303424:ℚ),(447440765487385063457/1180591620717411303424:ℚ)⟩ node13 node19
def node21 : BoxExpr 3 := .lit (-4/5:ℚ)
def node22 : BoxExpr 3 := .mul ⟨(-1431810449559632203063/4722366482869645213696:ℚ),(-1416698876814449338377/4722366482869645213696:ℚ)⟩ node20 node21
def node23 : BoxExpr 3 := .mul ⟨(664072410400534793199/4722366482869645213696:ℚ),(169578739258101300227/1180591620717411303424:ℚ)⟩ node20 node20
def node24 : BoxExpr 3 := .lit (9/20:ℚ)
def node25 : BoxExpr 3 := .mul ⟨(298832584680240656939/4722366482869645213696:ℚ),(305241730664582340409/4722366482869645213696:ℚ)⟩ node23 node24
def node26 : BoxExpr 3 := .add ⟨(-283244466219847886531/1180591620717411303424:ℚ),(-69466071634366687373/295147905179352825856:ℚ)⟩ node22 node25
def node27 : BoxExpr 3 := .add ⟨(1197661148184094948425/590295810358705651712:ℚ),(9638860378873156492153/4722366482869645213696:ℚ)⟩ node18 node26
def node28 : BoxExpr 3 := .lit (-1/4:ℚ)
def node29 : BoxExpr 3 := .add ⟨(342364652479021636911/2361183241434822606848:ℚ),(703618770889521854677/4722366482869645213696:ℚ)⟩ node13 node28
def node30 : BoxExpr 3 := .lit (39/100:ℚ)
def node31 : BoxExpr 3 := .mul ⟨(133522214466818438395/2361183241434822606848:ℚ),(274411320646913523325/4722366482869645213696:ℚ)⟩ node29 node30
def node32 : BoxExpr 3 := .mul ⟨(24820935794007663859/1180591620717411303424:ℚ),(104837135479420915951/4722366482869645213696:ℚ)⟩ node29 node29
def node33 : BoxExpr 3 := .lit (13/20:ℚ)
def node34 : BoxExpr 3 := .mul ⟨(64534433064419926033/4722366482869645213696:ℚ),(68144138061623595369/4722366482869645213696:ℚ)⟩ node32 node33
def node35 : BoxExpr 3 := .add ⟨(331578861998056802823/4722366482869645213696:ℚ),(171277729354268559347/2361183241434822606848:ℚ)⟩ node31 node34
def node36 : BoxExpr 3 := .add ⟨(9912868047470816390223/4722366482869645213696:ℚ),(9981415837581693610847/4722366482869645213696:ℚ)⟩ node27 node35
def node37 : BoxExpr 3 := .inv ⟨(642546132936308782619/590295810358705651712:ℚ),(5150068324860227343635/4722366482869645213696:ℚ)⟩ node17
def node38 : BoxExpr 3 := .mul ⟨(10790310414603358846075/4722366482869645213696:ℚ),(5442713280392247705221/2361183241434822606848:ℚ)⟩ node36 node37
def node39 : BoxExpr 3 := .mul ⟨(24655180673895112152133/4722366482869645213696:ℚ),(12545882645921637977337/2361183241434822606848:ℚ)⟩ node38 node38
def node40 : BoxExpr 3 := .neg ⟨(-12545882645921637977337/2361183241434822606848:ℚ),(-24655180673895112152133/4722366482869645213696:ℚ)⟩ node39
def node41 : BoxExpr 3 := .add ⟨(1045572221922368149141/2361183241434822606848:ℚ),(315966132724112512603/590295810358705651712:ℚ)⟩ node0 node40
def node42 : BoxExpr 3 := .lit (1/1000000000000000000:ℚ)
def node43 : BoxExpr 3 := .add ⟨(522786110961184075751/1180591620717411303424:ℚ),(2527729061792900105547/4722366482869645213696:ℚ)⟩ node41 node42
def node44 : BoxExpr 3 := .var 0
def node45 : BoxExpr 3 := .mul ⟨(4955329024506110089801/4722366482869645213696:ℚ),(4955329024506110089805/4722366482869645213696:ℚ)⟩ node44 node2
def node46 : BoxExpr 3 := .add ⟨(11689423629078224164531/4722366482869645213696:ℚ),(1461177953634778020567/590295810358705651712:ℚ)⟩ node45 node4
def node47 : BoxExpr 3 := .add ⟨(42372963770845257269/2361183241434822606848:ℚ),(84745927541690514539/4722366482869645213696:ℚ)⟩ node44 node6
def node48 : BoxExpr 3 := .mul ⟨(760410300741551441/2361183241434822606848:ℚ),(1520820601483102883/4722366482869645213696:ℚ)⟩ node47 node47
def node49 : BoxExpr 3 := .mul ⟨(3741218679648433089/4722366482869645213696:ℚ),(3741218679648433093/4722366482869645213696:ℚ)⟩ node48 node9
def node50 : BoxExpr 3 := .add ⟨(2923291211939468149405/1180591620717411303424:ℚ),(11693164847757872597629/4722366482869645213696:ℚ)⟩ node46 node49
def node51 : BoxExpr 3 := .var 1
def node52 : BoxExpr 3 := .mul ⟨(744276474003038415093/4722366482869645213696:ℚ),(744276474003038415095/4722366482869645213696:ℚ)⟩ node51 node51
def node53 : BoxExpr 3 := .neg ⟨(-744276474003038415095/4722366482869645213696:ℚ),(-744276474003038415093/4722366482869645213696:ℚ)⟩ node52
def node54 : BoxExpr 3 := .add ⟨(3978090008866606798601/4722366482869645213696:ℚ),(3978090008866606798603/4722366482869645213696:ℚ)⟩ node12 node53
def node55 : BoxExpr 3 := .sqrt ⟨(2167140911645472218037/2361183241434822606848:ℚ),(1083570455822736109019/1180591620717411303424:ℚ)⟩ node54
def node56 : BoxExpr 3 := .mul ⟨(10732219119424189528207/4722366482869645213696:ℚ),(10732219119424189528221/4722366482869645213696:ℚ)⟩ node50 node55
def node57 : BoxExpr 3 := .add ⟨(1780318328983800963399/4722366482869645213696:ℚ),(1780318328983800963401/4722366482869645213696:ℚ)⟩ node51 node19
def node58 : BoxExpr 3 := .mul ⟨(-1424254663187040770721/4722366482869645213696:ℚ),(-712127331593520385359/2361183241434822606848:ℚ)⟩ node57 node21
def node59 : BoxExpr 3 := .mul ⟨(671174794250538518471/4722366482869645213696:ℚ),(335587397125269259237/2361183241434822606848:ℚ)⟩ node57 node57
def node60 : BoxExpr 3 := .mul ⟨(302028657412742333311/4722366482869645213696:ℚ),(151014328706371166657/2361183241434822606848:ℚ)⟩ node59 node24
def node61 : BoxExpr 3 := .add ⟨(-561113002887149218705/2361183241434822606848:ℚ),(-280556501443574609351/1180591620717411303424:ℚ)⟩ node58 node60
def node62 : BoxExpr 3 := .add ⟨(9609993113649891090797/4722366482869645213696:ℚ),(9609993113649891090817/4722366482869645213696:ℚ)⟩ node56 node61
def node63 : BoxExpr 3 := .add ⟨(694174037923782564249/4722366482869645213696:ℚ),(347087018961891282125/2361183241434822606848:ℚ)⟩ node51 node28
def node64 : BoxExpr 3 := .mul ⟨(270727874790275200057/4722366482869645213696:ℚ),(135363937395137600029/2361183241434822606848:ℚ)⟩ node63 node30
def node65 : BoxExpr 3 := .mul ⟨(12755193732724288389/590295810358705651712:ℚ),(51020774930897153557/2361183241434822606848:ℚ)⟩ node63 node63
def node66 : BoxExpr 3 := .mul ⟨(33163503705083149811/2361183241434822606848:ℚ),(66327007410166299625/4722366482869645213696:ℚ)⟩ node65 node33
def node67 : BoxExpr 3 := .add ⟨(337054882200441499679/4722366482869645213696:ℚ),(337054882200441499683/4722366482869645213696:ℚ)⟩ node64 node66
def node68 : BoxExpr 3 := .add ⟨(2486761998962583147619/1180591620717411303424:ℚ),(2486761998962583147625/1180591620717411303424:ℚ)⟩ node62 node67
def node69 : BoxExpr 3 := .inv ⟨(5145199621929073609073/4722366482869645213696:ℚ),(1286299905482268402269/1180591620717411303424:ℚ)⟩ node55
def node70 : BoxExpr 3 := .mul ⟨(2709422689514513980869/1180591620717411303424:ℚ),(10837690758058055923509/4722366482869645213696:ℚ)⟩ node68 node69
def node71 : BoxExpr 3 := .mul ⟨(12436089129609723932189/2361183241434822606848:ℚ),(12436089129609723932265/2361183241434822606848:ℚ)⟩ node70 node70
def node72 : BoxExpr 3 := .neg ⟨(-12436089129609723932265/2361183241434822606848:ℚ),(-12436089129609723932189/2361183241434822606848:ℚ)⟩ node71
def node73 : BoxExpr 3 := .add ⟨(1155365738234282194213/2361183241434822606848:ℚ),(2310731476468564388579/4722366482869645213696:ℚ)⟩ node0 node72
def node74 : BoxExpr 3 := .add ⟨(577682869117141098287/1180591620717411303424:ℚ),(1155365738234282196651/2361183241434822606848:ℚ)⟩ node73 node42
def node75 : BoxExpr 3 := .add ⟨(42372963770845257269/1180591620717411303424:ℚ),(84745927541690514539/2361183241434822606848:ℚ)⟩ node47 node47
def node76 : BoxExpr 3 := .mul ⟨(208474981752558665763/2361183241434822606848:ℚ),(104237490876279332883/1180591620717411303424:ℚ)⟩ node75 node9
def node77 : BoxExpr 3 := .add ⟨(2872580534597332842647/4722366482869645213696:ℚ),(1436290267298666421327/2361183241434822606848:ℚ)⟩ node2 node76
def node78 : BoxExpr 3 := .mul ⟨(2636511512227816559879/4722366482869645213696:ℚ),(2636511512227816559887/4722366482869645213696:ℚ)⟩ node77 node55
def node79 : BoxExpr 3 := .mul ⟨(2872580534597332842645/4722366482869645213696:ℚ),(89768141706166651333/147573952589676412928:ℚ)⟩ node78 node69
def node80 : BoxExpr 3 := .mul ⟨(6592486971207047241407/4722366482869645213696:ℚ),(3296243485603523620727/2361183241434822606848:ℚ)⟩ node79 node70
def node81 : BoxExpr 3 := .mul ⟨(6592486971207047241407/4722366482869645213696:ℚ),(3296243485603523620727/2361183241434822606848:ℚ)⟩ node70 node79
def node82 : BoxExpr 3 := .add ⟨(6592486971207047241407/2361183241434822606848:ℚ),(3296243485603523620727/1180591620717411303424:ℚ)⟩ node80 node81
def node83 : BoxExpr 3 := .neg ⟨(-3296243485603523620727/1180591620717411303424:ℚ),(-6592486971207047241407/2361183241434822606848:ℚ)⟩ node82
def node84 : BoxExpr 3 := .add ⟨(1874765658641193867673/2361183241434822606848:ℚ),(937382829320596933837/1180591620717411303424:ℚ)⟩ node51 node51
def node85 : BoxExpr 3 := .neg ⟨(-937382829320596933837/1180591620717411303424:ℚ),(-1874765658641193867673/2361183241434822606848:ℚ)⟩ node84
def node86 : BoxExpr 3 := .lit (2/1:ℚ)
def node87 : BoxExpr 3 := .mul ⟨(2167140911645472218037/1180591620717411303424:ℚ),(1083570455822736109019/590295810358705651712:ℚ)⟩ node86 node55
def node88 : BoxExpr 3 := .inv ⟨(321574976370567100567/590295810358705651712:ℚ),(1286299905482268402269/2361183241434822606848:ℚ)⟩ node87
def node89 : BoxExpr 3 := .mul ⟨(-2042629176078824852471/4722366482869645213696:ℚ),(-510657294019706213117/1180591620717411303424:ℚ)⟩ node85 node88
def node90 : BoxExpr 3 := .mul ⟨(-5057803066613212192657/4722366482869645213696:ℚ),(-5057803066613212192645/4722366482869645213696:ℚ)⟩ node50 node89
def node91 : BoxExpr 3 := .add ⟨(1780318328983800963399/2361183241434822606848:ℚ),(1780318328983800963401/2361183241434822606848:ℚ)⟩ node57 node57
def node92 : BoxExpr 3 := .mul ⟨(801143248042710433529/2361183241434822606848:ℚ),(801143248042710433531/2361183241434822606848:ℚ)⟩ node91 node24
def node93 : BoxExpr 3 := .add ⟨(-2175606690210295303899/4722366482869645213696:ℚ),(-1087803345105147651947/2361183241434822606848:ℚ)⟩ node21 node92
def node94 : BoxExpr 3 := .add ⟨(-1808352439205876874139/1180591620717411303424:ℚ),(-7233409756823507496539/4722366482869645213696:ℚ)⟩ node90 node93
def node95 : BoxExpr 3 := .add ⟨(694174037923782564249/2361183241434822606848:ℚ),(347087018961891282125/1180591620717411303424:ℚ)⟩ node63 node63
def node96 : BoxExpr 3 := .mul ⟨(902426249300917333523/4722366482869645213696:ℚ),(451213124650458666763/2361183241434822606848:ℚ)⟩ node95 node33
def node97 : BoxExpr 3 := .add ⟨(171509323601254935429/295147905179352825856:ℚ),(686037294405019741717/1180591620717411303424:ℚ)⟩ node30 node96
def node98 : BoxExpr 3 := .add ⟨(-1122315144800857132423/1180591620717411303424:ℚ),(-4489260579203428529671/4722366482869645213696:ℚ)⟩ node94 node97
def node99 : BoxExpr 3 := .mul ⟨(-4891221788619527742887/4722366482869645213696:ℚ),(-1222805447154881935715/1180591620717411303424:ℚ)⟩ node98 node69
def node100 : BoxExpr 3 := .mul ⟨(3978090008866606798599/4722366482869645213696:ℚ),(994522502216651699651/1180591620717411303424:ℚ)⟩ node55 node55
def node101 : BoxExpr 3 := .inv ⟨(5605892563724143501975/4722366482869645213696:ℚ),(175184142616379484437/147573952589676412928:ℚ)⟩ node100
def node102 : BoxExpr 3 := .mul ⟨(-2424792686074623259919/4722366482869645213696:ℚ),(-2424792686074623259911/4722366482869645213696:ℚ)⟩ node89 node101
def node103 : BoxExpr 3 := .neg ⟨(2424792686074623259911/4722366482869645213696:ℚ),(2424792686074623259919/4722366482869645213696:ℚ)⟩ node102
def node104 : BoxExpr 3 := .mul ⟨(5107508982173358823983/4722366482869645213696:ℚ),(5107508982173358824013/4722366482869645213696:ℚ)⟩ node68 node103
def node105 : BoxExpr 3 := .add ⟨(27035899194228885137/590295810358705651712:ℚ),(216287193553831081153/4722366482869645213696:ℚ)⟩ node99 node104
def node106 : BoxExpr 3 := .mul ⟨(496372682460734293415/4722366482869645213696:ℚ),(124093170615183573387/1180591620717411303424:ℚ)⟩ node105 node70
def node107 : BoxExpr 3 := .mul ⟨(496372682460734293415/4722366482869645213696:ℚ),(124093170615183573387/1180591620717411303424:ℚ)⟩ node70 node105
def node108 : BoxExpr 3 := .add ⟨(496372682460734293415/2361183241434822606848:ℚ),(124093170615183573387/590295810358705651712:ℚ)⟩ node106 node107
def node109 : BoxExpr 3 := .neg ⟨(-124093170615183573387/590295810358705651712:ℚ),(-496372682460734293415/2361183241434822606848:ℚ)⟩ node108
def node110 : BoxExpr 3 := .lit (0/1:ℚ)
def node111 : BoxExpr 3 := .lit (123/25:ℚ)
def node112 : BoxExpr 3 := .mul ⟨(21304506941613916041421/4722366482869645213696:ℚ),(10672352998547890678565/2361183241434822606848:ℚ)⟩ node111 node17
def node113 : BoxExpr 3 := .mul ⟨(5797571450291287840453/1180591620717411303424:ℚ),(11638941477525676268035/2361183241434822606848:ℚ)⟩ node112 node37
def node114 : BoxExpr 3 := .mul ⟨(13247086143443645905187/1180591620717411303424:ℚ),(53657353006573751804243/4722366482869645213696:ℚ)⟩ node113 node38
def node115 : BoxExpr 3 := .add ⟨(70578828093081578897/2361183241434822606848:ℚ),(24728256747574862545/590295810358705651712:ℚ)⟩ node7 node7
def node116 : BoxExpr 3 := .mul ⟨(347247834217961368173/4722366482869645213696:ℚ),(243326046396136647443/2361183241434822606848:ℚ)⟩ node115 node9
def node117 : BoxExpr 3 := .add ⟨(1401439202655088439647/2361183241434822606848:ℚ),(367785332985561100751/590295810358705651712:ℚ)⟩ node2 node116
def node118 : BoxExpr 3 := .mul ⟨(1285052760650037625847/2361183241434822606848:ℚ),(1351511619442136092773/2361183241434822606848:ℚ)⟩ node117 node17
def node119 : BoxExpr 3 := .mul ⟨(2797599669470980191217/4722366482869645213696:ℚ),(736958599805650350047/1180591620717411303424:ℚ)⟩ node118 node37
def node120 : BoxExpr 3 := .mul ⟨(207167421752815804683/590295810358705651712:ℚ),(1840121404546218054079/4722366482869645213696:ℚ)⟩ node119 node119
def node121 : BoxExpr 3 := .add ⟨(13661420986949277514553/1180591620717411303424:ℚ),(27748737205559984929161/2361183241434822606848:ℚ)⟩ node114 node120
def node122 : BoxExpr 3 := .mul ⟨(13247086143443645905187/1180591620717411303424:ℚ),(53657353006573751804243/4722366482869645213696:ℚ)⟩ node38 node113
def node123 : BoxExpr 3 := .add ⟨(13661420986949277514553/1180591620717411303424:ℚ),(27748737205559984929161/2361183241434822606848:ℚ)⟩ node120 node122
def node124 : BoxExpr 3 := .add ⟨(13661420986949277514553/590295810358705651712:ℚ),(27748737205559984929161/1180591620717411303424:ℚ)⟩ node121 node123
def node125 : BoxExpr 3 := .neg ⟨(-27748737205559984929161/1180591620717411303424:ℚ),(-13661420986949277514553/590295810358705651712:ℚ)⟩ node124
def node126 : BoxExpr 3 := .add ⟨(932660462837727288623/1180591620717411303424:ℚ),(1884210391606933158101/2361183241434822606848:ℚ)⟩ node13 node13
def node127 : BoxExpr 3 := .neg ⟨(-1884210391606933158101/2361183241434822606848:ℚ),(-932660462837727288623/1180591620717411303424:ℚ)⟩ node126
def node128 : BoxExpr 3 := .mul ⟨(1082546084431601424869/590295810358705651712:ℚ),(2169177438729246072879/1180591620717411303424:ℚ)⟩ node86 node17
def node129 : BoxExpr 3 := .inv ⟨(642546132936308782619/1180591620717411303424:ℚ),(1287517081215056835909/2361183241434822606848:ℚ)⟩ node128
def node130 : BoxExpr 3 := .mul ⟨(-513715543382108805291/1180591620717411303424:ℚ),(-1015215360201872529169/2361183241434822606848:ℚ)⟩ node127 node129
def node131 : BoxExpr 3 := .mul ⟨(-1280287197483822782579/4722366482869645213696:ℚ),(-602563401246206987407/2361183241434822606848:ℚ)⟩ node117 node130
def node132 : BoxExpr 3 := .mul ⟨(-1396242025349711322017/4722366482869645213696:ℚ),(-40993724727228793157/147573952589676412928:ℚ)⟩ node131 node37
def node133 : BoxExpr 3 := .mul ⟨(992643014191527636137/1180591620717411303424:ℚ),(3985570182035240095495/4722366482869645213696:ℚ)⟩ node17 node17
def node134 : BoxExpr 3 := .inv ⟨(5595371347128731033077/4722366482869645213696:ℚ),(2808253430450747877307/2361183241434822606848:ℚ)⟩ node133
def node135 : BoxExpr 3 := .mul ⟨(-1221966522261122307759/2361183241434822606848:ℚ),(-2405788266643232659615/4722366482869645213696:ℚ)⟩ node130 node134
def node136 : BoxExpr 3 := .neg ⟨(2405788266643232659615/4722366482869645213696:ℚ),(1221966522261122307759/2361183241434822606848:ℚ)⟩ node135
def node137 : BoxExpr 3 := .mul ⟨(327332161195450106021/1180591620717411303424:ℚ),(699438283494522260507/2361183241434822606848:ℚ)⟩ node118 node136
def node138 : BoxExpr 3 := .add ⟨(-86913380567910897933/4722366482869645213696:ℚ),(43538687858861569995/2361183241434822606848:ℚ)⟩ node132 node137
def node139 : BoxExpr 3 := .mul ⟨(-200342185375370809187/4722366482869645213696:ℚ),(1568126618030657095/36893488147419103232:ℚ)⟩ node138 node38
def node140 : BoxExpr 3 := .mul ⟨(-5091888851778468121211/4722366482869645213696:ℚ),(-5023937843964172505207/4722366482869645213696:ℚ)⟩ node11 node130
def node141 : BoxExpr 3 := .add ⟨(442718399004515418243/590295810358705651712:ℚ),(447440765487385063457/590295810358705651712:ℚ)⟩ node20 node20
def node142 : BoxExpr 3 := .mul ⟨(796893118208127752837/2361183241434822606848:ℚ),(805393377877293114223/2361183241434822606848:ℚ)⟩ node141 node24
def node143 : BoxExpr 3 := .add ⟨(-2184106949879460665283/4722366482869645213696:ℚ),(-1083553215270564971255/2361183241434822606848:ℚ)⟩ node21 node142
def node144 : BoxExpr 3 := .add ⟨(-3637997900828964393247/2361183241434822606848:ℚ),(-7191044274505302447717/4722366482869645213696:ℚ)⟩ node140 node143
def node145 : BoxExpr 3 := .add ⟨(342364652479021636911/1180591620717411303424:ℚ),(703618770889521854677/2361183241434822606848:ℚ)⟩ node29 node29
def node146 : BoxExpr 3 := .mul ⟨(27817128013920507999/147573952589676412928:ℚ),(914704402156378411081/4722366482869645213696:ℚ)⟩ node145 node33
def node147 : BoxExpr 3 := .add ⟨(2731871024764617889309/4722366482869645213696:ℚ),(2756427330475540044423/4722366482869645213696:ℚ)⟩ node30 node146
def node148 : BoxExpr 3 := .add ⟨(-4544124776893310897185/4722366482869645213696:ℚ),(-2217308472014881201647/2361183241434822606848:ℚ)⟩ node144 node147
def node149 : BoxExpr 3 := .mul ⟨(-2477841688333953158439/2361183241434822606848:ℚ),(-2413574616689748658127/2361183241434822606848:ℚ)⟩ node148 node37
def node150 : BoxExpr 3 := .mul ⟨(5050065835402085158417/4722366482869645213696:ℚ),(5165611793382055681279/4722366482869645213696:ℚ)⟩ node36 node136
def node151 : BoxExpr 3 := .add ⟨(94382458734178841539/4722366482869645213696:ℚ),(338462560002558365025/4722366482869645213696:ℚ)⟩ node149 node150
def node152 : BoxExpr 3 := .mul ⟨(55913562896148853401/4722366482869645213696:ℚ),(211277879606284339081/4722366482869645213696:ℚ)⟩ node119 node151
def node153 : BoxExpr 3 := .add ⟨(-72214311239610977893/2361183241434822606848:ℚ),(411998086714208447241/4722366482869645213696:ℚ)⟩ node139 node152
def node154 : BoxExpr 3 := .mul ⟨(55913562896148853401/4722366482869645213696:ℚ),(211277879606284339081/4722366482869645213696:ℚ)⟩ node151 node119
def node155 : BoxExpr 3 := .mul ⟨(-200342185375370809187/4722366482869645213696:ℚ),(1568126618030657095/36893488147419103232:ℚ)⟩ node38 node138
def node156 : BoxExpr 3 := .add ⟨(-72214311239610977893/2361183241434822606848:ℚ),(411998086714208447241/4722366482869645213696:ℚ)⟩ node154 node155
def node157 : BoxExpr 3 := .add ⟨(-72214311239610977893/1180591620717411303424:ℚ),(411998086714208447241/2361183241434822606848:ℚ)⟩ node153 node156
def node158 : BoxExpr 3 := .neg ⟨(-411998086714208447241/2361183241434822606848:ℚ),(72214311239610977893/1180591620717411303424:ℚ)⟩ node157
def node159 : BoxExpr 3 := .add ⟨(-72214311239610977893/2361183241434822606848:ℚ),(411998086714208447241/4722366482869645213696:ℚ)⟩ node139 node154
def node160 : BoxExpr 3 := .add ⟨(-72214311239610977893/2361183241434822606848:ℚ),(411998086714208447241/4722366482869645213696:ℚ)⟩ node152 node155
def node161 : BoxExpr 3 := .add ⟨(-72214311239610977893/1180591620717411303424:ℚ),(411998086714208447241/2361183241434822606848:ℚ)⟩ node159 node160
def node162 : BoxExpr 3 := .neg ⟨(-411998086714208447241/2361183241434822606848:ℚ),(72214311239610977893/1180591620717411303424:ℚ)⟩ node161
def node163 : BoxExpr 3 := .mul ⟨(-1287517081215056835909/1180591620717411303424:ℚ),(-642546132936308782619/590295810358705651712:ℚ)⟩ node6 node129
def node164 : BoxExpr 3 := .mul ⟨(-513715543382108805291/590295810358705651712:ℚ),(-1015215360201872529169/1180591620717411303424:ℚ)⟩ node86 node130
def node165 : BoxExpr 3 := .mul ⟨(7941144113532221089097/2361183241434822606848:ℚ),(7971140364070480190989/2361183241434822606848:ℚ)⟩ node128 node128
def node166 : BoxExpr 3 := .inv ⟨(1398842836782182758269/4722366482869645213696:ℚ),(702063357612686969327/2361183241434822606848:ℚ)⟩ node165
def node167 : BoxExpr 3 := .mul ⟨(-76372907641320144235/295147905179352825856:ℚ),(-1202894133321616329807/4722366482869645213696:ℚ)⟩ node164 node166
def node168 : BoxExpr 3 := .neg ⟨(1202894133321616329807/4722366482869645213696:ℚ),(76372907641320144235/295147905179352825856:ℚ)⟩ node167
def node169 : BoxExpr 3 := .mul ⟨(-975122124804284227829/4722366482869645213696:ℚ),(-950279317116264469201/4722366482869645213696:ℚ)⟩ node127 node168
def node170 : BoxExpr 3 := .add ⟨(-6125190449664511571465/4722366482869645213696:ℚ),(-6090648380606734730153/4722366482869645213696:ℚ)⟩ node163 node169
def node171 : BoxExpr 3 := .mul ⟨(-15178044234524947625577/4722366482869645213696:ℚ),(-7535110305936651342341/2361183241434822606848:ℚ)⟩ node11 node170
def node172 : BoxExpr 3 := .lit (9/10:ℚ)
def node173 : BoxExpr 3 := .add ⟨(-10927914399942266933251/4722366482869645213696:ℚ),(-10820090777290621992355/4722366482869645213696:ℚ)⟩ node171 node172
def node174 : BoxExpr 3 := .lit (13/10:ℚ)
def node175 : BoxExpr 3 := .add ⟨(-4788837972211728155447/4722366482869645213696:ℚ),(-2340507174780041607275/2361183241434822606848:ℚ)⟩ node173 node174
def node176 : BoxExpr 3 := .mul ⟨(-5222560096307605541659/4722366482869645213696:ℚ),(-5095356625860971296715/4722366482869645213696:ℚ)⟩ node175 node37
def node177 : BoxExpr 3 := .mul ⟨(-1175844435302416655043/2361183241434822606848:ℚ),(-564798891070022474095/1180591620717411303424:ℚ)⟩ node148 node136
def node178 : BoxExpr 3 := .add ⟨(-7574248966912438851745/4722366482869645213696:ℚ),(-7354552190141061193095/4722366482869645213696:ℚ)⟩ node176 node177
def node179 : BoxExpr 3 := .mul ⟨(-1821235936985339772271/1180591620717411303424:ℚ),(-7216602006198773890211/4722366482869645213696:ℚ)⟩ node170 node134
def node180 : BoxExpr 3 := .mul ⟨(-1887765671167229631075/4722366482869645213696:ℚ),(-1861807916904431237171/4722366482869645213696:ℚ)⟩ node130 node17
def node181 : BoxExpr 3 := .mul ⟨(-1887765671167229631075/4722366482869645213696:ℚ),(-1861807916904431237171/4722366482869645213696:ℚ)⟩ node17 node130
def node182 : BoxExpr 3 := .add ⟨(-1887765671167229631075/2361183241434822606848:ℚ),(-1861807916904431237171/2361183241434822606848:ℚ)⟩ node180 node181
def node183 : BoxExpr 3 := .mul ⟨(3338462297485996686873/4722366482869645213696:ℚ),(3363730818764346054609/4722366482869645213696:ℚ)⟩ node133 node133
def node184 : BoxExpr 3 := .inv ⟨(6629765103119255704361/4722366482869645213696:ℚ),(6679945199717854386175/4722366482869645213696:ℚ)⟩ node183
def node185 : BoxExpr 3 := .mul ⟨(-1335153813141039158453/1180591620717411303424:ℚ),(-1306902926846060638563/1180591620717411303424:ℚ)⟩ node182 node184
def node186 : BoxExpr 3 := .neg ⟨(1306902926846060638563/1180591620717411303424:ℚ),(1335153813141039158453/1180591620717411303424:ℚ)⟩ node185
def node187 : BoxExpr 3 := .mul ⟨(-2323883227968866902147/4722366482869645213696:ℚ),(-70239567939073544499/147573952589676412928:ℚ)⟩ node130 node186
def node188 : BoxExpr 3 := .add ⟨(-9608826975910225991231/4722366482869645213696:ℚ),(-9464268180249127314179/4722366482869645213696:ℚ)⟩ node179 node187
def node189 : BoxExpr 3 := .neg ⟨(9464268180249127314179/4722366482869645213696:ℚ),(9608826975910225991231/4722366482869645213696:ℚ)⟩ node188
def node190 : BoxExpr 3 := .mul ⟨(19866743078287274105577/4722366482869645213696:ℚ),(10154834245271345128969/2361183241434822606848:ℚ)⟩ node36 node189
def node191 : BoxExpr 3 := .add ⟨(17515054207682440795491/4722366482869645213696:ℚ),(9025236463131300180779/2361183241434822606848:ℚ)⟩ node177 node190
def node192 : BoxExpr 3 := .add ⟨(4970402620385000971873/2361183241434822606848:ℚ),(10695920736121539168463/4722366482869645213696:ℚ)⟩ node178 node191
def node193 : BoxExpr 3 := .mul ⟨(2839264347338486089221/590295810358705651712:ℚ),(24654939445163969063161/4722366482869645213696:ℚ)⟩ node192 node38
def node194 : BoxExpr 3 := .mul ⟨(471588161837018685/1180591620717411303424:ℚ),(6064592029178584187/1180591620717411303424:ℚ)⟩ node151 node151
def node195 : BoxExpr 3 := .add ⟨(5679000282838809197127/1180591620717411303424:ℚ),(24679197813280683399909/4722366482869645213696:ℚ)⟩ node193 node194
def node196 : BoxExpr 3 := .mul ⟨(2839264347338486089221/590295810358705651712:ℚ),(24654939445163969063161/4722366482869645213696:ℚ)⟩ node38 node192
def node197 : BoxExpr 3 := .add ⟨(5679000282838809197127/1180591620717411303424:ℚ),(24679197813280683399909/4722366482869645213696:ℚ)⟩ node194 node196
def node198 : BoxExpr 3 := .add ⟨(5679000282838809197127/590295810358705651712:ℚ),(24679197813280683399909/2361183241434822606848:ℚ)⟩ node195 node197
def node199 : BoxExpr 3 := .neg ⟨(-24679197813280683399909/2361183241434822606848:ℚ),(-5679000282838809197127/590295810358705651712:ℚ)⟩ node198
def cert_static0 : TaylorCertificate3Reduced :=
  { center := ![(66124043/32768000:ℚ), (16261/40960:ℚ), (0/1:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (0/1:ℚ)],
    whole := node43, centerValue := node74, gradient := ![node83, node109, node110],
    hessian := ![![node125, node158, node110], ![node162, node199, node110], ![node110, node110, node110]] }
theorem cert_static0_check : cert_static0.check = true := by decide +kernel
theorem cert_static0_lower_pos : 0 < cert_static0.lower := by decide +kernel
theorem positive_static0 (A ρ : ℝ)
    (hAlo : (66025739/32768000:ℝ) ≤ A) (hAhi : A ≤ (66222347/32768000:ℝ))
    (hρlo : (404477/1024000:ℝ) ≤ ρ) (hρhi : ρ ≤ (408573/1024000:ℝ)) :
    0 < node43.eval ![A,ρ,0] := by
  apply cert_static0.positive_sound cert_static0_check cert_static0_lower_pos ![A,ρ,0]
  intro i
  fin_cases i
  · norm_num [cert_static0,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_static0,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_static0,Matrix.cons_val_two]
def node200 : BoxExpr 3 := .sqrt ⟨(785618801982371556317/1180591620717411303424:ℚ),(1727488277759528370291/2361183241434822606848:ℚ)⟩ node43
def node201 : BoxExpr 3 := .lit (33122966341758741077667512113159081635002439125022389799/132922799578491587290380706028034457600000000000000000000:ℚ)
def node202 : BoxExpr 3 := .sqrt ⟨(147334541848593700891/295147905179352825856:ℚ),(1178676334788749607129/2361183241434822606848:ℚ)⟩ node201
def node203 : BoxExpr 3 := .lit (266732711456819402766503272231896970748968762053683/456324345907579086572258966178089783278423978885120:ℚ)
def node204 : BoxExpr 3 := .mul ⟨(1377930139067634999113/4722366482869645213696:ℚ),(344482534766908749779/1180591620717411303424:ℚ)⟩ node202 node203
def node205 : BoxExpr 3 := .neg ⟨(-344482534766908749779/1180591620717411303424:ℚ),(-1377930139067634999113/4722366482869645213696:ℚ)⟩ node204
def node206 : BoxExpr 3 := .add ⟨(220568133607731403269/590295810358705651712:ℚ),(2077046416451421741469/4722366482869645213696:ℚ)⟩ node200 node205
def node207 : BoxExpr 3 := .sqrt ⟨(3303349947460461959087/4722366482869645213696:ℚ),(1651674973730230979599/2361183241434822606848:ℚ)⟩ node74
def node208 : BoxExpr 3 := .add ⟨(1925419808392826959971/4722366482869645213696:ℚ),(1925419808392826960085/4722366482869645213696:ℚ)⟩ node207 node205
def node209 : BoxExpr 3 := .mul ⟨(3303349947460461959087/2361183241434822606848:ℚ),(1651674973730230979599/1180591620717411303424:ℚ)⟩ node86 node207
def node210 : BoxExpr 3 := .inv ⟨(3375474223624855963991/4722366482869645213696:ℚ),(1687737111812427982053/2361183241434822606848:ℚ)⟩ node209
def node211 : BoxExpr 3 := .mul ⟨(-4712207305725607899221/2361183241434822606848:ℚ),(-2356103652862803949513/1180591620717411303424:ℚ)⟩ node83 node210
def node212 : BoxExpr 3 := .mul ⟨(-709598969514786834301/4722366482869645213696:ℚ),(-709598969514786834085/4722366482869645213696:ℚ)⟩ node109 node210
def node213 : BoxExpr 3 := .mul ⟨(785618801982371556317/590295810358705651712:ℚ),(1727488277759528370291/1180591620717411303424:ℚ)⟩ node86 node200
def node214 : BoxExpr 3 := .inv ⟨(3227336689579979134739/4722366482869645213696:ℚ),(3548277030516994289677/4722366482869645213696:ℚ)⟩ node213
def node215 : BoxExpr 3 := .mul ⟨(-83399039197406303864321/4722366482869645213696:ℚ),(-74691374069192723247215/4722366482869645213696:ℚ)⟩ node125 node214
def node216 : BoxExpr 3 := .mul ⟨(6392339298291793326629/4722366482869645213696:ℚ),(849373798668858805483/590295810358705651712:ℚ)⟩ node119 node38
def node217 : BoxExpr 3 := .mul ⟨(6392339298291793326629/4722366482869645213696:ℚ),(849373798668858805483/590295810358705651712:ℚ)⟩ node38 node119
def node218 : BoxExpr 3 := .add ⟨(6392339298291793326629/2361183241434822606848:ℚ),(849373798668858805483/295147905179352825856:ℚ)⟩ node216 node217
def node219 : BoxExpr 3 := .neg ⟨(-849373798668858805483/295147905179352825856:ℚ),(-6392339298291793326629/2361183241434822606848:ℚ)⟩ node218
def node220 : BoxExpr 3 := .mul ⟨(-10211197461517711126647/4722366482869645213696:ℚ),(-8737242746600492400359/4722366482869645213696:ℚ)⟩ node219 node214
def node221 : BoxExpr 3 := .mul ⟨(-10211197461517711126647/2361183241434822606848:ℚ),(-8737242746600492400359/2361183241434822606848:ℚ)⟩ node86 node220
def node222 : BoxExpr 3 := .mul ⟨(4182288887689472606007/2361183241434822606848:ℚ),(10110916247171600422191/4722366482869645213696:ℚ)⟩ node213 node213
def node223 : BoxExpr 3 := .inv ⟨(2205610713546259623359/4722366482869645213696:ℚ),(666523337979253825249/1180591620717411303424:ℚ)⟩ node222
def node224 : BoxExpr 3 := .mul ⟨(-5764907439102657970157/2361183241434822606848:ℚ),(-8161567416955742860557/4722366482869645213696:ℚ)⟩ node221 node223
def node225 : BoxExpr 3 := .neg ⟨(8161567416955742860557/4722366482869645213696:ℚ),(5764907439102657970157/2361183241434822606848:ℚ)⟩ node224
def node226 : BoxExpr 3 := .mul ⟨(-33180390201648146834113/4722366482869645213696:ℚ),(-11047746574586249485985/2361183241434822606848:ℚ)⟩ node219 node225
def node227 : BoxExpr 3 := .add ⟨(-58289714699527225349217/2361183241434822606848:ℚ),(-96786867218365222219185/4722366482869645213696:ℚ)⟩ node215 node226
def node228 : BoxExpr 3 := .mul ⟨(-309565840137131952261/2361183241434822606848:ℚ),(27130082213611831371/590295810358705651712:ℚ)⟩ node158 node214
def node229 : BoxExpr 3 := .mul ⟨(53914495578095190859/1180591620717411303424:ℚ),(48761428113528643889/295147905179352825856:ℚ)⟩ node151 node38
def node230 : BoxExpr 3 := .mul ⟨(53914495578095190859/1180591620717411303424:ℚ),(48761428113528643889/295147905179352825856:ℚ)⟩ node38 node151
def node231 : BoxExpr 3 := .add ⟨(53914495578095190859/590295810358705651712:ℚ),(48761428113528643889/147573952589676412928:ℚ)⟩ node229 node230
def node232 : BoxExpr 3 := .neg ⟨(-48761428113528643889/147573952589676412928:ℚ),(-53914495578095190859/590295810358705651712:ℚ)⟩ node231
def node233 : BoxExpr 3 := .mul ⟨(-146552840384637521829/590295810358705651712:ℚ),(-294767854736507889581/4722366482869645213696:ℚ)⟩ node232 node214
def node234 : BoxExpr 3 := .mul ⟨(-146552840384637521829/295147905179352825856:ℚ),(-294767854736507889581/2361183241434822606848:ℚ)⟩ node86 node233
def node235 : BoxExpr 3 := .mul ⟨(-330955723043846609623/1180591620717411303424:ℚ),(-68836582333696413237/1180591620717411303424:ℚ)⟩ node234 node223
def node236 : BoxExpr 3 := .neg ⟨(68836582333696413237/1180591620717411303424:ℚ),(330955723043846609623/1180591620717411303424:ℚ)⟩ node235
def node237 : BoxExpr 3 := .mul ⟨(-1904842384038818318795/2361183241434822606848:ℚ),(-745434378306691119509/4722366482869645213696:ℚ)⟩ node219 node236
def node238 : BoxExpr 3 := .add ⟨(-138400514010996891941/147573952589676412928:ℚ),(-528393720597796468541/4722366482869645213696:ℚ)⟩ node228 node237
def node239 : BoxExpr 3 := .mul ⟨(-309565840137131952261/2361183241434822606848:ℚ),(27130082213611831371/590295810358705651712:ℚ)⟩ node162 node214
def node240 : BoxExpr 3 := .mul ⟨(-3809684768077636637585/4722366482869645213696:ℚ),(-372717189153345559755/2361183241434822606848:ℚ)⟩ node232 node225
def node241 : BoxExpr 3 := .add ⟨(-4428816448351900542107/4722366482869645213696:ℚ),(-264196860298898234271/2361183241434822606848:ℚ)⟩ node239 node240
def node242 : BoxExpr 3 := .mul ⟨(-37086757688164923552567/4722366482869645213696:ℚ),(-3881114699468082249315/590295810358705651712:ℚ)⟩ node199 node214
def node243 : BoxExpr 3 := .mul ⟨(-218708971532857788051/2361183241434822606848:ℚ),(-12574338318904949349/2361183241434822606848:ℚ)⟩ node232 node236
def node244 : BoxExpr 3 := .add ⟨(-37524175631230639128669/4722366482869645213696:ℚ),(-15537033136191233946609/2361183241434822606848:ℚ)⟩ node242 node243
def cert_static1 : TaylorCertificate3Reduced :=
  { center := ![(66124043/32768000:ℚ), (16261/40960:ℚ), (0/1:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (0/1:ℚ)],
    whole := node206, centerValue := node208, gradient := ![node211, node212, node110],
    hessian := ![![node227, node238, node110], ![node241, node244, node110], ![node110, node110, node110]] }
theorem cert_static1_check : cert_static1.check = true := by decide +kernel
theorem cert_static1_lower_pos : 0 < cert_static1.lower := by decide +kernel
theorem positive_static1 (A ρ : ℝ)
    (hAlo : (66025739/32768000:ℝ) ≤ A) (hAhi : A ≤ (66222347/32768000:ℝ))
    (hρlo : (404477/1024000:ℝ) ≤ ρ) (hρhi : ρ ≤ (408573/1024000:ℝ)) :
    0 < node206.eval ![A,ρ,0] := by
  apply cert_static1.positive_sound cert_static1_check cert_static1_lower_pos ![A,ρ,0]
  intro i
  fin_cases i
  · norm_num [cert_static1,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_static1,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_static1,Matrix.cons_val_two]
def node245 : BoxExpr 3 := .lit (2303310553701196424145761883027290358774723356106349152374508838028109147083679876455884732236856925821119/2303793801264557708801064384615049401895805870002741631354811158982456791788718297021736288256000000000000:ℚ)
def node246 : BoxExpr 3 := .lit (456324345907579086572258966178089783278423978885120/723057057364398489338762238409986754027392740938803:ℚ)
def node247 : BoxExpr 3 := .mul ⟨(1113611804451318561465/4722366482869645213696:ℚ),(1310832717492183577259/4722366482869645213696:ℚ)⟩ node206 node246
def node248 : BoxExpr 3 := .mul ⟨(131304003565997059199/2361183241434822606848:ℚ),(363860454177159149695/4722366482869645213696:ℚ)⟩ node247 node247
def node249 : BoxExpr 3 := .neg ⟨(-363860454177159149695/4722366482869645213696:ℚ),(-131304003565997059199/2361183241434822606848:ℚ)⟩ node248
def node250 : BoxExpr 3 := .add ⟨(4357515457359716125463/4722366482869645213696:ℚ),(4458767904404881156761/4722366482869645213696:ℚ)⟩ node245 node249
def node251 : BoxExpr 3 := .mul ⟨(303785132069998468785/1180591620717411303424:ℚ),(1215140528279993875213/4722366482869645213696:ℚ)⟩ node208 node246
def node252 : BoxExpr 3 := .mul ⟨(156337559656246324941/2361183241434822606848:ℚ),(4885548739257697655/73786976294838206464:ℚ)⟩ node251 node251
def node253 : BoxExpr 3 := .neg ⟨(-4885548739257697655/73786976294838206464:ℚ),(-156337559656246324941/2361183241434822606848:ℚ)⟩ node252
def node254 : BoxExpr 3 := .add ⟨(2204350396112191312619/2361183241434822606848:ℚ),(4408700792224382625277/4722366482869645213696:ℚ)⟩ node245 node253
def node255 : BoxExpr 3 := .mul ⟨(-5947787645982331267275/4722366482869645213696:ℚ),(-5947787645982331267025/4722366482869645213696:ℚ)⟩ node211 node246
def node256 : BoxExpr 3 := .mul ⟨(-95653813724188013823/295147905179352825856:ℚ),(-765230509793504110505/2361183241434822606848:ℚ)⟩ node255 node251
def node257 : BoxExpr 3 := .mul ⟨(-95653813724188013823/295147905179352825856:ℚ),(-765230509793504110505/2361183241434822606848:ℚ)⟩ node251 node255
def node258 : BoxExpr 3 := .add ⟨(-95653813724188013823/147573952589676412928:ℚ),(-765230509793504110505/1180591620717411303424:ℚ)⟩ node256 node257
def node259 : BoxExpr 3 := .neg ⟨(765230509793504110505/1180591620717411303424:ℚ),(95653813724188013823/147573952589676412928:ℚ)⟩ node258
def node260 : BoxExpr 3 := .mul ⟨(-223915445069322070607/2361183241434822606848:ℚ),(-447830890138644141077/4722366482869645213696:ℚ)⟩ node212 node246
def node261 : BoxExpr 3 := .mul ⟨(-115234060379932874567/4722366482869645213696:ℚ),(-28808515094983218631/1180591620717411303424:ℚ)⟩ node260 node251
def node262 : BoxExpr 3 := .mul ⟨(-115234060379932874567/4722366482869645213696:ℚ),(-28808515094983218631/1180591620717411303424:ℚ)⟩ node251 node260
def node263 : BoxExpr 3 := .add ⟨(-115234060379932874567/2361183241434822606848:ℚ),(-28808515094983218631/590295810358705651712:ℚ)⟩ node261 node262
def node264 : BoxExpr 3 := .neg ⟨(28808515094983218631/590295810358705651712:ℚ),(115234060379932874567/2361183241434822606848:ℚ)⟩ node263
def node265 : BoxExpr 3 := .mul ⟨(-73573767553992835353497/4722366482869645213696:ℚ),(-61082598428474797321503/4722366482869645213696:ℚ)⟩ node227 node246
def node266 : BoxExpr 3 := .mul ⟨(-20422578808481868849581/4722366482869645213696:ℚ),(-7202141437270865206057/2361183241434822606848:ℚ)⟩ node265 node247
def node267 : BoxExpr 3 := .mul ⟨(-6444329607327098568087/4722366482869645213696:ℚ),(-689263824474517902955/590295810358705651712:ℚ)⟩ node220 node246
def node268 : BoxExpr 3 := .mul ⟨(6438597210311133651653/4722366482869645213696:ℚ),(1099273643800206332641/590295810358705651712:ℚ)⟩ node267 node267
def node269 : BoxExpr 3 := .add ⟨(-1747997699771341899741/590295810358705651712:ℚ),(-2805046862070039875493/2361183241434822606848:ℚ)⟩ node266 node268
def node270 : BoxExpr 3 := .mul ⟨(-20422578808481868849581/4722366482869645213696:ℚ),(-7202141437270865206057/2361183241434822606848:ℚ)⟩ node247 node265
def node271 : BoxExpr 3 := .add ⟨(-1747997699771341899741/590295810358705651712:ℚ),(-2805046862070039875493/2361183241434822606848:ℚ)⟩ node268 node270
def node272 : BoxExpr 3 := .add ⟨(-1747997699771341899741/295147905179352825856:ℚ),(-2805046862070039875493/1180591620717411303424:ℚ)⟩ node269 node271
def node273 : BoxExpr 3 := .neg ⟨(2805046862070039875493/1180591620717411303424:ℚ),(1747997699771341899741/295147905179352825856:ℚ)⟩ node272
def node274 : BoxExpr 3 := .mul ⟨(-2795044662596244432329/4722366482869645213696:ℚ),(-166735748221834354283/2361183241434822606848:ℚ)⟩ node238 node246
def node275 : BoxExpr 3 := .mul ⟨(-775847449339986744169/4722366482869645213696:ℚ),(-78638071872399874485/4722366482869645213696:ℚ)⟩ node274 node247
def node276 : BoxExpr 3 := .mul ⟨(-739920904977370832537/4722366482869645213696:ℚ),(-46507307804143484013/1180591620717411303424:ℚ)⟩ node233 node246
def node277 : BoxExpr 3 := .mul ⟨(108609291411430305351/2361183241434822606848:ℚ),(1009725571347096601595/4722366482869645213696:ℚ)⟩ node267 node276
def node278 : BoxExpr 3 := .add ⟨(-558628866517126133467/4722366482869645213696:ℚ),(465543749737348363555/2361183241434822606848:ℚ)⟩ node275 node277
def node279 : BoxExpr 3 := .mul ⟨(108609291411430305351/2361183241434822606848:ℚ),(1009725571347096601595/4722366482869645213696:ℚ)⟩ node276 node267
def node280 : BoxExpr 3 := .mul ⟨(-775847449339986744169/4722366482869645213696:ℚ),(-78638071872399874485/4722366482869645213696:ℚ)⟩ node247 node274
def node281 : BoxExpr 3 := .add ⟨(-558628866517126133467/4722366482869645213696:ℚ),(465543749737348363555/2361183241434822606848:ℚ)⟩ node279 node280
def node282 : BoxExpr 3 := .add ⟨(-558628866517126133467/2361183241434822606848:ℚ),(465543749737348363555/1180591620717411303424:ℚ)⟩ node278 node281
def node283 : BoxExpr 3 := .neg ⟨(-465543749737348363555/1180591620717411303424:ℚ),(558628866517126133467/2361183241434822606848:ℚ)⟩ node282
def node284 : BoxExpr 3 := .mul ⟨(-1397522331298122216163/2361183241434822606848:ℚ),(-333471496443668708567/4722366482869645213696:ℚ)⟩ node241 node246
def node285 : BoxExpr 3 := .mul ⟨(-96980931167498343021/590295810358705651712:ℚ),(-78638071872399874485/4722366482869645213696:ℚ)⟩ node284 node247
def node286 : BoxExpr 3 := .add ⟨(-279314433258563066733/2361183241434822606848:ℚ),(465543749737348363555/2361183241434822606848:ℚ)⟩ node285 node279
def node287 : BoxExpr 3 := .mul ⟨(-96980931167498343021/590295810358705651712:ℚ),(-78638071872399874485/4722366482869645213696:ℚ)⟩ node247 node284
def node288 : BoxExpr 3 := .add ⟨(-279314433258563066733/2361183241434822606848:ℚ),(465543749737348363555/2361183241434822606848:ℚ)⟩ node277 node287
def node289 : BoxExpr 3 := .add ⟨(-279314433258563066733/1180591620717411303424:ℚ),(465543749737348363555/1180591620717411303424:ℚ)⟩ node286 node288
def node290 : BoxExpr 3 := .neg ⟨(-465543749737348363555/1180591620717411303424:ℚ),(279314433258563066733/1180591620717411303424:ℚ)⟩ node289
def node291 : BoxExpr 3 := .mul ⟨(-5920416212746014693613/1180591620717411303424:ℚ),(-4902743435670348739897/1180591620717411303424:ℚ)⟩ node244 node246
def node292 : BoxExpr 3 := .mul ⟨(-6573547649036084734523/4722366482869645213696:ℚ),(-9032403602562027403/9223372036854775808:ℚ)⟩ node291 node247
def node293 : BoxExpr 3 := .mul ⟨(3664145401735099133/2361183241434822606848:ℚ),(115934023250529662819/4722366482869645213696:ℚ)⟩ node276 node276
def node294 : BoxExpr 3 := .add ⟨(-6566219358232614536257/4722366482869645213696:ℚ),(-4508656621261228367517/4722366482869645213696:ℚ)⟩ node292 node293
def node295 : BoxExpr 3 := .mul ⟨(-6573547649036084734523/4722366482869645213696:ℚ),(-9032403602562027403/9223372036854775808:ℚ)⟩ node247 node291
def node296 : BoxExpr 3 := .add ⟨(-6566219358232614536257/4722366482869645213696:ℚ),(-4508656621261228367517/4722366482869645213696:ℚ)⟩ node293 node295
def node297 : BoxExpr 3 := .add ⟨(-6566219358232614536257/2361183241434822606848:ℚ),(-4508656621261228367517/2361183241434822606848:ℚ)⟩ node294 node296
def node298 : BoxExpr 3 := .neg ⟨(4508656621261228367517/2361183241434822606848:ℚ),(6566219358232614536257/2361183241434822606848:ℚ)⟩ node297
def cert_static2 : TaylorCertificate3Reduced :=
  { center := ![(66124043/32768000:ℚ), (16261/40960:ℚ), (0/1:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (0/1:ℚ)],
    whole := node250, centerValue := node254, gradient := ![node259, node264, node110],
    hessian := ![![node273, node283, node110], ![node290, node298, node110], ![node110, node110, node110]] }
theorem cert_static2_check : cert_static2.check = true := by decide +kernel
theorem cert_static2_lower_pos : 0 < cert_static2.lower := by decide +kernel
theorem positive_static2 (A ρ : ℝ)
    (hAlo : (66025739/32768000:ℝ) ≤ A) (hAhi : A ≤ (66222347/32768000:ℝ))
    (hρlo : (404477/1024000:ℝ) ≤ ρ) (hρhi : ρ ≤ (408573/1024000:ℝ)) :
    0 < node250.eval ![A,ρ,0] := by
  apply cert_static2.positive_sound cert_static2_check cert_static2_lower_pos ![A,ρ,0]
  intro i
  fin_cases i
  · norm_num [cert_static2,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_static2,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_static2,Matrix.cons_val_two]
def node299 : BoxExpr 3 := .lit (-10963/50000:ℚ)
def node300 : BoxExpr 3 := .mul ⟨(-206565985231868082123/2361183241434822606848:ℚ),(-204495133081800085303/2361183241434822606848:ℚ)⟩ node13 node299
def node301 : BoxExpr 3 := .lit (1/2:ℚ)
def node302 : BoxExpr 3 := .add ⟨(974025635485543221301/2361183241434822606848:ℚ),(976096487635611218121/2361183241434822606848:ℚ)⟩ node300 node301
def node303 : BoxExpr 3 := .mul ⟨(4089215707610561737257/4722366482869645213696:ℚ),(1031561715512337927345/1180591620717411303424:ℚ)⟩ node36 node302
def node304 : BoxExpr 3 := .inv ⟨(699421418391091379135/590295810358705651712:ℚ),(1404126715225373938653/1180591620717411303424:ℚ)⟩ node16
def node305 : BoxExpr 3 := .mul ⟨(4845172539147988733659/4722366482869645213696:ℚ),(4907517003295055339133/4722366482869645213696:ℚ)⟩ node303 node304
def node306 : BoxExpr 3 := .mul ⟨(932660462837727288623/4722366482869645213696:ℚ),(942105195803466579051/4722366482869645213696:ℚ)⟩ node13 node301
def node307 : BoxExpr 3 := .add ⟨(-25691403049067780233/1180591620717411303424:ℚ),(-93320879230531830503/4722366482869645213696:ℚ)⟩ node299 node306
def node308 : BoxExpr 3 := .lit (-4463044196700782098633982290241252447823512137391687473978729294628281428437691326521755513111644247407593234707/112731987589976307366862910835847314262401851804042833045766368402263387157868406476875081754460466844792866734080:ℚ)
def node309 : BoxExpr 3 := .mul ⟨(1847280516314930909/2361183241434822606848:ℚ),(508559592244065185/590295810358705651712:ℚ)⟩ node307 node308
def node310 : BoxExpr 3 := .mul ⟨(4021586910757383637/4722366482869645213696:ℚ),(4436956185964511239/4722366482869645213696:ℚ)⟩ node309 node37
def node311 : BoxExpr 3 := .add ⟨(303074632878671632331/295147905179352825856:ℚ),(1227988489870254962593/1180591620717411303424:ℚ)⟩ node305 node310
def node312 : BoxExpr 3 := .sqrt ⟨(4536274346247360302947/4722366482869645213696:ℚ),(143396086432499176873/147573952589676412928:ℚ)⟩ node250
def node313 : BoxExpr 3 := .lit (723057057364398489338762238409986754027392740938803/456324345907579086572258966178089783278423978885120:ℚ)
def node314 : BoxExpr 3 := .mul ⟨(7187837356500661807169/4722366482869645213696:ℚ),(7270867099566284852581/4722366482869645213696:ℚ)⟩ node312 node313
def node315 : BoxExpr 3 := .lit (3/2:ℚ)
def node316 : BoxExpr 3 := .mul ⟨(10781756034750992710753/4722366482869645213696:ℚ),(1363287581168678409859/590295810358705651712:ℚ)⟩ node314 node315
def node317 : BoxExpr 3 := .add ⟨(15630950160809738828049/4722366482869645213696:ℚ),(3954563652207611782311/1180591620717411303424:ℚ)⟩ node311 node316
def node318 : BoxExpr 3 := .lit (3/1:ℚ)
def node319 : BoxExpr 3 := .sqrt ⟨(8179378680290567732005/4722366482869645213696:ℚ),(4089689340145283866003/2361183241434822606848:ℚ)⟩ node318
def node320 : BoxExpr 3 := .mul ⟨(2044844670072641933001/2361183241434822606848:ℚ),(4089689340145283866003/4722366482869645213696:ℚ)⟩ node319 node301
def node321 : BoxExpr 3 := .mul ⟨(1195261590243901294299/2361183241434822606848:ℚ),(2390523180487802588601/4722366482869645213696:ℚ)⟩ node320 node203
def node322 : BoxExpr 3 := .mul ⟨(602096784928655801385/590295810358705651712:ℚ),(4831117418512173226619/4722366482869645213696:ℚ)⟩ node321 node1
def node323 : BoxExpr 3 := .neg ⟨(-4831117418512173226619/4722366482869645213696:ℚ),(-602096784928655801385/590295810358705651712:ℚ)⟩ node322
def node324 : BoxExpr 3 := .add ⟨(5399916371148782800715/2361183241434822606848:ℚ),(2750370082350300179541/1180591620717411303424:ℚ)⟩ node317 node323
def node325 : BoxExpr 3 := .lit (-3/1000000:ℚ)
def node326 : BoxExpr 3 := .add ⟨(5399909287599058496247/2361183241434822606848:ℚ),(11001466162301752109229/4722366482869645213696:ℚ)⟩ node324 node325
def node327 : BoxExpr 3 := .lit (2379812631/2500000000:ℚ)
def node328 : BoxExpr 3 := .sqrt ⟨(575931827043009164565/590295810358705651712:ℚ),(4607454616344073316521/4722366482869645213696:ℚ)⟩ node327
def node329 : BoxExpr 3 := .mul ⟨(2850080697015310292705/1180591620717411303424:ℚ),(11417138871047974434969/4722366482869645213696:ℚ)⟩ node11 node328
def node330 : BoxExpr 3 := .lit (-3467541/25000000:ℚ)
def node331 : BoxExpr 3 := .add ⟨(5372661406103094736731/2361183241434822606848:ℚ),(2690534723798230684403/1180591620717411303424:ℚ)⟩ node329 node330
def node332 : BoxExpr 3 := .lit (38963398397/1250000000000:ℚ)
def node333 : BoxExpr 3 := .add ⟨(10892522369525141203285/4722366482869645213696:ℚ),(2727334613127968616859/1180591620717411303424:ℚ)⟩ node331 node332
def node334 : BoxExpr 3 := .neg ⟨(-2727334613127968616859/1180591620717411303424:ℚ),(-10892522369525141203285/4722366482869645213696:ℚ)⟩ node333
def node335 : BoxExpr 3 := .add ⟨(-54759938656878737471/2361183241434822606848:ℚ),(13617974097076363243/590295810358705651712:ℚ)⟩ node326 node334
def node336 : BoxExpr 3 := .mul ⟨(489444229643170581185/590295810358705651712:ℚ),(1991277838382942042805/2361183241434822606848:ℚ)⟩ node36 node13
def node337 : BoxExpr 3 := .mul ⟨(4639406498410873073863/4722366482869645213696:ℚ),(4736619100533123232943/4722366482869645213696:ℚ)⟩ node336 node304
def node338 : BoxExpr 3 := .mul ⟨(-101945255473893958287/2361183241434822606848:ℚ),(-50876629624312736347/1180591620717411303424:ℚ)⟩ node308 node37
def node339 : BoxExpr 3 := .add ⟨(4435515987463085157289/4722366482869645213696:ℚ),(4533112582035872287555/4722366482869645213696:ℚ)⟩ node337 node338
def node340 : BoxExpr 3 := .mul ⟨(-1282877887438369916039/2361183241434822606848:ℚ),(-2561976722828644964879/4722366482869645213696:ℚ)⟩ node11 node299
def node341 : BoxExpr 3 := .inv ⟨(4840144299940133938763/4722366482869645213696:ℚ),(4840144299940133938765/4722366482869645213696:ℚ)⟩ node328
def node342 : BoxExpr 3 := .mul ⟨(-2629746808905371839137/4722366482869645213696:ℚ),(-656468376425279313069/1180591620717411303424:ℚ)⟩ node340 node341
def node343 : BoxExpr 3 := .neg ⟨(656468376425279313069/1180591620717411303424:ℚ),(2629746808905371839137/4722366482869645213696:ℚ)⟩ node342
def node344 : BoxExpr 3 := .lit (7553/10000:ℚ)
def node345 : BoxExpr 3 := .add ⟨(1548169227553140070545/1180591620717411303424:ℚ),(3098275106708407434521/2361183241434822606848:ℚ)⟩ node343 node344
def node346 : BoxExpr 3 := .lit (-4527719/12500000:ℚ)
def node347 : BoxExpr 3 := .add ⟨(4482153034256394909595/4722366482869645213696:ℚ),(2243013168730324748229/2361183241434822606848:ℚ)⟩ node345 node346
def node348 : BoxExpr 3 := .neg ⟨(-2243013168730324748229/2361183241434822606848:ℚ),(-4482153034256394909595/4722366482869645213696:ℚ)⟩ node347
def node349 : BoxExpr 3 := .add ⟨(-50510349997564339169/4722366482869645213696:ℚ),(6369943472434672245/590295810358705651712:ℚ)⟩ node339 node348
def node350 : BoxExpr 3 := .mul ⟨(-272531219611620357/2361183241434822606848:ℚ),(274954889599207027/2361183241434822606848:ℚ)⟩ node349 node349
def node351 : BoxExpr 3 := .lit (2/3:ℚ)
def node352 : BoxExpr 3 := .mul ⟨(-363374959482160477/4722366482869645213696:ℚ),(183303259732804685/2361183241434822606848:ℚ)⟩ node350 node351
def node353 : BoxExpr 3 := .neg ⟨(-183303259732804685/2361183241434822606848:ℚ),(363374959482160477/4722366482869645213696:ℚ)⟩ node352
def node354 : BoxExpr 3 := .add ⟨(-13735810479152885539/590295810358705651712:ℚ),(109307167736093066421/4722366482869645213696:ℚ)⟩ node335 node353
def node355 : BoxExpr 3 := .mul ⟨(-411061118313668167427/4722366482869645213696:ℚ),(-411061118313668167425/4722366482869645213696:ℚ)⟩ node51 node299
def node356 : BoxExpr 3 := .add ⟨(1950122123121154439421/4722366482869645213696:ℚ),(1950122123121154439423/4722366482869645213696:ℚ)⟩ node355 node301
def node357 : BoxExpr 3 := .mul ⟨(1026919364836552130787/1180591620717411303424:ℚ),(4107677459346208523163/4722366482869645213696:ℚ)⟩ node68 node356
def node358 : BoxExpr 3 := .inv ⟨(5605892563724143501977/4722366482869645213696:ℚ),(5605892563724143501981/4722366482869645213696:ℚ)⟩ node54
def node359 : BoxExpr 3 := .mul ⟨(4876198958098066150391/4722366482869645213696:ℚ),(4876198958098066150413/4722366482869645213696:ℚ)⟩ node357 node358
def node360 : BoxExpr 3 := .mul ⟨(234345707330149233459/1180591620717411303424:ℚ),(937382829320596933837/4722366482869645213696:ℚ)⟩ node51 node301
def node361 : BoxExpr 3 := .add ⟨(-98043245713401475719/4722366482869645213696:ℚ),(-98043245713401475717/4722366482869645213696:ℚ)⟩ node299 node360
def node362 : BoxExpr 3 := .mul ⟨(121297465165349739/147573952589676412928:ℚ),(1940759442645595825/2361183241434822606848:ℚ)⟩ node361 node308
def node363 : BoxExpr 3 := .mul ⟨(2114531937912502461/2361183241434822606848:ℚ),(4229063875825004925/4722366482869645213696:ℚ)⟩ node362 node69
def node364 : BoxExpr 3 := .add ⟨(4880428021973891155313/4722366482869645213696:ℚ),(2440214010986945577669/2361183241434822606848:ℚ)⟩ node359 node363
def node365 : BoxExpr 3 := .sqrt ⟨(4562839122103832873107/4722366482869645213696:ℚ),(570354890262979109141/590295810358705651712:ℚ)⟩ node254
def node366 : BoxExpr 3 := .mul ⟨(3614964945924394590007/2361183241434822606848:ℚ),(7229929891848789180049/4722366482869645213696:ℚ)⟩ node365 node313
def node367 : BoxExpr 3 := .mul ⟨(10844894837773183770021/4722366482869645213696:ℚ),(5422447418886591885037/2361183241434822606848:ℚ)⟩ node366 node315
def node368 : BoxExpr 3 := .add ⟨(7862661429873537462667/2361183241434822606848:ℚ),(3931330714936768731353/1180591620717411303424:ℚ)⟩ node364 node367
def node369 : BoxExpr 3 := .mul ⟨(2411972924485354909423/2361183241434822606848:ℚ),(4823945848970709818853/4722366482869645213696:ℚ)⟩ node321 node44
def node370 : BoxExpr 3 := .neg ⟨(-4823945848970709818853/4722366482869645213696:ℚ),(-2411972924485354909423/2361183241434822606848:ℚ)⟩ node369
def node371 : BoxExpr 3 := .add ⟨(10901377010776365106481/4722366482869645213696:ℚ),(5450688505388182553283/2361183241434822606848:ℚ)⟩ node368 node370
def node372 : BoxExpr 3 := .add ⟨(10901362843676916497545/4722366482869645213696:ℚ),(10901362843676916497631/4722366482869645213696:ℚ)⟩ node371 node325
def node373 : BoxExpr 3 := .mul ⟨(5704314410254700972553/2361183241434822606848:ℚ),(5704314410254700972559/2361183241434822606848:ℚ)⟩ node50 node328
def node374 : BoxExpr 3 := .add ⟨(2688407211163587561937/1180591620717411303424:ℚ),(10753628844654350247761/4722366482869645213696:ℚ)⟩ node373 node330
def node375 : BoxExpr 3 := .add ⟨(10900828401973301977571/4722366482869645213696:ℚ),(10900828401973301977585/4722366482869645213696:ℚ)⟩ node374 node332
def node376 : BoxExpr 3 := .neg ⟨(-10900828401973301977585/4722366482869645213696:ℚ),(-10900828401973301977571/4722366482869645213696:ℚ)⟩ node375
def node377 : BoxExpr 3 := .add ⟨(66805212951814995/590295810358705651712:ℚ),(133610425903630015/1180591620717411303424:ℚ)⟩ node372 node376
def node378 : BoxExpr 3 := .mul ⟨(1974474456305203347823/2361183241434822606848:ℚ),(3948948912610406695659/4722366482869645213696:ℚ)⟩ node68 node51
def node379 : BoxExpr 3 := .mul ⟨(4687773264534305138209/4722366482869645213696:ℚ),(1171943316133576284557/1180591620717411303424:ℚ)⟩ node378 node358
def node380 : BoxExpr 3 := .mul ⟨(-101848879827429804921/2361183241434822606848:ℚ),(-12731109978428725615/295147905179352825856:ℚ)⟩ node308 node69
def node381 : BoxExpr 3 := .add ⟨(4484075504879445528367/4722366482869645213696:ℚ),(1121018876219861382097/1180591620717411303424:ℚ)⟩ node379 node380
def node382 : BoxExpr 3 := .mul ⟨(-2563843324519391145757/4722366482869645213696:ℚ),(-2563843324519391145751/4722366482869645213696:ℚ)⟩ node50 node299
def node383 : BoxExpr 3 := .mul ⟨(-1313893330613688274903/2361183241434822606848:ℚ),(-2627786661227376549797/4722366482869645213696:ℚ)⟩ node382 node341
def node384 : BoxExpr 3 := .neg ⟨(2627786661227376549797/4722366482869645213696:ℚ),(1313893330613688274903/2361183241434822606848:ℚ)⟩ node383
def node385 : BoxExpr 3 := .add ⟨(6194590065738819579701/4722366482869645213696:ℚ),(6194590065738819579711/4722366482869645213696:ℚ)⟩ node384 node344
def node386 : BoxExpr 3 := .add ⟨(1121016547445663551779/1180591620717411303424:ℚ),(4484066189782654207127/4722366482869645213696:ℚ)⟩ node385 node346
def node387 : BoxExpr 3 := .neg ⟨(-4484066189782654207127/4722366482869645213696:ℚ),(-1121016547445663551779/1180591620717411303424:ℚ)⟩ node386
def node388 : BoxExpr 3 := .add ⟨(1164387098915155/590295810358705651712:ℚ),(1164387098915159/590295810358705651712:ℚ)⟩ node381 node387
def node389 : BoxExpr 3 := .mul ⟨(2296809993/590295810358705651712:ℚ),(18374479945/4722366482869645213696:ℚ)⟩ node388 node388
def node390 : BoxExpr 3 := .mul ⟨(12249653295/4722366482869645213696:ℚ),(12249653297/4722366482869645213696:ℚ)⟩ node389 node351
def node391 : BoxExpr 3 := .neg ⟨(-12249653297/4722366482869645213696:ℚ),(-12249653295/4722366482869645213696:ℚ)⟩ node390
def node392 : BoxExpr 3 := .add ⟨(534441691364866663/4722366482869645213696:ℚ),(534441691364866765/4722366482869645213696:ℚ)⟩ node377 node391
def node393 : BoxExpr 3 := .mul ⟨(1088759088586179117607/4722366482869645213696:ℚ),(1088759088586179117613/4722366482869645213696:ℚ)⟩ node78 node356
def node394 : BoxExpr 3 := .mul ⟨(80778706244695110407/295147905179352825856:ℚ),(1292459299915121766521/4722366482869645213696:ℚ)⟩ node393 node358
def node395 : BoxExpr 3 := .mul ⟨(4562839122103832873107/2361183241434822606848:ℚ),(570354890262979109141/295147905179352825856:ℚ)⟩ node86 node365
def node396 : BoxExpr 3 := .inv ⟨(2443735643724405560515/4722366482869645213696:ℚ),(2443735643724405560527/4722366482869645213696:ℚ)⟩ node395
def node397 : BoxExpr 3 := .mul ⟨(791984730211546904717/2361183241434822606848:ℚ),(791984730211546904803/2361183241434822606848:ℚ)⟩ node259 node396
def node398 : BoxExpr 3 := .mul ⟨(1254919124171119511875/2361183241434822606848:ℚ),(313729781042779878003/590295810358705651712:ℚ)⟩ node397 node313
def node399 : BoxExpr 3 := .mul ⟨(3764757372513358535625/4722366482869645213696:ℚ),(941189343128339634009/1180591620717411303424:ℚ)⟩ node398 node315
def node400 : BoxExpr 3 := .add ⟨(5057216672428480302137/4722366482869645213696:ℚ),(5057216672428480302557/4722366482869645213696:ℚ)⟩ node394 node399
def node401 : BoxExpr 3 := .neg ⟨(-2390523180487802588601/4722366482869645213696:ℚ),(-1195261590243901294299/2361183241434822606848:ℚ)⟩ node321
def node402 : BoxExpr 3 := .add ⟨(20833542905786544637/36893488147419103232:ℚ),(2666693491940677713959/4722366482869645213696:ℚ)⟩ node400 node401
def node403 : BoxExpr 3 := .mul ⟨(2802680497788877355967/4722366482869645213696:ℚ),(350335062223609669497/590295810358705651712:ℚ)⟩ node77 node328
def node404 : BoxExpr 3 := .neg ⟨(-350335062223609669497/590295810358705651712:ℚ),(-2802680497788877355967/4722366482869645213696:ℚ)⟩ node403
def node405 : BoxExpr 3 := .add ⟨(-16998375731024955305/590295810358705651712:ℚ),(-16998375731024955251/590295810358705651712:ℚ)⟩ node402 node404
def node406 : BoxExpr 3 := .mul ⟨(261671836549905548585/1180591620717411303424:ℚ),(1046687346199622194345/4722366482869645213696:ℚ)⟩ node78 node51
def node407 : BoxExpr 3 := .mul ⟨(1242516190111327313825/4722366482869645213696:ℚ),(1242516190111327313833/4722366482869645213696:ℚ)⟩ node406 node358
def node408 : BoxExpr 3 := .mul ⟨(-629842008015811199081/4722366482869645213696:ℚ),(-314921004007905599539/2361183241434822606848:ℚ)⟩ node77 node299
def node409 : BoxExpr 3 := .mul ⟨(-645550534042431142421/4722366482869645213696:ℚ),(-645550534042431142417/4722366482869645213696:ℚ)⟩ node408 node341
def node410 : BoxExpr 3 := .add ⟨(149241414017224042851/1180591620717411303424:ℚ),(74620707008612021427/590295810358705651712:ℚ)⟩ node407 node409
def node411 : BoxExpr 3 := .mul ⟨(1177543692881121/4722366482869645213696:ℚ),(588771846440563/2361183241434822606848:ℚ)⟩ node410 node388
def node412 : BoxExpr 3 := .mul ⟨(1177543692881121/4722366482869645213696:ℚ),(588771846440563/2361183241434822606848:ℚ)⟩ node388 node410
def node413 : BoxExpr 3 := .add ⟨(1177543692881121/2361183241434822606848:ℚ),(588771846440563/1180591620717411303424:ℚ)⟩ node411 node412
def node414 : BoxExpr 3 := .mul ⟨(1570058257174827/4722366482869645213696:ℚ),(1570058257174835/4722366482869645213696:ℚ)⟩ node413 node351
def node415 : BoxExpr 3 := .neg ⟨(-1570058257174835/4722366482869645213696:ℚ),(-1570058257174827/4722366482869645213696:ℚ)⟩ node414
def node416 : BoxExpr 3 := .add ⟨(-135988575906456817275/4722366482869645213696:ℚ),(-135988575906456816835/4722366482869645213696:ℚ)⟩ node405 node415
def node417 : BoxExpr 3 := .mul ⟨(-231732501165400155461/590295810358705651712:ℚ),(-463465002330800310919/1180591620717411303424:ℚ)⟩ node98 node356
def node418 : BoxExpr 3 := .mul ⟨(-1090494871785071961897/2361183241434822606848:ℚ),(-2180989743570143923785/4722366482869645213696:ℚ)⟩ node68 node299
def node419 : BoxExpr 3 := .add ⟨(-2017424876446672583741/2361183241434822606848:ℚ),(-4034849752893345167461/4722366482869645213696:ℚ)⟩ node417 node418
def node420 : BoxExpr 3 := .mul ⟨(-4789745630191778553813/4722366482869645213696:ℚ),(-4789745630191778553783/4722366482869645213696:ℚ)⟩ node419 node358
def node421 : BoxExpr 3 := .mul ⟨(837779118586525097813/1180591620717411303424:ℚ),(418889559293262548907/590295810358705651712:ℚ)⟩ node54 node54
def node422 : BoxExpr 3 := .inv ⟨(6654721006939080684825/4722366482869645213696:ℚ),(3327360503469540342417/2361183241434822606848:ℚ)⟩ node421
def node423 : BoxExpr 3 := .mul ⟨(-1320952371750932507521/1180591620717411303424:ℚ),(-5283809487003730030073/4722366482869645213696:ℚ)⟩ node85 node422
def node424 : BoxExpr 3 := .neg ⟨(5283809487003730030073/4722366482869645213696:ℚ),(1320952371750932507521/1180591620717411303424:ℚ)⟩ node423
def node425 : BoxExpr 3 := .mul ⟨(4596039974444311034903/4722366482869645213696:ℚ),(4596039974444311034931/4722366482869645213696:ℚ)⟩ node357 node424
def node426 : BoxExpr 3 := .add ⟨(-96852827873733759455/2361183241434822606848:ℚ),(-48426413936866879713/1180591620717411303424:ℚ)⟩ node420 node425
def node427 : BoxExpr 3 := .lit (-4463044196700782098633982290241252447823512137391687473978729294628281428437691326521755513111644247407593234707/225463975179952614733725821671694628524803703608085666091532736804526774315736812953750163508920933689585733468160:ℚ)
def node428 : BoxExpr 3 := .mul ⟨(-101848879827429804921/4722366482869645213696:ℚ),(-101848879827429804919/4722366482869645213696:ℚ)⟩ node427 node69
def node429 : BoxExpr 3 := .mul ⟨(1993042818268369611/4722366482869645213696:ℚ),(1993042818268369613/4722366482869645213696:ℚ)⟩ node362 node103
def node430 : BoxExpr 3 := .add ⟨(-49927918504580717655/2361183241434822606848:ℚ),(-49927918504580717653/2361183241434822606848:ℚ)⟩ node428 node429
def node431 : BoxExpr 3 := .add ⟨(-73390373189157238555/1180591620717411303424:ℚ),(-146780746378314477079/2361183241434822606848:ℚ)⟩ node426 node430
def node432 : BoxExpr 3 := .mul ⟨(29815727108753656529/1180591620717411303424:ℚ),(59631454217507313081/2361183241434822606848:ℚ)⟩ node264 node396
def node433 : BoxExpr 3 := .mul ⟨(188974987635673105093/4722366482869645213696:ℚ),(188974987635673105167/4722366482869645213696:ℚ)⟩ node432 node313
def node434 : BoxExpr 3 := .mul ⟨(283462481453509657639/4722366482869645213696:ℚ),(283462481453509657751/4722366482869645213696:ℚ)⟩ node433 node315
def node435 : BoxExpr 3 := .add ⟨(-10099011303119296581/4722366482869645213696:ℚ),(-10099011303119296407/4722366482869645213696:ℚ)⟩ node431 node434
def node436 : BoxExpr 3 := .mul ⟨(-445555824453289497811/1180591620717411303424:ℚ),(-891111648906578995617/2361183241434822606848:ℚ)⟩ node98 node51
def node437 : BoxExpr 3 := .add ⟨(127575385906830853113/73786976294838206464:ℚ),(4082412349018587299633/2361183241434822606848:ℚ)⟩ node436 node68
def node438 : BoxExpr 3 := .mul ⟨(4846206899112162263611/2361183241434822606848:ℚ),(4846206899112162263635/2361183241434822606848:ℚ)⟩ node437 node358
def node439 : BoxExpr 3 := .mul ⟨(552305020264558514007/590295810358705651712:ℚ),(4418440162116468112081/4722366482869645213696:ℚ)⟩ node378 node424
def node440 : BoxExpr 3 := .add ⟨(7055426980170396319639/2361183241434822606848:ℚ),(14110853960340792639351/4722366482869645213696:ℚ)⟩ node438 node439
def node441 : BoxExpr 3 := .mul ⟨(-95997215671819621621/4722366482869645213696:ℚ),(-95997215671819621619/4722366482869645213696:ℚ)⟩ node308 node103
def node442 : BoxExpr 3 := .add ⟨(14014856744668973017657/4722366482869645213696:ℚ),(3503714186167243254433/1180591620717411303424:ℚ)⟩ node440 node441
def node443 : BoxExpr 3 := .mul ⟨(13822492130445739/2361183241434822606848:ℚ),(13822492130445787/2361183241434822606848:ℚ)⟩ node442 node388
def node444 : BoxExpr 3 := .mul ⟨(13822492130445739/2361183241434822606848:ℚ),(13822492130445787/2361183241434822606848:ℚ)⟩ node388 node442
def node445 : BoxExpr 3 := .add ⟨(13822492130445739/1180591620717411303424:ℚ),(13822492130445787/1180591620717411303424:ℚ)⟩ node443 node444
def node446 : BoxExpr 3 := .mul ⟨(18429989507260985/2361183241434822606848:ℚ),(36859979014522099/4722366482869645213696:ℚ)⟩ node445 node351
def node447 : BoxExpr 3 := .neg ⟨(-36859979014522099/4722366482869645213696:ℚ),(-18429989507260985/2361183241434822606848:ℚ)⟩ node446
def node448 : BoxExpr 3 := .add ⟨(-1266983910266727335/590295810358705651712:ℚ),(-10135871282133818377/4722366482869645213696:ℚ)⟩ node435 node447
def node449 : BoxExpr 3 := .mul ⟨(4394223952712326911979/2361183241434822606848:ℚ),(8823750816018599986525/4722366482869645213696:ℚ)⟩ node112 node302
def node450 : BoxExpr 3 := .mul ⟨(2603283214788987691143/1180591620717411303424:ℚ),(10494453824544824277245/4722366482869645213696:ℚ)⟩ node449 node304
def node451 : BoxExpr 3 := .mul ⟨(4536274346247360302947/2361183241434822606848:ℚ),(143396086432499176873/73786976294838206464:ℚ)⟩ node86 node312
def node452 : BoxExpr 3 := .inv ⟨(607494165977581284235/1180591620717411303424:ℚ),(614511587493020229303/1180591620717411303424:ℚ)⟩ node451
def node453 : BoxExpr 3 := .mul ⟨(5773544633378877665551/4722366482869645213696:ℚ),(7278824091723749418531/2361183241434822606848:ℚ)⟩ node273 node452
def node454 : BoxExpr 3 := .mul ⟨(-1788814595866488887937/4722366482869645213696:ℚ),(-1300318108051035187409/4722366482869645213696:ℚ)⟩ node267 node247
def node455 : BoxExpr 3 := .mul ⟨(-1788814595866488887937/4722366482869645213696:ℚ),(-1300318108051035187409/4722366482869645213696:ℚ)⟩ node247 node267
def node456 : BoxExpr 3 := .add ⟨(-1788814595866488887937/2361183241434822606848:ℚ),(-1300318108051035187409/2361183241434822606848:ℚ)⟩ node454 node455
def node457 : BoxExpr 3 := .neg ⟨(1300318108051035187409/2361183241434822606848:ℚ),(1788814595866488887937/2361183241434822606848:ℚ)⟩ node456
def node458 : BoxExpr 3 := .mul ⟨(1338203068180323083859/4722366482869645213696:ℚ),(931098677770235903287/2361183241434822606848:ℚ)⟩ node457 node452
def node459 : BoxExpr 3 := .mul ⟨(1338203068180323083859/2361183241434822606848:ℚ),(931098677770235903287/1180591620717411303424:ℚ)⟩ node86 node458
def node460 : BoxExpr 3 := .mul ⟨(17430061829438864501847/4722366482869645213696:ℚ),(17835071617619524627047/4722366482869645213696:ℚ)⟩ node451 node451
def node461 : BoxExpr 3 := .inv ⟨(625193598227533752661/2361183241434822606848:ℚ),(639720771410727784235/2361183241434822606848:ℚ)⟩ node460
def node462 : BoxExpr 3 := .mul ⟨(354329124768132112035/2361183241434822606848:ℚ),(1009058770111766312519/4722366482869645213696:ℚ)⟩ node459 node461
def node463 : BoxExpr 3 := .neg ⟨(-1009058770111766312519/4722366482869645213696:ℚ),(-354329124768132112035/2361183241434822606848:ℚ)⟩ node462
def node464 : BoxExpr 3 := .mul ⟨(-191113826363403907023/1180591620717411303424:ℚ),(-390262448979519308889/4722366482869645213696:ℚ)⟩ node457 node463
def node465 : BoxExpr 3 := .add ⟨(5009089327925262037459/4722366482869645213696:ℚ),(14167385734467979528173/4722366482869645213696:ℚ)⟩ node453 node464
def node466 : BoxExpr 3 := .mul ⟨(992128028563097830505/590295810358705651712:ℚ),(5612142071522024316911/1180591620717411303424:ℚ)⟩ node465 node313
def node467 : BoxExpr 3 := .mul ⟨(2976384085689293491515/1180591620717411303424:ℚ),(16836426214566072950733/2361183241434822606848:ℚ)⟩ node466 node315
def node468 : BoxExpr 3 := .add ⟨(2789833650239140591329/590295810358705651712:ℚ),(44167306253676970178711/4722366482869645213696:ℚ)⟩ node450 node467
def node469 : BoxExpr 3 := .mul ⟨(11334338356206420358639/2361183241434822606848:ℚ),(5667169178103210179321/1180591620717411303424:ℚ)⟩ node111 node328
def node470 : BoxExpr 3 := .neg ⟨(-5667169178103210179321/1180591620717411303424:ℚ),(-11334338356206420358639/2361183241434822606848:ℚ)⟩ node469
def node471 : BoxExpr 3 := .add ⟨(-87501877624928996663/1180591620717411303424:ℚ),(21498629541264129461433/4722366482869645213696:ℚ)⟩ node468 node470
def node472 : BoxExpr 3 := .mul ⟨(1051902228298727040855/590295810358705651712:ℚ),(2129118789880716473737/1180591620717411303424:ℚ)⟩ node112 node13
def node473 : BoxExpr 3 := .mul ⟨(4985452619617054574319/2361183241434822606848:ℚ),(10128998106705751877597/4722366482869645213696:ℚ)⟩ node472 node304
def node474 : BoxExpr 3 := .lit (-1348449/1250000:ℚ)
def node475 : BoxExpr 3 := .mul ⟨(-1305337548221994733919/1180591620717411303424:ℚ),(-652668774110997366959/590295810358705651712:ℚ)⟩ node474 node341
def node476 : BoxExpr 3 := .add ⟨(2374777523173065106481/2361183241434822606848:ℚ),(4907647913817772941925/4722366482869645213696:ℚ)⟩ node473 node475
def node477 : BoxExpr 3 := .mul ⟨(-52492116969523811609/4722366482869645213696:ℚ),(26479469483812267759/2361183241434822606848:ℚ)⟩ node476 node349
def node478 : BoxExpr 3 := .mul ⟨(253796037826877572651/1180591620717411303424:ℚ),(1078498353301429433267/4722366482869645213696:ℚ)⟩ node118 node13
def node479 : BoxExpr 3 := .mul ⟨(1202857154964700683927/4722366482869645213696:ℚ),(1282702946237146206481/4722366482869645213696:ℚ)⟩ node478 node304
def node480 : BoxExpr 3 := .mul ⟨(-322562448441656507803/2361183241434822606848:ℚ),(-614559119148309382553/4722366482869645213696:ℚ)⟩ node117 node299
def node481 : BoxExpr 3 := .mul ⟨(-165303646155273769807/1180591620717411303424:ℚ),(-314943241731883602805/2361183241434822606848:ℚ)⟩ node480 node341
def node482 : BoxExpr 3 := .add ⟨(541642570343605604699/4722366482869645213696:ℚ),(652816462773379000871/4722366482869645213696:ℚ)⟩ node479 node481
def node483 : BoxExpr 3 := .mul ⟨(62124927210255660989/4722366482869645213696:ℚ),(11280608345780476701/590295810358705651712:ℚ)⟩ node482 node482
def node484 : BoxExpr 3 := .add ⟨(2408202560182962345/1180591620717411303424:ℚ),(71601902866934174563/2361183241434822606848:ℚ)⟩ node477 node483
def node485 : BoxExpr 3 := .mul ⟨(-52492116969523811609/4722366482869645213696:ℚ),(26479469483812267759/2361183241434822606848:ℚ)⟩ node349 node476
def node486 : BoxExpr 3 := .add ⟨(2408202560182962345/1180591620717411303424:ℚ),(71601902866934174563/2361183241434822606848:ℚ)⟩ node483 node485
def node487 : BoxExpr 3 := .add ⟨(2408202560182962345/590295810358705651712:ℚ),(71601902866934174563/1180591620717411303424:ℚ)⟩ node484 node486
def node488 : BoxExpr 3 := .mul ⟨(12843746987642465839/4722366482869645213696:ℚ),(190938407645157798835/4722366482869645213696:ℚ)⟩ node487 node351
def node489 : BoxExpr 3 := .neg ⟨(-190938407645157798835/4722366482869645213696:ℚ),(-12843746987642465839/4722366482869645213696:ℚ)⟩ node488
def node490 : BoxExpr 3 := .add ⟨(-540945918144873785487/4722366482869645213696:ℚ),(10742892897138243497797/2361183241434822606848:ℚ)⟩ node471 node489
def node491 : BoxExpr 3 := .mul ⟨(-529261691637876830959/4722366482869645213696:ℚ),(-497133970392333970195/4722366482869645213696:ℚ)⟩ node131 node302
def node492 : BoxExpr 3 := .mul ⟨(-592664875357765519403/4722366482869645213696:ℚ),(-563521336600254499685/4722366482869645213696:ℚ)⟩ node118 node299
def node493 : BoxExpr 3 := .add ⟨(-560963283497821175181/2361183241434822606848:ℚ),(-132581913374073558735/590295810358705651712:ℚ)⟩ node491 node492
def node494 : BoxExpr 3 := .mul ⟨(-1334353926959426606843/4722366482869645213696:ℚ),(-1256734379988224827633/4722366482869645213696:ℚ)⟩ node493 node304
def node495 : BoxExpr 3 := .mul ⟨(1060209398287951901529/4722366482869645213696:ℚ),(558705364999347868657/2361183241434822606848:ℚ)⟩ node118 node302
def node496 : BoxExpr 3 := .mul ⟨(834615574371499171719/1180591620717411303424:ℚ),(1681865409382173027303/2361183241434822606848:ℚ)⟩ node16 node16
def node497 : BoxExpr 3 := .inv ⟨(6629765103119255704367/4722366482869645213696:ℚ),(6679945199717854386169/4722366482869645213696:ℚ)⟩ node496
def node498 : BoxExpr 3 := .mul ⟨(-166579910283466975105/147573952589676412928:ℚ),(-1309368896296077729265/1180591620717411303424:ℚ)⟩ node127 node497
def node499 : BoxExpr 3 := .neg ⟨(1309368896296077729265/1180591620717411303424:ℚ),(166579910283466975105/147573952589676412928:ℚ)⟩ node498
def node500 : BoxExpr 3 := .mul ⟨(1175855550148197900749/4722366482869645213696:ℚ),(1261321363875886567177/4722366482869645213696:ℚ)⟩ node495 node499
def node501 : BoxExpr 3 := .add ⟨(-79249188405614353047/2361183241434822606848:ℚ),(573372985957717443/590295810358705651712:ℚ)⟩ node494 node500
def node502 : BoxExpr 3 := .mul ⟨(-969283615700092828965/4722366482869645213696:ℚ),(581545566746038724723/4722366482869645213696:ℚ)⟩ node283 node452
def node503 : BoxExpr 3 := .mul ⟨(-205386967343410209459/4722366482869645213696:ℚ),(-43868757032574204617/4722366482869645213696:ℚ)⟩ node276 node247
def node504 : BoxExpr 3 := .mul ⟨(-205386967343410209459/4722366482869645213696:ℚ),(-43868757032574204617/4722366482869645213696:ℚ)⟩ node247 node276
def node505 : BoxExpr 3 := .add ⟨(-205386967343410209459/2361183241434822606848:ℚ),(-43868757032574204617/2361183241434822606848:ℚ)⟩ node503 node504
def node506 : BoxExpr 3 := .neg ⟨(43868757032574204617/2361183241434822606848:ℚ),(205386967343410209459/2361183241434822606848:ℚ)⟩ node505
def node507 : BoxExpr 3 := .mul ⟨(22573439873969611227/2361183241434822606848:ℚ),(213812581993221889843/4722366482869645213696:ℚ)⟩ node506 node452
def node508 : BoxExpr 3 := .mul ⟨(22573439873969611227/1180591620717411303424:ℚ),(213812581993221889843/2361183241434822606848:ℚ)⟩ node86 node507
def node509 : BoxExpr 3 := .mul ⟨(11953981251030755241/2361183241434822606848:ℚ),(115857462893820929139/4722366482869645213696:ℚ)⟩ node508 node461
def node510 : BoxExpr 3 := .neg ⟨(-115857462893820929139/4722366482869645213696:ℚ),(-11953981251030755241/2361183241434822606848:ℚ)⟩ node509
def node511 : BoxExpr 3 := .mul ⟨(-21943184779952604101/1180591620717411303424:ℚ),(-6583130868984244265/2361183241434822606848:ℚ)⟩ node457 node510
def node512 : BoxExpr 3 := .add ⟨(-1057056354819903245369/4722366482869645213696:ℚ),(568379305008070236193/4722366482869645213696:ℚ)⟩ node502 node511
def node513 : BoxExpr 3 := .mul ⟨(-418732894836173967231/1180591620717411303424:ℚ),(900610873453577394521/4722366482869645213696:ℚ)⟩ node512 node313
def node514 : BoxExpr 3 := .mul ⟨(-1256198684508521901693/2361183241434822606848:ℚ),(675458155090183045891/2361183241434822606848:ℚ)⟩ node513 node315
def node515 : BoxExpr 3 := .add ⟨(-333861968228534063685/590295810358705651712:ℚ),(677751647034013915663/2361183241434822606848:ℚ)⟩ node501 node514
def node516 : BoxExpr 3 := .mul ⟨(-255415420477323205931/2361183241434822606848:ℚ),(-476021556339574343057/4722366482869645213696:ℚ)⟩ node131 node13
def node517 : BoxExpr 3 := .add ⟨(257409335043178604979/590295810358705651712:ℚ),(2227001682544697842489/4722366482869645213696:ℚ)⟩ node516 node118
def node518 : BoxExpr 3 := .mul ⟨(2439964493240824613045/4722366482869645213696:ℚ),(662166430465744970087/1180591620717411303424:ℚ)⟩ node517 node304
def node519 : BoxExpr 3 := .mul ⟨(140739876559414984003/590295810358705651712:ℚ),(1217397486352797551095/4722366482869645213696:ℚ)⟩ node478 node499
def node520 : BoxExpr 3 := .add ⟨(3565883505716144485069/4722366482869645213696:ℚ),(3866063208215777431443/4722366482869645213696:ℚ)⟩ node518 node519
def node521 : BoxExpr 3 := .mul ⟨(-41351345023315870549/4722366482869645213696:ℚ),(41719090098622020015/4722366482869645213696:ℚ)⟩ node520 node349
def node522 : BoxExpr 3 := .mul ⟨(-453273118278718435839/1180591620717411303424:ℚ),(-875830350424963968553/2361183241434822606848:ℚ)⟩ node148 node13
def node523 : BoxExpr 3 := .add ⟨(8099775574355942646867/4722366482869645213696:ℚ),(8229755136731765673741/4722366482869645213696:ℚ)⟩ node522 node36
def node524 : BoxExpr 3 := .mul ⟨(4798574224525665237115/2361183241434822606848:ℚ),(9787990058938676521227/4722366482869645213696:ℚ)⟩ node523 node304
def node525 : BoxExpr 3 := .mul ⟨(4342656949416113091773/4722366482869645213696:ℚ),(2247733274377928443711/2361183241434822606848:ℚ)⟩ node336 node499
def node526 : BoxExpr 3 := .add ⟨(13939805398467443566003/4722366482869645213696:ℚ),(14283456607694533408649/4722366482869645213696:ℚ)⟩ node524 node525
def node527 : BoxExpr 3 := .mul ⟨(-24188744970842064997/1180591620717411303424:ℚ),(-95244833267604147237/4722366482869645213696:ℚ)⟩ node308 node136
def node528 : BoxExpr 3 := .add ⟨(13843050418584075306015/4722366482869645213696:ℚ),(3547052943606732315353/1180591620717411303424:ℚ)⟩ node526 node527
def node529 : BoxExpr 3 := .mul ⟨(49617505315640599959/147573952589676412928:ℚ),(1961367940683960843491/4722366482869645213696:ℚ)⟩ node482 node528
def node530 : BoxExpr 3 := .add ⟨(1546408825077183328139/4722366482869645213696:ℚ),(1001543515391291431753/2361183241434822606848:ℚ)⟩ node521 node529
def node531 : BoxExpr 3 := .mul ⟨(49617505315640599959/147573952589676412928:ℚ),(1961367940683960843491/4722366482869645213696:ℚ)⟩ node528 node482
def node532 : BoxExpr 3 := .mul ⟨(-41351345023315870549/4722366482869645213696:ℚ),(41719090098622020015/4722366482869645213696:ℚ)⟩ node349 node520
def node533 : BoxExpr 3 := .add ⟨(1546408825077183328139/4722366482869645213696:ℚ),(1001543515391291431753/2361183241434822606848:ℚ)⟩ node531 node532
def node534 : BoxExpr 3 := .add ⟨(1546408825077183328139/2361183241434822606848:ℚ),(1001543515391291431753/1180591620717411303424:ℚ)⟩ node530 node533
def node535 : BoxExpr 3 := .mul ⟨(1030939216718122218759/2361183241434822606848:ℚ),(2670782707710110484675/4722366482869645213696:ℚ)⟩ node534 node351
def node536 : BoxExpr 3 := .neg ⟨(-2670782707710110484675/4722366482869645213696:ℚ),(-1030939216718122218759/2361183241434822606848:ℚ)⟩ node535
def node537 : BoxExpr 3 := .add ⟨(-5341678453538382994155/4722366482869645213696:ℚ),(-44148446210513537887/295147905179352825856:ℚ)⟩ node515 node536
def node538 : BoxExpr 3 := .mul ⟨(-969283615700092828965/4722366482869645213696:ℚ),(290772783373019362361/2361183241434822606848:ℚ)⟩ node290 node452
def node539 : BoxExpr 3 := .mul ⟨(-87772739119810416403/4722366482869645213696:ℚ),(-13166261737968488531/4722366482869645213696:ℚ)⟩ node506 node463
def node540 : BoxExpr 3 := .add ⟨(-132132044352487905671/590295810358705651712:ℚ),(568379305008070236191/4722366482869645213696:ℚ)⟩ node538 node539
def node541 : BoxExpr 3 := .mul ⟨(-1674931579344695868923/4722366482869645213696:ℚ),(450305436726788697259/2361183241434822606848:ℚ)⟩ node540 node313
def node542 : BoxExpr 3 := .mul ⟨(-2512397369017043803385/4722366482869645213696:ℚ),(1350916310180366091777/4722366482869645213696:ℚ)⟩ node541 node315
def node543 : BoxExpr 3 := .add ⟨(-2670895745828272509479/4722366482869645213696:ℚ),(1355503294068027831321/4722366482869645213696:ℚ)⟩ node501 node542
def node544 : BoxExpr 3 := .add ⟨(1546408825077183328139/4722366482869645213696:ℚ),(1001543515391291431753/2361183241434822606848:ℚ)⟩ node521 node531
def node545 : BoxExpr 3 := .add ⟨(1546408825077183328139/4722366482869645213696:ℚ),(1001543515391291431753/2361183241434822606848:ℚ)⟩ node529 node532
def node546 : BoxExpr 3 := .add ⟨(1546408825077183328139/2361183241434822606848:ℚ),(1001543515391291431753/1180591620717411303424:ℚ)⟩ node544 node545
def node547 : BoxExpr 3 := .mul ⟨(1030939216718122218759/2361183241434822606848:ℚ),(2670782707710110484675/4722366482869645213696:ℚ)⟩ node546 node351
def node548 : BoxExpr 3 := .neg ⟨(-2670782707710110484675/4722366482869645213696:ℚ),(-1030939216718122218759/2361183241434822606848:ℚ)⟩ node547
def node549 : BoxExpr 3 := .add ⟨(-2670839226769191497077/2361183241434822606848:ℚ),(-706375139368216606197/4722366482869645213696:ℚ)⟩ node543 node548
def node550 : BoxExpr 3 := .mul ⟨(-1979671819833615593679/4722366482869645213696:ℚ),(-482748214596061443655/1180591620717411303424:ℚ)⟩ node175 node302
def node551 : BoxExpr 3 := .mul ⟨(972334111147965704545/4722366482869645213696:ℚ),(996344798581627347317/4722366482869645213696:ℚ)⟩ node148 node299
def node552 : BoxExpr 3 := .add ⟨(-503668854342824944567/2361183241434822606848:ℚ),(-934648059802618427303/4722366482869645213696:ℚ)⟩ node550 node551
def node553 : BoxExpr 3 := .add ⟨(-35003597537684184589/4722366482869645213696:ℚ),(30848369389504460007/2361183241434822606848:ℚ)⟩ node552 node551
def node554 : BoxExpr 3 := .mul ⟨(-41631234348243775745/4722366482869645213696:ℚ),(36689248696024616615/2361183241434822606848:ℚ)⟩ node553 node304
def node555 : BoxExpr 3 := .mul ⟨(-1878509111985814741015/4722366482869645213696:ℚ),(-914675005150967069669/2361183241434822606848:ℚ)⟩ node148 node302
def node556 : BoxExpr 3 := .mul ⟨(-2188525236548162141115/4722366482869645213696:ℚ),(-1086747724044225600859/2361183241434822606848:ℚ)⟩ node36 node299
def node557 : BoxExpr 3 := .add ⟨(-2033517174266988441065/2361183241434822606848:ℚ),(-31272230143674885477/36893488147419103232:ℚ)⟩ node555 node556
def node558 : BoxExpr 3 := .mul ⟨(-4590825176190084704915/4722366482869645213696:ℚ),(-2219735109042811971375/2361183241434822606848:ℚ)⟩ node557 node499
def node559 : BoxExpr 3 := .add ⟨(-1158114102634582120165/1180591620717411303424:ℚ),(-272880732543348419345/295147905179352825856:ℚ)⟩ node554 node558
def node560 : BoxExpr 3 := .mul ⟨(-6679945199717854386169/2361183241434822606848:ℚ),(-6629765103119255704367/2361183241434822606848:ℚ)⟩ node6 node497
def node561 : BoxExpr 3 := .mul ⟨(-3180461652313836233469/4722366482869645213696:ℚ),(-3136728659774582216265/4722366482869645213696:ℚ)⟩ node127 node16
def node562 : BoxExpr 3 := .mul ⟨(-3180461652313836233469/4722366482869645213696:ℚ),(-3136728659774582216265/4722366482869645213696:ℚ)⟩ node16 node127
def node563 : BoxExpr 3 := .add ⟨(-3180461652313836233469/2361183241434822606848:ℚ),(-3136728659774582216265/2361183241434822606848:ℚ)⟩ node561 node562
def node564 : BoxExpr 3 := .mul ⟨(590028884467411410191/1180591620717411303424:ℚ),(1197988875085087826631/2361183241434822606848:ℚ)⟩ node496 node496
def node565 : BoxExpr 3 := .inv ⟨(9307576081183016120093/4722366482869645213696:ℚ),(9449005712093380670143/4722366482869645213696:ℚ)⟩ node564
def node566 : BoxExpr 3 := .mul ⟨(-12727601904181540473775/4722366482869645213696:ℚ),(-12364707717109663220121/4722366482869645213696:ℚ)⟩ node563 node565
def node567 : BoxExpr 3 := .neg ⟨(12364707717109663220121/4722366482869645213696:ℚ),(12727601904181540473775/4722366482869645213696:ℚ)⟩ node566
def node568 : BoxExpr 3 := .mul ⟨(-10156551743744461984359/4722366482869645213696:ℚ),(-9768046647057354004461/4722366482869645213696:ℚ)⟩ node127 node567
def node569 : BoxExpr 3 := .add ⟨(-23516442143180170756697/4722366482869645213696:ℚ),(-23027576853295865413195/4722366482869645213696:ℚ)⟩ node560 node568
def node570 : BoxExpr 3 := .neg ⟨(23027576853295865413195/4722366482869645213696:ℚ),(23516442143180170756697/4722366482869645213696:ℚ)⟩ node569
def node571 : BoxExpr 3 := .mul ⟨(9970078489067801961603/2361183241434822606848:ℚ),(20547885462056974819113/4722366482869645213696:ℚ)⟩ node303 node570
def node572 : BoxExpr 3 := .add ⟨(15349331801945519218291/4722366482869645213696:ℚ),(16108415243971350876363/4722366482869645213696:ℚ)⟩ node558 node571
def node573 : BoxExpr 3 := .add ⟨(10716875391407190737631/4722366482869645213696:ℚ),(11742323523277776166843/4722366482869645213696:ℚ)⟩ node559 node572
def node574 : BoxExpr 3 := .mul ⟨(-24188744970842064997/2361183241434822606848:ℚ),(-23811208316901036809/2361183241434822606848:ℚ)⟩ node427 node136
def node575 : BoxExpr 3 := .mul ⟨(925550689149901125/590295810358705651712:ℚ),(8278325956342458513/4722366482869645213696:ℚ)⟩ node309 node189
def node576 : BoxExpr 3 := .add ⟨(-20486542214242460497/2361183241434822606848:ℚ),(-39344090677459615105/4722366482869645213696:ℚ)⟩ node574 node575
def node577 : BoxExpr 3 := .add ⟨(-22337643592542262747/1180591620717411303424:ℚ),(-86966507311261688723/4722366482869645213696:ℚ)⟩ node574 node576
def node578 : BoxExpr 3 := .add ⟨(10627524817037021686643/4722366482869645213696:ℚ),(1456919626995814309765/590295810358705651712:ℚ)⟩ node573 node577
def node579 : BoxExpr 3 := .mul ⟨(1160004249457568224491/1180591620717411303424:ℚ),(6835586177043948614533/4722366482869645213696:ℚ)⟩ node298 node452
def node580 : BoxExpr 3 := .mul ⟨(-10077834083475730205/4722366482869645213696:ℚ),(-27761838316429707/295147905179352825856:ℚ)⟩ node506 node510
def node581 : BoxExpr 3 := .add ⟨(4629939163746797167759/4722366482869645213696:ℚ),(6835141987630885739221/4722366482869645213696:ℚ)⟩ node579 node580
def node582 : BoxExpr 3 := .mul ⟨(7336251544626037023203/4722366482869645213696:ℚ),(10830449211327405416491/4722366482869645213696:ℚ)⟩ node581 node313
def node583 : BoxExpr 3 := .mul ⟨(2751094329234763883701/1180591620717411303424:ℚ),(16245673816991108124737/4722366482869645213696:ℚ)⟩ node582 node315
def node584 : BoxExpr 3 := .add ⟨(21631902133976077221447/4722366482869645213696:ℚ),(27901030832957622602857/4722366482869645213696:ℚ)⟩ node578 node583
def node585 : BoxExpr 3 := .mul ⟨(-1910732321113732819977/4722366482869645213696:ℚ),(-462246738541751410735/1180591620717411303424:ℚ)⟩ node175 node13
def node586 : BoxExpr 3 := .add ⟨(-3227428549003521858581/2361183241434822606848:ℚ),(-3141801949098384023117/2361183241434822606848:ℚ)⟩ node585 node148
def node587 : BoxExpr 3 := .add ⟨(-10998981874900354614347/4722366482869645213696:ℚ),(-1339777605278316306191/590295810358705651712:ℚ)⟩ node586 node148
def node588 : BoxExpr 3 := .mul ⟨(-13081546590549584244017/4722366482869645213696:ℚ),(-3174913785828667791403/1180591620717411303424:ℚ)⟩ node587 node304
def node589 : BoxExpr 3 := .mul ⟨(4491643858015719925569/2361183241434822606848:ℚ),(9289660189176105528865/4722366482869645213696:ℚ)⟩ node523 node499
def node590 : BoxExpr 3 := .add ⟨(-4098258874518144392879/4722366482869645213696:ℚ),(-3409994954138565636747/4722366482869645213696:ℚ)⟩ node588 node589
def node591 : BoxExpr 3 := .mul ⟨(19093333233487485542533/4722366482869645213696:ℚ),(4958083012743374894681/1180591620717411303424:ℚ)⟩ node336 node570
def node592 : BoxExpr 3 := .add ⟨(28076620949518925393671/4722366482869645213696:ℚ),(29121992240149605107589/4722366482869645213696:ℚ)⟩ node589 node591
def node593 : BoxExpr 3 := .add ⟨(2997295259375097625099/590295810358705651712:ℚ),(12855998643005519735421/2361183241434822606848:ℚ)⟩ node590 node592
def node594 : BoxExpr 3 := .mul ⟨(-190206082535846260895/2361183241434822606848:ℚ),(-187344550916249912729/2361183241434822606848:ℚ)⟩ node308 node189
def node595 : BoxExpr 3 := .add ⟨(11798974954964544239501/2361183241434822606848:ℚ),(3167163523022317455673/590295810358705651712:ℚ)⟩ node593 node594
def node596 : BoxExpr 3 := .mul ⟨(-271007408895828495093/4722366482869645213696:ℚ),(273417527355983222357/4722366482869645213696:ℚ)⟩ node595 node349
def node597 : BoxExpr 3 := .mul ⟨(40579240426721968320537/4722366482869645213696:ℚ),(1332127083993671782723/147573952589676412928:ℚ)⟩ node528 node528
def node598 : BoxExpr 3 := .add ⟨(10077058254456534956361/1180591620717411303424:ℚ),(42901484215153480269493/4722366482869645213696:ℚ)⟩ node596 node597
def node599 : BoxExpr 3 := .mul ⟨(-271007408895828495093/4722366482869645213696:ℚ),(273417527355983222357/4722366482869645213696:ℚ)⟩ node349 node595
def node600 : BoxExpr 3 := .add ⟨(10077058254456534956361/1180591620717411303424:ℚ),(42901484215153480269493/4722366482869645213696:ℚ)⟩ node597 node599
def node601 : BoxExpr 3 := .add ⟨(10077058254456534956361/590295810358705651712:ℚ),(42901484215153480269493/2361183241434822606848:ℚ)⟩ node598 node600
def node602 : BoxExpr 3 := .mul ⟨(13436077672608713275145/1180591620717411303424:ℚ),(7150247369192246711583/590295810358705651712:ℚ)⟩ node601 node351
def node603 : BoxExpr 3 := .neg ⟨(-7150247369192246711583/590295810358705651712:ℚ),(-13436077672608713275145/1180591620717411303424:ℚ)⟩ node602
def node604 : BoxExpr 3 := .add ⟨(-35570076819561896471217/4722366482869645213696:ℚ),(-25843279857477230497723/4722366482869645213696:ℚ)⟩ node584 node603
def cert_tangent : TaylorCertificate3Reduced :=
  { center := ![(66124043/32768000:ℚ), (16261/40960:ℚ), (0/1:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (0/1:ℚ)],
    whole := node354, centerValue := node392, gradient := ![node416, node448, node110],
    hessian := ![![node490, node537, node110], ![node549, node604, node110], ![node110, node110, node110]] }
theorem cert_tangent_check : cert_tangent.check = true := by decide +kernel
theorem cert_tangent_lower_pos : 0 < cert_tangent.lower := by decide +kernel
theorem positive_tangent (A ρ : ℝ)
    (hAlo : (66025739/32768000:ℝ) ≤ A) (hAhi : A ≤ (66222347/32768000:ℝ))
    (hρlo : (404477/1024000:ℝ) ≤ ρ) (hρhi : ρ ≤ (408573/1024000:ℝ)) :
    0 < node354.eval ![A,ρ,0] := by
  apply cert_tangent.positive_sound cert_tangent_check cert_tangent_lower_pos ![A,ρ,0]
  intro i
  fin_cases i
  · norm_num [cert_tangent,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_tangent,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_tangent,Matrix.cons_val_two]
end GaussLocalMaxColoring.Certificate.Case1Constructive.CellTangentAdaptive2Seed16108.Data
end

section
-- Source module: Solutions.GaussLocalMaxNeighborEnvelope

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace GaussLocalMaxColoring.NeighborEnvelope

noncomputable section

def left (k x : ℝ) : ℝ := (max (k-x) 0)^2-x^2

def both (k₁ k₂ x : ℝ) : ℝ := (max (k₁-x) 0)^2+(max (x-k₂) 0)^2-x^2

theorem left_le_affine (k x s : ℝ) (hs : k ≤ s) :
    left k x ≤ s^2-2*s*x := by
  by_cases hx : x ≤ k
  · rw [left,max_eq_left (show 0 ≤ k-x by linarith)]
    have hp := mul_nonneg (show 0 ≤ s-k by linarith) (show 0 ≤ s+k-2*x by linarith)
    nlinarith only [hp]
  · rw [left,max_eq_right (show k-x ≤ 0 by linarith)]
    nlinarith [sq_nonneg (s-x)]

theorem left_at_projection (k z : ℝ) :
    left k z = (max z k)^2-2*(max z k)*z := by
  by_cases hz : z ≤ k
  · rw [left,max_eq_right hz,max_eq_left (show 0 ≤ k-z by linarith)]
    ring
  · rw [left,max_eq_left (show k ≤ z by linarith),max_eq_right (show k-z ≤ 0 by linarith)]
    ring

theorem both_le_affine (k₁ k₂ x s : ℝ) (hs₁ : k₁ ≤ s) (hs₂ : s ≤ k₂) :
    both k₁ k₂ x ≤ s^2-2*s*x := by
  by_cases hx₁ : x ≤ k₁
  · rw [both,max_eq_left (show 0 ≤ k₁-x by linarith),max_eq_right (show x-k₂ ≤ 0 by linarith)]
    have hp := mul_nonneg (show 0 ≤ s-k₁ by linarith) (show 0 ≤ s+k₁-2*x by linarith)
    nlinarith only [hp]
  by_cases hx₂ : k₂ ≤ x
  · rw [both,max_eq_right (show k₁-x ≤ 0 by linarith),max_eq_left (show 0 ≤ x-k₂ by linarith)]
    have hp := mul_nonneg (show 0 ≤ k₂-s by linarith) (show 0 ≤ 2*x-s-k₂ by linarith)
    nlinarith only [hp]
  · rw [both,max_eq_right (show k₁-x ≤ 0 by linarith),max_eq_right (show x-k₂ ≤ 0 by linarith)]
    nlinarith [sq_nonneg (s-x)]

theorem both_at_projection (k₁ k₂ z : ℝ) (hk : k₁ ≤ k₂) :
    both k₁ k₂ z = (min (max z k₁) k₂)^2-2*(min (max z k₁) k₂)*z := by
  by_cases hz₁ : z ≤ k₁
  · rw [both,max_eq_right hz₁,min_eq_left hk,
      max_eq_left (show 0 ≤ k₁-z by linarith),max_eq_right (show z-k₂ ≤ 0 by linarith)]
    ring
  by_cases hz₂ : k₂ ≤ z
  · rw [both,max_eq_left (show k₁ ≤ z by linarith),min_eq_right hz₂,
      max_eq_right (show k₁-z ≤ 0 by linarith),max_eq_left (show 0 ≤ z-k₂ by linarith)]
    ring
  · rw [both,max_eq_left (show k₁ ≤ z by linarith),min_eq_left (show z ≤ k₂ by linarith),
      max_eq_right (show k₁-z ≤ 0 by linarith),max_eq_right (show z-k₂ ≤ 0 by linarith)]
    ring

theorem affine_weighted (s x y a b : ℝ) (hab : a+b=1) :
    a*(s^2-2*s*x)+b*(s^2-2*s*y) = s^2-2*s*(a*x+b*y) := by
  have hb : b=1-a := by linarith
  rw [hb]
  ring

theorem concave_left (k : ℝ) : ConcaveOn ℝ Set.univ (left k) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  let z := a*x+b*y
  let s := max z k
  have hs : k ≤ s := le_max_right _ _
  calc
    a*left k x+b*left k y ≤ a*(s^2-2*s*x)+b*(s^2-2*s*y) :=
      add_le_add (mul_le_mul_of_nonneg_left (left_le_affine k x s hs) ha)
        (mul_le_mul_of_nonneg_left (left_le_affine k y s hs) hb)
    _ = s^2-2*s*z := affine_weighted s x y a b hab
    _ = left k z := (left_at_projection k z).symm

theorem concave_both (k₁ k₂ : ℝ) (hk : k₁ ≤ k₂) :
    ConcaveOn ℝ Set.univ (both k₁ k₂) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  let z := a*x+b*y
  let s := min (max z k₁) k₂
  have hs₁ : k₁ ≤ s := le_min (le_max_right _ _) hk
  have hs₂ : s ≤ k₂ := min_le_right _ _
  calc
    a*both k₁ k₂ x+b*both k₁ k₂ y ≤ a*(s^2-2*s*x)+b*(s^2-2*s*y) :=
      add_le_add (mul_le_mul_of_nonneg_left (both_le_affine k₁ k₂ x s hs₁ hs₂) ha)
        (mul_le_mul_of_nonneg_left (both_le_affine k₁ k₂ y s hs₁ hs₂) hb)
    _ = s^2-2*s*z := affine_weighted s x y a b hab
    _ = both k₁ k₂ z := (both_at_projection k₁ k₂ z hk).symm

end
end GaussLocalMaxColoring.NeighborEnvelope

namespace GaussLocalMaxColoring.NeighborEnvelope
noncomputable section

theorem concave_hinge_quadratic (k₁ k₂ K β : ℝ) (hk : k₁ ≤ k₂)
    (hβ : 0 ≤ β) (hK : β ≤ K) :
    ConcaveOn ℝ Set.univ (fun x =>
      K*(max (k₁-x) 0)^2+β*(max (x-k₂) 0)^2-K*x^2) := by
  have hL := concave_left k₁
  have hB := concave_both k₁ k₂ hk
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  have h₁ := hL.2 hx hy ha hb hab
  have h₂ := hB.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h₁ h₂ ⊢
  have hp₁ := mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr hK)
  have hp₂ := mul_le_mul_of_nonneg_left h₂ hβ
  unfold left at hp₁
  unfold both at hp₂
  nlinarith only [hp₁,hp₂]

def semicircle (x : ℝ) : ℝ := Real.sqrt (1-x^2)

theorem semicircle_le_one (x : ℝ) : semicircle x ≤ 1 := by
  unfold semicircle
  calc
    _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
    _ = 1 := Real.sqrt_one

theorem semicircle_strong_jensen (x y a b : ℝ)
    (hx : x ∈ Set.Icc (-1:ℝ) 1) (hy : y ∈ Set.Icc (-1:ℝ) 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    a*semicircle x+b*semicircle y+(1/2:ℝ)*a*b*(x-y)^2 ≤
      semicircle (a*x+b*y) := by
  have hbEq : b=1-a := by linarith
  subst b
  let z := a*x+(1-a)*y
  let S := a*semicircle x+(1-a)*semicircle y
  have hz : z ∈ Set.Icc (-1:ℝ) 1 := (convex_Icc (-1:ℝ) 1) hx hy ha hb hab
  have hxBase : 0 ≤ 1-x^2 := by
    have hp := mul_nonneg (show 0 ≤ 1-x by linarith [hx.2]) (show 0 ≤ 1+x by linarith [hx.1])
    nlinarith only [hp]
  have hyBase : 0 ≤ 1-y^2 := by
    have hp := mul_nonneg (show 0 ≤ 1-y by linarith [hy.2]) (show 0 ≤ 1+y by linarith [hy.1])
    nlinarith only [hp]
  have hzBase : 0 ≤ 1-z^2 := by
    have hp := mul_nonneg (show 0 ≤ 1-z by linarith [hz.2]) (show 0 ≤ 1+z by linarith [hz.1])
    nlinarith only [hp]
  have hxUnit : x^2+(semicircle x)^2=1 := by
    rw [semicircle,Real.sq_sqrt hxBase]; ring
  have hyUnit : y^2+(semicircle y)^2=1 := by
    rw [semicircle,Real.sq_sqrt hyBase]; ring
  have hzUnit : z^2+(semicircle z)^2=1 := by
    rw [semicircle,Real.sq_sqrt hzBase]; ring
  have hId : (semicircle z)^2-S^2 =
      a*(1-a)*((x-y)^2+(semicircle x-semicircle y)^2) := by
    dsimp only [z,S] at hzUnit ⊢
    linear_combination hzUnit-a*hxUnit-(1-a)*hyUnit
  have hab0 : 0 ≤ a*(1-a) := mul_nonneg ha hb
  have hRight0 : 0 ≤ a*(1-a)*((x-y)^2+(semicircle x-semicircle y)^2) :=
    mul_nonneg hab0 (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hS0 : 0 ≤ S := by
    dsimp only [S]
    exact add_nonneg (mul_nonneg ha (Real.sqrt_nonneg _)) (mul_nonneg hb (Real.sqrt_nonneg _))
  have hz0 : 0 ≤ semicircle z := Real.sqrt_nonneg _
  have hDiff : 0 ≤ semicircle z-S := by
    by_contra hn
    have ht : semicircle z < S := by linarith
    have hp : 0 < (S-semicircle z)*(S+semicircle z) :=
      mul_pos (by linarith) (by linarith)
    nlinarith only [hId,hRight0,hp]
  have hS1 : S ≤ 1 := by
    have hp := add_le_add (mul_le_mul_of_nonneg_left (semicircle_le_one x) ha)
      (mul_le_mul_of_nonneg_left (semicircle_le_one y) hb)
    dsimp only [S]
    nlinarith only [hp]
  have hDrop := mul_nonneg hab0 (sq_nonneg (semicircle x-semicircle y))
  have hNumerator : a*(1-a)*(x-y)^2 ≤ (semicircle z)^2-S^2 := by
    nlinarith only [hId,hDrop]
  have hUpper := mul_nonneg hDiff
    (show 0 ≤ 2-(semicircle z+S) by linarith [semicircle_le_one z])
  change S+(1/2:ℝ)*a*(1-a)*(x-y)^2 ≤ semicircle z
  nlinarith only [hNumerator,hUpper]

end
end GaussLocalMaxColoring.NeighborEnvelope

namespace GaussLocalMaxColoring.NeighborEnvelope
noncomputable section

theorem variance_identity (x y a b : ℝ) (hab : a+b=1) :
    a*x^2+b*y^2-(a*x+b*y)^2=a*b*(x-y)^2 := by
  have hb : b=1-a := by linarith
  rw [hb]
  ring

theorem concave_semicircle_quadratic (F K : ℝ) (hK : 0 ≤ K) (hFK : 2*K ≤ F) :
    ConcaveOn ℝ (Set.Icc (-1:ℝ) 1) (fun x => F*semicircle x+K*x^2) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hj := semicircle_strong_jensen x y a b hx hy ha hb hab
  have hF : 0 ≤ F := by linarith
  have hm := mul_le_mul_of_nonneg_left hj hF
  have hv := variance_identity x y a b hab
  have hvK := congrArg (fun v : ℝ => K*v) hv
  have hp := mul_nonneg (show 0 ≤ F-2*K by linarith)
    (mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x-y)))
  nlinarith only [hm,hvK,hp]

theorem convex_hinge_left (k : ℝ) : ConvexOn ℝ Set.univ (fun x => max (k-x) 0) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  apply max_le
  · have hx : k-x ≤ max (k-x) 0 := le_max_left _ _
    have hy : k-y ≤ max (k-y) 0 := le_max_left _ _
    have h := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    have hbEq : b=1-a := by linarith
    rw [hbEq] at h ⊢
    nlinarith only [h]
  · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))

theorem convex_hinge_right (k : ℝ) : ConvexOn ℝ Set.univ (fun x => max (x-k) 0) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  apply max_le
  · have hx : x-k ≤ max (x-k) 0 := le_max_left _ _
    have hy : y-k ≤ max (y-k) 0 := le_max_left _ _
    have h := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    have hbEq : b=1-a := by linarith
    rw [hbEq] at h ⊢
    nlinarith only [h]
  · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))

end
end GaussLocalMaxColoring.NeighborEnvelope
end

section
-- Source module: Solutions.GaussLocalMaxNeighborConcavity

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.NeighborEnvelope
noncomputable section

theorem ftilde_uniform_lower (A : ℝ) : (1201/500:ℝ) ≤ ftilde A := by
  unfold ftilde
  have hs := sq_nonneg (A-2+(13/123:ℝ))
  nlinarith only [hs]

theorem fA_quad_decomposition (A r : ℝ) (hr : r ≤ (1/4:ℝ)) :
    fA A r+(3/8:ℝ)*r^2 =
      (ftilde A*semicircle r+(1201/1000:ℝ)*r^2)+
      ((413/500:ℝ)*(max (-(1/40)-r) 0)^2+(9/20:ℝ)*(max (r-1/50) 0)^2-(413/500:ℝ)*r^2)-
      (357/500:ℝ)*max (-(1/40)-r) 0-(4/5:ℝ)*max (r-1/50) 0 := by
  have hz : max (r-(1/4:ℝ)) 0=0 := max_eq_right (by linarith)
  simp only [fA,hz,semicircle]
  ring

/-- Uniform strong concavity of the exact public threshold below the third hinge. -/
theorem fA_strong_concave_left (A : ℝ) :
    ConcaveOn ℝ (Set.Icc (-(1/2):ℝ) (1/4)) (fun r => fA A r+(3/8:ℝ)*r^2) := by
  have hF := ftilde_uniform_lower A
  have hH := concave_semicircle_quadratic (ftilde A) (1201/1000:ℝ) (by norm_num) (by linarith)
  have hQ := concave_hinge_quadratic (-(1/40):ℝ) (1/50) (413/500) (9/20)
    (by norm_num) (by norm_num) (by norm_num)
  have hZ₁ := convex_hinge_left (-(1/40):ℝ)
  have hZ₂ := convex_hinge_right (1/50:ℝ)
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  have hz : a*x+b*y ∈ Set.Icc (-(1/2):ℝ) (1/4) := (convex_Icc _ _) hx hy ha hb hab
  have hx₁ : x ∈ Set.Icc (-1:ℝ) 1 := ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hy₁ : y ∈ Set.Icc (-1:ℝ) 1 := ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hh := hH.2 hx₁ hy₁ ha hb hab
  have hq := hQ.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  have hz₁ := hZ₁.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  have hz₂ := hZ₂.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  simp only [smul_eq_mul] at hh hq hz₁ hz₂ ⊢
  rw [fA_quad_decomposition A x hx.2,fA_quad_decomposition A y hy.2,
    fA_quad_decomposition A (a*x+b*y) hz.2]
  have hp₁ := mul_le_mul_of_nonneg_left hz₁ (show 0 ≤ (357/500:ℝ) by norm_num)
  have hp₂ := mul_le_mul_of_nonneg_left hz₂ (show 0 ≤ (4/5:ℝ) by norm_num)
  nlinarith only [hh,hq,hp₁,hp₂]

end
end GaussLocalMaxColoring.Main
end

section
-- Source module: Solutions.GaussLocalMaxNeighborLocalization

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace GaussLocalMaxColoring.NeighborEnvelope
noncomputable section

/-- A convex function cannot attain a smaller value outside a bracket whose
middle sample is below both endpoints. -/
theorem convex_lower_from_central {g : ℝ → ℝ} {S : Set ℝ}
    (hg : ConvexOn ℝ S g) (u v w δ : ℝ)
    (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S)
    (huv : u < v) (hvw : v < w)
    (hleft : g v ≤ g u) (hright : g v ≤ g w)
    (hcenter : ∀ x ∈ Set.Icc u w, δ ≤ g x) :
    ∀ x ∈ S, δ ≤ g x := by
  intro x hx
  by_cases hxu : x < u
  · have hs := hg.slope_mono_adjacent hx hv hxu huv
    have hn : (g v-g u)/(v-u) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hleft) (by linarith)
    have hp : g u-g x ≤ 0 := by
      have ht := (div_le_iff₀ (show 0 < u-x by linarith)).mp (hs.trans hn)
      simpa only [zero_mul] using ht
    exact (hcenter u ⟨le_rfl,by linarith⟩).trans (by linarith)
  by_cases hwx : w < x
  · have hs := hg.slope_mono_adjacent hv hx hvw hwx
    have hn : 0 ≤ (g w-g v)/(w-v) :=
      div_nonneg (sub_nonneg.mpr hright) (by linarith)
    have hp : 0 ≤ g x-g w := by
      have ht := (le_div_iff₀ (show 0 < x-w by linarith)).mp (hn.trans hs)
      simpa only [zero_mul] using ht
    exact (hcenter w ⟨by linarith,le_rfl⟩).trans (by linarith)
  exact hcenter x ⟨by linarith,by linarith⟩

end
end GaussLocalMaxColoring.NeighborEnvelope

namespace GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.NeighborEnvelope
noncomputable section

theorem fA_concave_left (A : ℝ) :
    ConcaveOn ℝ (Set.Icc (-(1/2):ℝ) (1/4)) (fA A) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  have h := (fA_strong_concave_left A).2 hx hy ha hb hab
  have hv := variance_identity x y a b hab
  have hp := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x-y))
  simp only [smul_eq_mul] at h ⊢
  nlinarith only [h,hv,hp]

theorem affine_sub_fA_convex_left (A K T : ℝ) :
    ConvexOn ℝ (Set.Icc (-(1/2):ℝ) (1/4)) (fun r => K+T*r-fA A r) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  have h := (fA_concave_left A).2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have he : K+T*(a*x+b*y) = a*(K+T*x)+b*(K+T*y) := by
    have hbEq : b=1-a := by linarith
    rw [hbEq]
    ring
  linarith only [h,he]

theorem affine_sub_fA_lower_from_central (A K T u v w δ : ℝ)
    (hu : u ∈ Set.Icc (-(1/2):ℝ) (1/4))
    (hv : v ∈ Set.Icc (-(1/2):ℝ) (1/4))
    (hw : w ∈ Set.Icc (-(1/2):ℝ) (1/4))
    (huv : u < v) (hvw : v < w)
    (hleft : T*(u-v)-fA A u+fA A v ≥ 0)
    (hright : T*(w-v)-fA A w+fA A v ≥ 0)
    (hcenter : ∀ r ∈ Set.Icc u w, fA A r+δ ≤ K+T*r) :
    ∀ r ∈ Set.Icc (-(1/2):ℝ) (1/4), fA A r+δ ≤ K+T*r := by
  have h := convex_lower_from_central (affine_sub_fA_convex_left A K T)
    u v w δ hu hv hw huv hvw (by linarith : K+T*v-fA A v ≤ K+T*u-fA A u)
    (by linarith : K+T*v-fA A v ≤ K+T*w-fA A w)
    (by intro r hr; have hc := hcenter r hr; linarith)
  intro r hr
  have he := h r hr
  linarith

end
end GaussLocalMaxColoring.Main
end

section
-- Source module: Solutions.GaussLocalMaxNeighborTangent

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace GaussLocalMaxColoring.NeighborEnvelope
noncomputable section

theorem convex_support_of_hasDerivAt {g : ℝ → ℝ} {S : Set ℝ}
    (hg : ConvexOn ℝ S g) {s d : ℝ} (hs : s ∈ S)
    (hd : HasDerivAt g d s) {r : ℝ} (hr : r ∈ S) :
    g s+d*(r-s) ≤ g r := by
  rcases lt_trichotomy r s with hrs | rfl | hsr
  · have h := hg.slope_le_of_hasDerivAt hr hs hrs hd
    rw [slope_def_field] at h
    have hp := (div_le_iff₀ (show 0 < s-r by linarith)).mp h
    linarith
  · simp
  · have h := hg.le_slope_of_hasDerivAt hs hr hsr hd
    rw [slope_def_field] at h
    have hp := (le_div_iff₀ (show 0 < r-s by linarith)).mp h
    linarith

end
end GaussLocalMaxColoring.NeighborEnvelope

namespace GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.NeighborEnvelope
noncomputable section

theorem affine_sub_fA_strong_convex_left (A K T : ℝ) :
    ConvexOn ℝ (Set.Icc (-(1/2):ℝ) (1/4))
      (fun r => K+T*r-fA A r-(3/8:ℝ)*r^2) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  have h := (fA_strong_concave_left A).2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have he : K+T*(a*x+b*y) = a*(K+T*x)+b*(K+T*y) := by
    have hbEq : b=1-a := by linarith
    rw [hbEq]
    ring
  linarith only [h,he]

theorem affine_sub_fA_lower_from_tangent (A K T s d : ℝ)
    (hs : s ∈ Set.Icc (-(1/2):ℝ) (1/4))
    (hd : HasDerivAt (fun r => K+T*r-fA A r) d s) :
    ∀ r ∈ Set.Icc (-(1/2):ℝ) (1/4),
      K+T*s-fA A s-(2/3:ℝ)*d^2 ≤ K+T*r-fA A r := by
  have hderiv : HasDerivAt (fun r => K+T*r-fA A r-(3/8:ℝ)*r^2)
      (d-(3/4:ℝ)*s) s := by
    convert! hd.sub (((hasDerivAt_id s).pow 2).const_mul (3/8:ℝ)) using 1 <;>
      (try simp only [id_eq]) <;> ring
  intro r hr
  have hp := convex_support_of_hasDerivAt (affine_sub_fA_strong_convex_left A K T) hs hderiv hr
  have hsquare := sq_nonneg (r-s+(4/3:ℝ)*d)
  nlinarith only [hp,hsquare]

def fA_left_derivative (A s : ℝ) : ℝ :=
  -(ftilde A*s/Real.sqrt (1-s^2))+(7553/10000:ℝ)+(413/250:ℝ)*s

theorem fA_hasDerivAt_left (A s : ℝ) (hslo : -(1/2:ℝ) < s)
    (hshi : s < -(1/40:ℝ)) : HasDerivAt (fA A) (fA_left_derivative A s) s := by
  have hbase : 0 < 1-s^2 := by
    have hp := mul_pos (show 0 < 1-s by linarith) (show 0 < 1+s by linarith)
    nlinarith only [hp]
  have hsqrt := (((hasDerivAt_const s (1:ℝ)).sub ((hasDerivAt_id s).pow 2)).sqrt (ne_of_gt hbase)).const_mul (ftilde A)
  have hz := (hasDerivAt_const s (-(1/40:ℝ))).sub (hasDerivAt_id s)
  have heq : fA A =ᶠ[nhds s] (fun r =>
      ftilde A*Real.sqrt (1-r^2)-(357/500:ℝ)*(-(1/40:ℝ)-r)+
        (413/500:ℝ)*(-(1/40:ℝ)-r)^2) := by
    filter_upwards [eventually_lt_nhds hshi] with r hr
    have h₁ : max (-(1/40:ℝ)-r) 0=-(1/40:ℝ)-r := max_eq_left (by linarith)
    have h₂ : max (r-(1/50:ℝ)) 0=0 := max_eq_right (by linarith)
    have h₃ : max (r-(1/4:ℝ)) 0=0 := max_eq_right (by linarith)
    simp only [fA,h₁,h₂,h₃]
    ring
  have hd := (hsqrt.sub (hz.const_mul (357/500:ℝ))).add ((hz.pow 2).const_mul (413/500:ℝ))
  have ht := hd.congr_of_eventuallyEq heq
  convert! ht using 1
  unfold fA_left_derivative
  simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
  ring

theorem affine_sub_fA_lower_from_left_sample (A K T s : ℝ)
    (hslo : -(1/2:ℝ) < s) (hshi : s < -(1/40:ℝ)) :
    ∀ r ∈ Set.Icc (-(1/2):ℝ) (1/4),
      K+T*s-fA A s-(2/3:ℝ)*(T-fA_left_derivative A s)^2 ≤ K+T*r-fA A r := by
  apply affine_sub_fA_lower_from_tangent A K T s (T-fA_left_derivative A s)
    ⟨hslo.le,by linarith⟩
  convert! ((hasDerivAt_const s K).add ((hasDerivAt_id s).const_mul T)).sub
    (fA_hasDerivAt_left A s hslo hshi) using 1 <;> (try simp only [id_eq]) <;> ring

end
end GaussLocalMaxColoring.Main
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
-- Source module: Solutions.GaussLocalMaxNeighborTangentPatterns

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace GaussLocalMaxColoring.Certificate.NeighborTangentSyntax
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate.CapacityCore
open ThinConstructiveSyntax
noncomputable section

def ftildePattern : CertificateFormula 3 :=
  let A := CertificateFormula.var 0
  let d := .add A (.neg (.lit 2))
  .add (.add (.mul A (.lit (13/25))) (.lit (713/500)))
    (.mul (.mul d d) (.lit (123/50)))

def slopePattern (fj : ℕ) (b c θ σ : ℚ) : CertificateFormula 3 :=
  let base : CertificateFormula 3 := .add (.lit 1) (.neg (.mul (.var 1) (.var 1)))
  .add (.mul (.mul (sourceFAPattern (.var 0) (.var 1) fj) (.var 1)) (.inv base))
    (.mul (.lit (-(1+θ)*b+σ*(θ*c))) (.inv (.sqrt base)))

def derivativePattern (s : ℚ) : CertificateFormula 3 :=
  .add (.add (.neg (.mul (.mul ftildePattern (.lit s))
    (.inv (.sqrt (.lit (1-s*s)))))) (.lit (7553/10000))) (.lit ((413/250)*s))

def tangentGap (fj cj : ℕ) (b c θ σ s : ℚ) : CertificateFormula 3 :=
  let d := .add (slopePattern fj b c θ σ) (.neg (derivativePattern s))
  .add ((gap fj cj 0 b c θ σ).subst ![.var 0,.var 1,.lit s])
    (.neg (.mul (.lit (2/3)) (.mul d d)))

def signedSlope (A ρ b c θ σ : ℝ) : ℝ :=
  fA A ρ*ρ/(1-ρ^2)+(-((1+θ)*b)+σ*(θ*c))/Real.sqrt (1-ρ^2)

theorem ftildePattern_eval (A ρ r : ℝ) :
    ftildePattern.eval (point A ρ r)=ftilde A := by
  norm_num [ftildePattern,CertificateFormula.eval,point,ftilde]
  ring

theorem slopePattern_eval (fj : ℕ) (b c θ σ : ℚ) (A ρ r : ℝ)
    (hf : sourceFADomain fj ρ) :
    (slopePattern fj b c θ σ).eval (point A ρ r)=
      signedSlope A ρ (b:ℝ) (c:ℝ) (θ:ℝ) (σ:ℝ) := by
  have h := sourceFAPattern_eval (.var 0 : CertificateFormula 3) (.var 1) fj (point A ρ r) hf
  change (sourceFAPattern (.var 0) (.var 1) fj).eval (point A ρ r)=fA A ρ at h
  simp only [slopePattern,CertificateFormula.eval]
  rw [h]
  simp only [signedSlope,Rat.cast_add,Rat.cast_neg,Rat.cast_mul,Rat.cast_one,
    div_eq_mul_inv,pow_two,sub_eq_add_neg,point,Matrix.cons_val_zero,Matrix.cons_val_one,neg_mul]

theorem derivativePattern_eval (s : ℚ) (A ρ r : ℝ) :
    (derivativePattern s).eval (point A ρ r)=fA_left_derivative A (s:ℝ) := by
  change -((ftildePattern.eval (point A ρ r)*(s:ℝ))*
    (Real.sqrt ((1-s*s:ℚ):ℝ))⁻¹)+((7553/10000:ℚ):ℝ)+(((413/250)*s:ℚ):ℝ)=_
  rw [ftildePattern_eval]
  norm_num only [Rat.cast_sub,Rat.cast_mul,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat]
  unfold fA_left_derivative
  ring

theorem subst_sample_eval (e : CertificateFormula 3) (s : ℚ) (A ρ r : ℝ) :
    (e.subst ![.var 0,.var 1,.lit s]).eval (point A ρ r)=e.eval (point A ρ (s:ℝ)) := by
  rw [CertificateFormula.subst_eval]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem tangentGap_eval (fj cj : ℕ) (b c θ σ s : ℚ) (A ρ r : ℝ)
    (hf : sourceFADomain fj ρ) (hs : (s:ℝ) ≤ -(1/40:ℝ)) (hbase : 0 < 1-ρ^2) :
    (tangentGap fj cj b c θ σ s).eval (point A ρ r)=
      l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2))
        (constructedA (b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2))
          (thresholdCapacity cj ρ+1/4) (c:ℝ) (θ:ℝ))) (b:ℝ) (c:ℝ) (θ:ℝ) (σ:ℝ) (s:ℝ)-
            3/10^6-fA A (s:ℝ)-
          (2/3:ℝ)*(signedSlope A ρ (b:ℝ) (c:ℝ) (θ:ℝ) (σ:ℝ)-fA_left_derivative A (s:ℝ))^2 := by
  have hk : sourceFADomain 0 (s:ℝ) := Or.inl ⟨rfl,hs⟩
  change ((gap fj cj 0 b c θ σ).subst ![.var 0,.var 1,.lit s]).eval (point A ρ r)+
    -(((2/3:ℚ):ℝ)*(((slopePattern fj b c θ σ).eval (point A ρ r)+
      -((derivativePattern s).eval (point A ρ r)))*
      ((slopePattern fj b c θ σ).eval (point A ρ r)+
      -((derivativePattern s).eval (point A ρ r)))))=_
  rw [subst_sample_eval,gap_eval fj cj 0 b c θ σ A ρ (s:ℝ) hf hk hbase,
    slopePattern_eval fj b c θ σ A ρ r hf,derivativePattern_eval]
  norm_num only [Rat.cast_div,Rat.cast_ofNat]
  ring

theorem scaled_affine (A ρ θ sa sb sc σ r : ℝ) :
    case1ScaledLhs A ρ r θ sa sb sc σ=
      case1ScaledLhs A ρ 0 θ sa sb sc σ+
        (fA A ρ*ρ/(1-ρ^2)+(-sb+σ*sc)/Real.sqrt (1-ρ^2))*r := by
  unfold case1ScaledLhs
  ring

theorem signed_tangent_lower (A ρ a b c θ σ s : ℝ) (hbase : 0 < 1-ρ^2)
    (hslo : -(1/2:ℝ) < s) (hshi : s < -(1/40:ℝ))
    (r : ℝ) (hr : r ∈ Set.Icc (-(1/2):ℝ) (1/4)) :
    l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) a b c θ σ s-fA A s-
      (2/3:ℝ)*(signedSlope A ρ b c θ σ-fA_left_derivative A s)^2 ≤
        l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) a b c θ σ r-fA A r := by
  have h := affine_sub_fA_lower_from_left_sample A
    (case1ScaledLhs A ρ 0 θ ((1+θ)*a) ((1+θ)*b) (θ*c) σ)
    (signedSlope A ρ b c θ σ) s hslo hshi r hr
  unfold signedSlope at h
  rw [← scaled_affine A ρ θ ((1+θ)*a) ((1+θ)*b) (θ*c) σ s,
      ← scaled_affine A ρ θ ((1+θ)*a) ((1+θ)*b) (θ*c) σ r] at h
  rw [signed_bridge A ρ s a b c θ σ hbase,signed_bridge A ρ r a b c θ σ hbase] at h
  exact h

end
end GaussLocalMaxColoring.Certificate.NeighborTangentSyntax
end

section
-- Source module: Solutions.GaussLocalMaxCase1FamilyTangentAdaptive2Seed16108Semantics
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellTangentAdaptive2Seed16108
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate.CapacityCore
noncomputable section
namespace Parameters
def b : ℚ := (44490246235455727562171925126916054015955403303/3071862531100574555014005683424734134759560577024:ℚ)
def c : ℚ := (33610536730032291021/1180591620717411303424:ℚ)
def theta : ℚ := (266732711456819402766503272231896970748968762053683/456324345907579086572258966178089783278423978885120:ℚ)
def sample : ℚ := (-10963/50000:ℚ)
end Parameters

theorem static_shape0 : Data.node43.formula.canonicalize = (ThinConstructiveSyntax.massRad 3 4).canonicalize := by decide +kernel

theorem static_bound0 (A ρ : ℝ) (hAlo : (66025739/32768000:ℝ) ≤ A) (hAhi : A ≤ (66222347/32768000:ℝ))
    (hρlo : (404477/1024000:ℝ) ≤ ρ) (hρhi : ρ ≤ (408573/1024000:ℝ)) : 0 < (thresholdCapacity 4 ρ+1/4)-(fA A ρ/Real.sqrt (1-ρ^2))^2+1/10^18 := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have he := ThinConstructiveSyntax.reflect_massRad Data.node43 3 4 static_shape0 A ρ 0 hf
  have hp := Data.positive_static0 A ρ hAlo hAhi hρlo hρhi
  change 0 < Data.node43.eval (ThinConstructiveSyntax.point A ρ 0) at hp
  rw [he] at hp
  exact hp

theorem static_shape1 : Data.node206.formula.canonicalize = (ThinConstructiveSyntax.muNumer 3 4 Parameters.c Parameters.theta).canonicalize := by decide +kernel

theorem static_bound1 (A ρ : ℝ) (hAlo : (66025739/32768000:ℝ) ≤ A) (hAhi : A ≤ (66222347/32768000:ℝ))
    (hρlo : (404477/1024000:ℝ) ≤ ρ) (hρhi : ρ ≤ (408573/1024000:ℝ)) : 0 < constructedMass (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4)-(Parameters.theta:ℝ)*constructedKappa (Parameters.c:ℝ) := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have he := ThinConstructiveSyntax.reflect_muNumer Data.node206 3 4 Parameters.c Parameters.theta static_shape1 A ρ 0 hf
  have hp := Data.positive_static1 A ρ hAlo hAhi hρlo hρhi
  change 0 < Data.node206.eval (ThinConstructiveSyntax.point A ρ 0) at hp
  rw [he] at hp
  exact hp

theorem static_shape2 : Data.node250.formula.canonicalize = (ThinConstructiveSyntax.aRad 3 4 Parameters.b Parameters.c Parameters.theta).canonicalize := by decide +kernel

theorem static_bound2 (A ρ : ℝ) (hAlo : (66025739/32768000:ℝ) ≤ A) (hAhi : A ≤ (66222347/32768000:ℝ))
    (hρlo : (404477/1024000:ℝ) ≤ ρ) (hρhi : ρ ≤ (408573/1024000:ℝ)) : 0 < 1-1/10^12-(Parameters.b:ℝ)^2-(constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))^2 := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have he := ThinConstructiveSyntax.reflect_aRad Data.node250 3 4 Parameters.b Parameters.c Parameters.theta static_shape2 A ρ 0 hf
  have hp := Data.positive_static2 A ρ hAlo hAhi hρlo hρhi
  change 0 < Data.node250.eval (ThinConstructiveSyntax.point A ρ 0) at hp
  rw [he] at hp
  exact hp

theorem static_conditions (A ρ : ℝ) (hAlo : (66025739/32768000:ℝ) ≤ A) (hAhi : A ≤ (66222347/32768000:ℝ))
    (hρlo : (404477/1024000:ℝ) ≤ ρ) (hρhi : ρ ≤ (408573/1024000:ℝ)) : Case2Static (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ)) (Parameters.c:ℝ) (constructedKappa (Parameters.c:ℝ)) (Parameters.theta:ℝ) ∧
    capacity Da ρ+1/4+1/10^18 ≤ (fA A ρ/Real.sqrt (1-ρ^2))^2+((constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))+(Parameters.theta:ℝ)*((constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))+constructedKappa (Parameters.c:ℝ)))^2 := by
  have hc : 0 ≤ (Parameters.c:ℝ) := by norm_num [Parameters.c]
  have hθ : 0 < (Parameters.theta:ℝ) := by norm_num [Parameters.theta]
  have hθ14 : (Parameters.theta:ℝ) < 14 := by norm_num [Parameters.theta]
  have hk : 0 ≤ (1/4:ℝ)-(Parameters.c:ℝ)^2-1/10^20 := by norm_num [Parameters.c]
  have hMr := (static_bound0 A ρ hAlo hAhi hρlo hρhi).le
  have hM : (Parameters.theta:ℝ)*constructedKappa (Parameters.c:ℝ) ≤
      constructedMass (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) := by
    have h := static_bound1 A ρ hAlo hAhi hρlo hρhi; linarith
  have ha := (static_bound2 A ρ hAlo hAhi hρlo hρhi).le
  have hd : thresholdCapacityDomain 4 ρ := by norm_num [thresholdCapacityDomain] <;> linarith
  have hJ : capacity Da ρ+1/4 ≤ (thresholdCapacity 4 ρ+1/4) := by
    have h := thresholdCapacity_upper 4 ρ hd; linarith
  exact ⟨constructed_static (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) hc hθ hθ14 hk hM ha,
    constructed_iii_of_upper (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (capacity Da ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ) hθ hMr hJ⟩


theorem tangent_shape : Data.node354.formula.canonicalize =
    (NeighborTangentSyntax.tangentGap 3 4 Parameters.b Parameters.c Parameters.theta (-1) Parameters.sample).canonicalize := by decide +kernel

theorem tangent_bound (A ρ : ℝ) (hAlo : (66025739/32768000:ℝ) ≤ A) (hAhi : A ≤ (66222347/32768000:ℝ))
    (hρlo : (404477/1024000:ℝ) ≤ ρ) (hρhi : ρ ≤ (408573/1024000:ℝ)) :
    0 < l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) (Parameters.sample:ℝ)-3/10^6-fA A (Parameters.sample:ℝ)-
      (2/3:ℝ)*(NeighborTangentSyntax.signedSlope A ρ (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1)-fA_left_derivative A (Parameters.sample:ℝ))^2 := by
  have hf : sourceFADomain 3 ρ := by norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by
    have hp := mul_pos (show 0 < 1-ρ by linarith) (show 0 < 1+ρ by linarith)
    nlinarith only [hp]
  have he := CertificateFormula.eval_eq_of_canonicalize_eq _ _ tangent_shape
    (ThinConstructiveSyntax.point A ρ 0)
  rw [NeighborTangentSyntax.tangentGap_eval 3 4 Parameters.b Parameters.c Parameters.theta (-1)
    Parameters.sample A ρ 0 hf (by norm_num [Parameters.sample]) hbase] at he
  have hp := Data.positive_tangent A ρ hAlo hAhi hρlo hρhi
  change 0 < Data.node354.eval (ThinConstructiveSyntax.point A ρ 0) at hp
  rw [← BoxExpr.formula_eval] at hp
  rw [he] at hp
  simp only [Rat.cast_neg,Rat.cast_one] at hp
  exact hp

theorem children_cover (A ρ : ℝ) (hAlo : (66025739/32768000:ℝ) ≤ A) (hAhi : A ≤ (66222347/32768000:ℝ))
    (hρlo : (404477/1024000:ℝ) ≤ ρ) (hρhi : ρ ≤ (408573/1024000:ℝ)) (r : ℝ)
    (hrlo : -(1/2:ℝ) ≤ r) (hrhi : r ≤ 1/2-ρ) :
    fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hbase : 0 < 1-ρ^2 := by
    have hp := mul_pos (show 0 < 1-ρ by linarith) (show 0 < 1+ρ by linarith)
    nlinarith only [hp]
  have hp := tangent_bound A ρ hAlo hAhi hρlo hρhi
  have ht := NeighborTangentSyntax.signed_tangent_lower A ρ (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ)
    (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) (Parameters.sample:ℝ) hbase
    (by norm_num [Parameters.sample]) (by norm_num [Parameters.sample]) r ⟨hrlo,by linarith⟩
  linarith

theorem rectangle (A ρ : ℝ) (hAlo : (66025739/32768000:ℝ) ≤ A) (hAhi : A ≤ (66222347/32768000:ℝ))
    (hρlo : (404477/1024000:ℝ) ≤ ρ) (hρhi : ρ ≤ (408573/1024000:ℝ)) (hcase : qA A ρ < qc ρ) :
    L40Case1 A ρ (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))
      (Parameters.c:ℝ) (constructedKappa (Parameters.c:ℝ)) (Parameters.theta:ℝ) ∧
      0 < qA A ρ/Real.sqrt (1-ρ^2) := by
  have hstat := static_conditions A ρ hAlo hAhi hρlo hρhi
  have hq : qA A ρ = fA A ρ := by
    unfold qA at hcase ⊢
    by_cases h : qc ρ ≤ fA A ρ
    · rw [min_eq_left h] at hcase
      exact (lt_irrefl _ hcase).elim
    · exact min_eq_right (by linarith)
  have hbase : 0 < 1-ρ^2 := by
    have hp := mul_pos (show 0 < 1-ρ by linarith) (show 0 < 1+ρ by linarith)
    nlinarith only [hp]
  have hθ : 0 ≤ (Parameters.theta:ℝ) := by norm_num [Parameters.theta]
  have hc : 0 ≤ (Parameters.c:ℝ) := by norm_num [Parameters.c]
  refine ⟨?_,?_⟩
  · change L40Conds A ρ (qA A ρ/Real.sqrt (1-ρ^2)) (capacity Da ρ+1/4) 1
      (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))
      (Parameters.c:ℝ) (constructedKappa (Parameters.c:ℝ)) (Parameters.theta:ℝ)
    rw [hq]
    refine ⟨hstat.1.1,hstat.1.2,?_,?_⟩
    · simpa only [one_mul] using hstat.2
    · intro r hrlo hrhi _
      have hh := children_cover A ρ hAlo hAhi hρlo hρhi r hrlo hrhi
      have hs := l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ)
        (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl)
      exact (add_le_add (min_le_right (qc r) (fA A r)) le_rfl).trans (hh.trans hs)
  · rw [hq]
    apply div_pos _ (Real.sqrt_pos.mpr hbase)
    have hF := ftilde_uniform_lower A
    have hS : (4/5:ℝ) ≤ Real.sqrt (1-ρ^2) := by
      apply Real.le_sqrt_of_sq_le
      have hp := mul_nonneg (show 0 ≤ (1/2:ℝ)-ρ by linarith)
        (show 0 ≤ (1/2:ℝ)+ρ by linarith)
      nlinarith only [hp]
    have hp := mul_le_mul_of_nonneg_left hS (show 0 ≤ ftilde A by linarith)
    have hz1 : max (-(1/40:ℝ)-ρ) 0=0 := max_eq_right (by linarith)
    have hz2 : max (ρ-(1/50:ℝ)) 0=ρ-(1/50:ℝ) := max_eq_left (by linarith)
    have hz3 : max (ρ-(1/4:ℝ)) 0=ρ-(1/4:ℝ) := max_eq_left (by linarith)
    unfold fA
    rw [hz1,hz2,hz3]
    nlinarith [sq_nonneg (ρ-(1/50:ℝ)),sq_nonneg (ρ-(1/4:ℝ))]

theorem exists_rectangle (A ρ : ℝ) (hAlo : (66025739/32768000:ℝ) ≤ A) (hAhi : A ≤ (66222347/32768000:ℝ))
    (hρlo : (404477/1024000:ℝ) ≤ ρ) (hρhi : ρ ≤ (408573/1024000:ℝ)) (hcase : qA A ρ < qc ρ) :
    (∃ a b μ c κ θ : ℝ, L40Case1 A ρ a b μ c κ θ) ∧ 0 < qA A ρ/Real.sqrt (1-ρ^2) := by
  have h := rectangle A ρ hAlo hAhi hρlo hρhi hcase
  exact ⟨⟨_,_,_,_,_,_,h.1⟩,h.2⟩

end
end GaussLocalMaxColoring.Certificate.Case1Constructive.CellTangentAdaptive2Seed16108
end

section
-- Source module: Solutions.Sol_GaussLocalMaxCase1FamilyTangentAdaptive2Seed16108
set_option autoImplicit false
open GaussLocalMaxColoring.Main
theorem solution (A ρ : ℝ) (hAlo : (66025739/32768000:ℝ) ≤ A) (hAhi : A ≤ (66222347/32768000:ℝ))
    (hρlo : (404477/1024000:ℝ) ≤ ρ) (hρhi : ρ ≤ (408573/1024000:ℝ)) (hcase : qA A ρ < qc ρ) :
    (∃ a b μ c κ θ : ℝ, L40Case1 A ρ a b μ c κ θ) ∧ 0 < qA A ρ/Real.sqrt (1-ρ^2) :=
  GaussLocalMaxColoring.Certificate.Case1Constructive.CellTangentAdaptive2Seed16108.exists_rectangle A ρ hAlo hAhi hρlo hρhi hcase
end

#print axioms solution
