-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_40_adaptive0seed25646_b4_part_9
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T14:29:17.25389+00:00
-- url     : https://prove2.me/submissions/ebfeda1d-62f9-4e11-9e29-4a1e388f414e

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
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646DefsB4Part9
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part9

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
def node407 : BoxExpr 3 := .mul ⟨(17026592217487914599/590295810358705651712:ℚ),(17026592217487914605/590295810358705651712:ℚ)⟩ node264 node382
def node408 : BoxExpr 3 := .mul ⟨(214611489749779220183/4722366482869645213696:ℚ),(53652872437444805065/1180591620717411303424:ℚ)⟩ node407 node313
def node409 : BoxExpr 3 := .mul ⟨(160958617312334415137/2361183241434822606848:ℚ),(160958617312334415195/2361183241434822606848:ℚ)⟩ node408 node315
def node411 : BoxExpr 3 := .mul ⟨(1985879505045154496735/2361183241434822606848:ℚ),(1985879505045154496741/2361183241434822606848:ℚ)⟩ node68 node51
def node412 : BoxExpr 3 := .mul ⟨(4726142958811166820663/4722366482869645213696:ℚ),(590767869851395852585/590295810358705651712:ℚ)⟩ node411 node349
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
def node4254 : BoxExpr 3 := .lit (-312036485317165491123742954302726779952711837284451442610337461713791988599992016921959547053639792687389742941247471/43624816861295183480575856049041147371514908121470076568809273260400089500027672742507792890927579075052513478012043264:ℚ)
def node4316 : BoxExpr 3 := .lit (-312036485317165491123742954302726779952711837284451442610337461713791988599992016921959547053639792687389742941247471/87249633722590366961151712098082294743029816242940153137618546520800179000055345485015585781855158150105026956024086528:ℚ)
def node4317 : BoxExpr 3 := .mul ⟨(-18423130790036717717/4722366482869645213696:ℚ),(-18423130790036717715/4722366482869645213696:ℚ)⟩ node4316 node69
def node4322 : BoxExpr 3 := .mul ⟨(-18423130790036717717/2361183241434822606848:ℚ),(-4605782697509179429/590295810358705651712:ℚ)⟩ node4254 node69
def node4323 : BoxExpr 3 := .add ⟨(4689296697231093385229/4722366482869645213696:ℚ),(146540521788471668289/147573952589676412928:ℚ)⟩ node412 node4322
def node4374 : BoxExpr 3 := .mul ⟨(-8827585205831290249/4722366482869645213696:ℚ),(-8689927252347545421/4722366482869645213696:ℚ)⟩ node4316 node136
def node4380 : BoxExpr 3 := .mul ⟨(-8827585205831290249/2361183241434822606848:ℚ),(-17379854504695090843/4722366482869645213696:ℚ)⟩ node4254 node136
def node4381 : BoxExpr 3 := .add ⟨(13991001436857553560029/4722366482869645213696:ℚ),(14339400081008473739423/4722366482869645213696:ℚ)⟩ node534 node4380
def node4758 : BoxExpr 3 := .var 2
def node4759 : BoxExpr 3 := .mul ⟨(0/1:ℚ),(36881607541024625235/4722366482869645213696:ℚ)⟩ node13 node4758
def node4760 : BoxExpr 3 := .add ⟨(1/2:ℚ),(2398064848975847232083/4722366482869645213696:ℚ)⟩ node4759 node301
def node4761 : BoxExpr 3 := .mul ⟨(4953395616637338341467/4722366482869645213696:ℚ),(1266459744977928596855/1180591620717411303424:ℚ)⟩ node36 node4760
def node4762 : BoxExpr 3 := .mul ⟨(5883069229245334571837/4722366482869645213696:ℚ),(188735716442733006405/147573952589676412928:ℚ)⟩ node4761 node304
def node4763 : BoxExpr 3 := .add ⟨(938626831624067721723/4722366482869645213696:ℚ),(1039925636471734425511/4722366482869645213696:ℚ)⟩ node4758 node306
def node4764 : BoxExpr 3 := .mul ⟨(-7438306082237209559/4722366482869645213696:ℚ),(-3356871600121434229/2361183241434822606848:ℚ)⟩ node4763 node4254
def node4765 : BoxExpr 3 := .mul ⟨(-4060882234892025717/2361183241434822606848:ℚ),(-3658349569192248049/2361183241434822606848:ℚ)⟩ node4764 node37
def node4766 : BoxExpr 3 := .add ⟨(5874947464775550520403/4722366482869645213696:ℚ),(3016113113514535854431/2361183241434822606848:ℚ)⟩ node4762 node4765
def node4767 : BoxExpr 3 := .add ⟨(8294695859957468440105/2361183241434822606848:ℚ),(2109248777986107775763/590295810358705651712:ℚ)⟩ node4766 node316
def node4768 : BoxExpr 3 := .add ⟨(5913722743476557763923/2361183241434822606848:ℚ),(12126167187290117376839/4722366482869645213696:ℚ)⟩ node4767 node323
def node4769 : BoxExpr 3 := .add ⟨(5913715659926833459455/2361183241434822606848:ℚ),(378942281880958398997/147573952589676412928:ℚ)⟩ node4768 node325
def node4770 : BoxExpr 3 := .mul ⟨(0/1:ℚ),(1786640353283903609/4722366482869645213696:ℚ)⟩ node4758 node4758
def node4771 : BoxExpr 3 := .neg ⟨(-1786640353283903609/4722366482869645213696:ℚ),(0/1:ℚ)⟩ node4770
def node4772 : BoxExpr 3 := .add ⟨(4720579842516361310087/4722366482869645213696:ℚ),(1/1:ℚ)⟩ node12 node4771
def node4773 : BoxExpr 3 := .sqrt ⟨(2360736539091631294971/2361183241434822606848:ℚ),(1/1:ℚ)⟩ node4772
def node4774 : BoxExpr 3 := .mul ⟨(11688338172153317318437/4722366482869645213696:ℚ),(5854038089980057203133/2361183241434822606848:ℚ)⟩ node11 node4773
def node4775 : BoxExpr 3 := .neg ⟨(-5854038089980057203133/2361183241434822606848:ℚ),(-11688338172153317318437/4722366482869645213696:ℚ)⟩ node4774
def node4776 : BoxExpr 3 := .add ⟨(29838784973388128161/1180591620717411303424:ℚ),(437814848037351449467/4722366482869645213696:ℚ)⟩ node4769 node4775
def node4777 : BoxExpr 3 := .var 2
def node4778 : BoxExpr 3 := .mul ⟨(18348949698630385203/4722366482869645213696:ℚ),(18348949698630385205/4722366482869645213696:ℚ)⟩ node51 node4777
def node4779 : BoxExpr 3 := .add ⟨(2379532191133452992051/4722366482869645213696:ℚ),(2379532191133452992053/4722366482869645213696:ℚ)⟩ node4778 node301
def node4780 : BoxExpr 3 := .mul ⟨(5009241773300832837259/4722366482869645213696:ℚ),(1252310443325208209319/1180591620717411303424:ℚ)⟩ node68 node4779
def node4781 : BoxExpr 3 := .mul ⟨(2980341037273833874173/2361183241434822606848:ℚ),(2980341037273833874185/2361183241434822606848:ℚ)⟩ node4780 node349
def node4782 : BoxExpr 3 := .add ⟨(61829764627993817101/295147905179352825856:ℚ),(494638117023950536809/2361183241434822606848:ℚ)⟩ node4777 node351
def node4783 : BoxExpr 3 := .mul ⟨(-7076024641240039009/4722366482869645213696:ℚ),(-221125770038751219/147573952589676412928:ℚ)⟩ node4782 node4254
def node4784 : BoxExpr 3 := .mul ⟨(-7718827208118040341/4722366482869645213696:ℚ),(-7718827208118040339/4722366482869645213696:ℚ)⟩ node4783 node69
def node4785 : BoxExpr 3 := .add ⟨(5952963247339549708005/4722366482869645213696:ℚ),(5952963247339549708031/4722366482869645213696:ℚ)⟩ node4781 node4784
def node4786 : BoxExpr 3 := .add ⟨(16731965760255811659901/4722366482869645213696:ℚ),(4182991440063952914995/1180591620717411303424:ℚ)⟩ node4785 node358
def node4787 : BoxExpr 3 := .add ⟨(2994270281368882142271/1180591620717411303424:ℚ),(748567570342220535573/295147905179352825856:ℚ)⟩ node4786 node361
def node4788 : BoxExpr 3 := .add ⟨(2994266739594019990037/1180591620717411303424:ℚ),(11977066958376079960233/4722366482869645213696:ℚ)⟩ node4787 node325
def node4789 : BoxExpr 3 := .mul ⟨(223330044160487951/2361183241434822606848:ℚ),(446660088320975903/4722366482869645213696:ℚ)⟩ node4777 node4777
def node4790 : BoxExpr 3 := .neg ⟨(-446660088320975903/4722366482869645213696:ℚ),(-223330044160487951/2361183241434822606848:ℚ)⟩ node4789
def node4791 : BoxExpr 3 := .add ⟨(4721919822781324237793/4722366482869645213696:ℚ),(2360959911390662118897/2361183241434822606848:ℚ)⟩ node12 node4790
def node4792 : BoxExpr 3 := .sqrt ⟨(2361071573772187691061/2361183241434822606848:ℚ),(4722143147544375382123/4722366482869645213696:ℚ)⟩ node4791
def node4793 : BoxExpr 3 := .mul ⟨(11698655174109323909577/4722366482869645213696:ℚ),(11698655174109323909589/4722366482869645213696:ℚ)⟩ node50 node4792
def node4794 : BoxExpr 3 := .neg ⟨(-11698655174109323909589/4722366482869645213696:ℚ),(-11698655174109323909577/4722366482869645213696:ℚ)⟩ node4793
def node4795 : BoxExpr 3 := .add ⟨(278411784266756050559/4722366482869645213696:ℚ),(8700368258336126583/147573952589676412928:ℚ)⟩ node4788 node4794
def node4796 : BoxExpr 3 := .mul ⟨(1349302871205113090433/4722366482869645213696:ℚ),(168662858900639136305/590295810358705651712:ℚ)⟩ node78 node4779
def node4797 : BoxExpr 3 := .mul ⟨(1605585396256138190273/4722366482869645213696:ℚ),(1605585396256138190283/4722366482869645213696:ℚ)⟩ node4796 node349
def node4798 : BoxExpr 3 := .add ⟨(2742408366768754588933/2361183241434822606848:ℚ),(685602091692188647287/590295810358705651712:ℚ)⟩ node4797 node385
def node4799 : BoxExpr 3 := .add ⟨(195684417064047208069/295147905179352825856:ℚ),(6115138033251475253/9223372036854775808:ℚ)⟩ node4798 node387
def node4800 : BoxExpr 3 := .mul ⟨(91278608812515685867/147573952589676412928:ℚ),(365114435250062743469/590295810358705651712:ℚ)⟩ node77 node4792
def node4801 : BoxExpr 3 := .neg ⟨(-365114435250062743469/590295810358705651712:ℚ),(-91278608812515685867/147573952589676412928:ℚ)⟩ node4800
def node4802 : BoxExpr 3 := .add ⟨(26254398878031672669/590295810358705651712:ℚ),(6563599719507918181/147573952589676412928:ℚ)⟩ node4799 node4801
def node4803 : BoxExpr 3 := .mul ⟨(-2269463474565041852125/4722366482869645213696:ℚ),(-141841467160315115757/295147905179352825856:ℚ)⟩ node98 node4779
def node4804 : BoxExpr 3 := .mul ⟨(6042669537540980167/295147905179352825856:ℚ),(96682712600655682675/4722366482869645213696:ℚ)⟩ node68 node4777
def node4805 : BoxExpr 3 := .add ⟨(-2172780761964386169453/4722366482869645213696:ℚ),(-2172780761964386169437/4722366482869645213696:ℚ)⟩ node4803 node4804
def node4806 : BoxExpr 3 := .mul ⟨(-646368049591511735021/1180591620717411303424:ℚ),(-2585472198366046940063/4722366482869645213696:ℚ)⟩ node4805 node349
def node4807 : BoxExpr 3 := .mul ⟨(5667515432919390690795/4722366482869645213696:ℚ),(5667515432919390690825/4722366482869645213696:ℚ)⟩ node4780 node399
def node4808 : BoxExpr 3 := .add ⟨(3082043234553343750711/4722366482869645213696:ℚ),(1541021617276671875381/2361183241434822606848:ℚ)⟩ node4806 node4807
def node4809 : BoxExpr 3 := .mul ⟨(-3669594501009084525/4722366482869645213696:ℚ),(-3669594501009084523/4722366482869645213696:ℚ)⟩ node4783 node103
def node4810 : BoxExpr 3 := .add ⟨(-11046362645522901121/2361183241434822606848:ℚ),(-11046362645522901119/2361183241434822606848:ℚ)⟩ node4317 node4809
def node4811 : BoxExpr 3 := .add ⟨(3059950509262297948469/4722366482869645213696:ℚ),(764987627315574487131/1180591620717411303424:ℚ)⟩ node4808 node4810
def node4812 : BoxExpr 3 := .add ⟨(3381867743886966778743/4722366482869645213696:ℚ),(1690933871943483389457/2361183241434822606848:ℚ)⟩ node4811 node409
def node4813 : BoxExpr 3 := .add ⟨(45927035940963706679/2361183241434822606848:ℚ),(5740879492620463335/295147905179352825856:ℚ)⟩ node4777 node4777
def node4814 : BoxExpr 3 := .neg ⟨(-5740879492620463335/295147905179352825856:ℚ),(-45927035940963706679/2361183241434822606848:ℚ)⟩ node4813
def node4815 : BoxExpr 3 := .mul ⟨(2361071573772187691061/1180591620717411303424:ℚ),(4722143147544375382123/2361183241434822606848:ℚ)⟩ node86 node4792
def node4816 : BoxExpr 3 := .inv ⟨(2361294914378816638073/4722366482869645213696:ℚ),(1180647457189408319037/2361183241434822606848:ℚ)⟩ node4815
def node4817 : BoxExpr 3 := .mul ⟨(-45929208075350587417/4722366482869645213696:ℚ),(-45929208075350587415/4722366482869645213696:ℚ)⟩ node4814 node4816
def node4818 : BoxExpr 3 := .mul ⟨(-56892596317506555485/2361183241434822606848:ℚ),(-28446298158753277741/1180591620717411303424:ℚ)⟩ node50 node4817
def node4819 : BoxExpr 3 := .neg ⟨(28446298158753277741/1180591620717411303424:ℚ),(56892596317506555485/2361183241434822606848:ℚ)⟩ node4818
def node4820 : BoxExpr 3 := .add ⟨(4803081889866106496193/4722366482869645213696:ℚ),(2401540944933053248109/2361183241434822606848:ℚ)⟩ node4323 node4819
def node4821 : BoxExpr 3 := .mul ⟨(10639432152754895939513/4722366482869645213696:ℚ),(10826187744460227162213/4722366482869645213696:ℚ)⟩ node112 node4760
def node4822 : BoxExpr 3 := .mul ⟨(12636284431689977869645/4722366482869645213696:ℚ),(12907087230505515013929/4722366482869645213696:ℚ)⟩ node4821 node304
def node4823 : BoxExpr 3 := .add ⟨(1497655959409547627023/295147905179352825856:ℚ),(23616718421583166714105/2361183241434822606848:ℚ)⟩ node4822 node448
def node4824 : BoxExpr 3 := .mul ⟨(11614823772330825971257/2361183241434822606848:ℚ),(23234043095718654451385/4722366482869645213696:ℚ)⟩ node111 node4773
def node4825 : BoxExpr 3 := .neg ⟨(-23234043095718654451385/4722366482869645213696:ℚ),(-11614823772330825971257/2361183241434822606848:ℚ)⟩ node4824
def node4826 : BoxExpr 3 := .add ⟨(728452254834107580983/4722366482869645213696:ℚ),(187529603894567824107/36893488147419103232:ℚ)⟩ node4823 node4825
def node4827 : BoxExpr 3 := .mul ⟨(-332920057890169355527/2361183241434822606848:ℚ),(-617638709267156972597/4722366482869645213696:ℚ)⟩ node131 node4760
def node4828 : BoxExpr 3 := .mul ⟨(0/1:ℚ),(53378848533719303269/4722366482869645213696:ℚ)⟩ node118 node4758
def node4829 : BoxExpr 3 := .add ⟨(-332920057890169355527/2361183241434822606848:ℚ),(-35266241295839854333/295147905179352825856:ℚ)⟩ node4827 node4828
def node4830 : BoxExpr 3 := .mul ⟨(-198455279429832354975/1180591620717411303424:ℚ),(-167540616624150980203/1180591620717411303424:ℚ)⟩ node4829 node304
def node4831 : BoxExpr 3 := .mul ⟨(652851522347641074869/2361183241434822606848:ℚ),(1393579377864290298351/4722366482869645213696:ℚ)⟩ node118 node4760
def node4832 : BoxExpr 3 := .mul ⟨(366083016055369810569/1180591620717411303424:ℚ),(1590664239094105146931/4722366482869645213696:ℚ)⟩ node4831 node461
def node4833 : BoxExpr 3 := .add ⟨(83813868312768727797/590295810358705651712:ℚ),(920501772597501226119/4722366482869645213696:ℚ)⟩ node4830 node4832
def node4834 : BoxExpr 3 := .add ⟨(-2086789778392321019583/4722366482869645213696:ℚ),(2334075653169160999023/4722366482869645213696:ℚ)⟩ node4833 node476
def node4835 : BoxExpr 3 := .add ⟨(0/1:ℚ),(91854071881927413359/2361183241434822606848:ℚ)⟩ node4758 node4758
def node4836 : BoxExpr 3 := .neg ⟨(-91854071881927413359/2361183241434822606848:ℚ),(0/1:ℚ)⟩ node4835
def node4837 : BoxExpr 3 := .mul ⟨(2360736539091631294971/1180591620717411303424:ℚ),(2/1:ℚ)⟩ node86 node4773
def node4838 : BoxExpr 3 := .inv ⟨(1/2:ℚ),(2361630028303745658951/4722366482869645213696:ℚ)⟩ node4837
def node4839 : BoxExpr 3 := .mul ⟨(-45935726328150476009/2361183241434822606848:ℚ),(0/1:ℚ)⟩ node4836 node4838
def node4840 : BoxExpr 3 := .mul ⟨(-14545942004301254255/1180591620717411303424:ℚ),(0/1:ℚ)⟩ node117 node4839
def node4841 : BoxExpr 3 := .neg ⟨(0/1:ℚ),(14545942004301254255/1180591620717411303424:ℚ)⟩ node4840
def node4842 : BoxExpr 3 := .add ⟨(1232930592106363975947/4722366482869645213696:ℚ),(685939457373232859373/2361183241434822606848:ℚ)⟩ node479 node4841
def node4843 : BoxExpr 3 := .add ⟨(-1043394889196160509791/2361183241434822606848:ℚ),(2334075653169160999023/4722366482869645213696:ℚ)⟩ node4833 node492
def node4844 : BoxExpr 3 := .mul ⟨(-615952283554811798269/1180591620717411303424:ℚ),(-2371223024062864833603/4722366482869645213696:ℚ)⟩ node175 node4760
def node4845 : BoxExpr 3 := .mul ⟨(-88676611989587064221/4722366482869645213696:ℚ),(0/1:ℚ)⟩ node148 node4758
def node4846 : BoxExpr 3 := .add ⟨(-2552485746208834257297/4722366482869645213696:ℚ),(-2371223024062864833603/4722366482869645213696:ℚ)⟩ node4844 node4845
def node4847 : BoxExpr 3 := .add ⟨(-1320581179099210660759/2361183241434822606848:ℚ),(-2371223024062864833603/4722366482869645213696:ℚ)⟩ node4846 node4845
def node4848 : BoxExpr 3 := .mul ⟨(-1574409836215819486589/2361183241434822606848:ℚ),(-2816263890105440892093/4722366482869645213696:ℚ)⟩ node4847 node304
def node4849 : BoxExpr 3 := .mul ⟨(-1157554922616005063379/2361183241434822606848:ℚ),(-2224534134442377629031/4722366482869645213696:ℚ)⟩ node148 node4760
def node4850 : BoxExpr 3 := .mul ⟨(0/1:ℚ),(194038930182311776327/4722366482869645213696:ℚ)⟩ node36 node4758
def node4851 : BoxExpr 3 := .add ⟨(-1157554922616005063379/2361183241434822606848:ℚ),(-63452975133127057897/147573952589676412928:ℚ)⟩ node4849 node4850
def node4852 : BoxExpr 3 := .mul ⟨(-2642520762634206132149/4722366482869645213696:ℚ),(-1138589377548649806919/2361183241434822606848:ℚ)⟩ node4851 node461
def node4853 : BoxExpr 3 := .add ⟨(-5791340435065845105327/4722366482869645213696:ℚ),(-5093442645202740505931/4722366482869645213696:ℚ)⟩ node4848 node4852
def node4854 : BoxExpr 3 := .mul ⟨(24425763221432913275057/4722366482869645213696:ℚ),(25514898155742723283641/4722366482869645213696:ℚ)⟩ node4761 node514
def node4855 : BoxExpr 3 := .add ⟨(5445810614699676785727/1180591620717411303424:ℚ),(23237719400645423669803/4722366482869645213696:ℚ)⟩ node4852 node4854
def node4856 : BoxExpr 3 := .add ⟨(15991902023732862037581/4722366482869645213696:ℚ),(567008648607583848871/147573952589676412928:ℚ)⟩ node4853 node4855
def node4857 : BoxExpr 3 := .mul ⟨(-15273347148950290259/4722366482869645213696:ℚ),(-6788306865747574369/2361183241434822606848:ℚ)⟩ node4764 node189
def node4858 : BoxExpr 3 := .add ⟨(-6025233088695395127/1180591620717411303424:ℚ),(-22266540983842694159/4722366482869645213696:ℚ)⟩ node4374 node4857
def node4859 : BoxExpr 3 := .add ⟨(-32928517560612870757/4722366482869645213696:ℚ),(-7739117059047559895/1180591620717411303424:ℚ)⟩ node4374 node4858
def node4860 : BoxExpr 3 := .add ⟨(1994871688271531145853/590295810358705651712:ℚ),(4528330071801623231073/1180591620717411303424:ℚ)⟩ node4856 node4859
def node4861 : BoxExpr 3 := .add ⟨(27062706784538820538347/4722366482869645213696:ℚ),(34706791326533939398835/4722366482869645213696:ℚ)⟩ node4860 node527
def node4862 : BoxExpr 3 := .mul ⟨(-2361630028303745658951/2361183241434822606848:ℚ),(-1/1:ℚ)⟩ node6 node4838
def node4863 : BoxExpr 3 := .mul ⟨(-45935726328150476009/1180591620717411303424:ℚ),(0/1:ℚ)⟩ node86 node4839
def node4864 : BoxExpr 3 := .mul ⟨(18882319370065445240343/4722366482869645213696:ℚ),(4/1:ℚ)⟩ node4837 node4837
def node4865 : BoxExpr 3 := .inv ⟨(1/4:ℚ),(1181038449857197272707/4722366482869645213696:ℚ)⟩ node4864
def node4866 : BoxExpr 3 := .mul ⟨(-45953112036062055523/4722366482869645213696:ℚ),(0/1:ℚ)⟩ node4863 node4865
def node4867 : BoxExpr 3 := .neg ⟨(0/1:ℚ),(45953112036062055523/4722366482869645213696:ℚ)⟩ node4866
def node4868 : BoxExpr 3 := .mul ⟨(-1787654758041455683/4722366482869645213696:ℚ),(0/1:ℚ)⟩ node4836 node4867
def node4869 : BoxExpr 3 := .add ⟨(-4725047711365532773585/4722366482869645213696:ℚ),(-1/1:ℚ)⟩ node4862 node4868
def node4870 : BoxExpr 3 := .mul ⟨(-2928680925087624044881/1180591620717411303424:ℚ),(-11690549858194116419425/4722366482869645213696:ℚ)⟩ node11 node4869
def node4871 : BoxExpr 3 := .neg ⟨(11690549858194116419425/4722366482869645213696:ℚ),(2928680925087624044881/1180591620717411303424:ℚ)⟩ node4870
def cert_iv32 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (155606922197/16000007377576:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (155606922197/16000007377576:ℚ)],
    whole := node4776, centerValue := node4795, gradient := ![node4802, node4812, node4820],
    hessian := ![![node4826, node4834, node4842], ![node4843, node4861, node4381], ![node4842, node4381, node4871]] }
def node4872 : BoxExpr 3 := .var 2
def node4873 : BoxExpr 3 := .mul ⟨(9128547813374228895/1180591620717411303424:ℚ),(37922862583592280487/4722366482869645213696:ℚ)⟩ node13 node4872
def node4874 : BoxExpr 3 := .add ⟨(599424358172079880607/1180591620717411303424:ℚ),(2399106104018414887335/4722366482869645213696:ℚ)⟩ node4873 node301
def node4875 : BoxExpr 3 := .mul ⟨(2514998358594940839851/2361183241434822606848:ℚ),(316752412467886866717/295147905179352825856:ℚ)⟩ node36 node4874
def node4876 : BoxExpr 3 := .mul ⟨(2987023569318044861751/2361183241434822606848:ℚ),(6042165334201734936921/4722366482869645213696:ℚ)⟩ node4875 node304
def node4877 : BoxExpr 3 := .add ⟨(1030480903505995135081/4722366482869645213696:ℚ),(521259447123599958213/2361183241434822606848:ℚ)⟩ node4872 node306
def node4878 : BoxExpr 3 := .mul ⟨(-233026717246699065/147573952589676412928:ℚ),(-3685375234225354705/2361183241434822606848:ℚ)⟩ node4877 node4254
def node4879 : BoxExpr 3 := .mul ⟨(-8142017676477969995/4722366482869645213696:ℚ),(-1004088963363417263/590295810358705651712:ℚ)⟩ node4878 node37
def node4880 : BoxExpr 3 := .add ⟨(5965905120959611753507/4722366482869645213696:ℚ),(6034132622494827598817/4722366482869645213696:ℚ)⟩ node4876 node4879
def node4881 : BoxExpr 3 := .add ⟨(8340174688049499056657/2361183241434822606848:ℚ),(16875896619354618096059/4722366482869645213696:ℚ)⟩ node4880 node316
def node4882 : BoxExpr 3 := .add ⟨(5959201571568588380475/2361183241434822606848:ℚ),(6064036791377936633397/2361183241434822606848:ℚ)⟩ node4881 node323
def node4883 : BoxExpr 3 := .add ⟨(5959194488018864076007/2361183241434822606848:ℚ),(12128059415656424657859/4722366482869645213696:ℚ)⟩ node4882 node325
def node4884 : BoxExpr 3 := .mul ⟨(223330044160487951/590295810358705651712:ℚ),(944473296573929043/2361183241434822606848:ℚ)⟩ node4872 node4872
def node4885 : BoxExpr 3 := .neg ⟨(-944473296573929043/2361183241434822606848:ℚ),(-223330044160487951/590295810358705651712:ℚ)⟩ node4884
def node4886 : BoxExpr 3 := .add ⟨(2360238768138248677805/2361183241434822606848:ℚ),(590072480314545163761/590295810358705651712:ℚ)⟩ node12 node4885
def node4887 : BoxExpr 3 := .sqrt ⟨(4721421915106847437639/4722366482869645213696:ℚ),(590184134772907823743/590295810358705651712:ℚ)⟩ node4886
def node4888 : BoxExpr 3 := .mul ⟨(11688211514364706538999/4722366482869645213696:ℚ),(11705861178188090803323/4722366482869645213696:ℚ)⟩ node11 node4887
def node4889 : BoxExpr 3 := .neg ⟨(-11705861178188090803323/4722366482869645213696:ℚ),(-11688211514364706538999/4722366482869645213696:ℚ)⟩ node4888
def node4890 : BoxExpr 3 := .add ⟨(212527797849637348691/4722366482869645213696:ℚ),(109961975322929529715/1180591620717411303424:ℚ)⟩ node4883 node4889
def node4891 : BoxExpr 3 := .var 2
def node4892 : BoxExpr 3 := .mul ⟨(18607966830384566271/2361183241434822606848:ℚ),(4542960651949357/576460752303423488:ℚ)⟩ node51 node4891
def node4893 : BoxExpr 3 := .add ⟨(1199199587547795869695/2361183241434822606848:ℚ),(292773336803661101/576460752303423488:ℚ)⟩ node4892 node301
def node4894 : BoxExpr 3 := .mul ⟨(2524479681700867963597/2361183241434822606848:ℚ),(5048959363401735927211/4722366482869645213696:ℚ)⟩ node68 node4893
def node4895 : BoxExpr 3 := .mul ⟨(6007943504135779416553/4722366482869645213696:ℚ),(6007943504135779416577/4722366482869645213696:ℚ)⟩ node4894 node349
def node4896 : BoxExpr 3 := .add ⟨(1036499898876597525753/4722366482869645213696:ℚ),(1036499898876597525755/4722366482869645213696:ℚ)⟩ node4891 node351
def node4897 : BoxExpr 3 := .mul ⟨(-7413802710172539745/4722366482869645213696:ℚ),(-231681334692891867/147573952589676412928:ℚ)⟩ node4896 node4254
def node4898 : BoxExpr 3 := .mul ⟨(-8087289823918774695/4722366482869645213696:ℚ),(-8087289823918774693/4722366482869645213696:ℚ)⟩ node4897 node69
def node4899 : BoxExpr 3 := .add ⟨(2999928107155930320929/2361183241434822606848:ℚ),(1499964053577965160471/1180591620717411303424:ℚ)⟩ node4895 node4898
def node4900 : BoxExpr 3 := .add ⟨(8389429363614061296877/2361183241434822606848:ℚ),(16778858727228122593833/4722366482869645213696:ℚ)⟩ node4899 node358
def node4901 : BoxExpr 3 := .add ⟨(12023974092447839502937/4722366482869645213696:ℚ),(12023974092447839503021/4722366482869645213696:ℚ)⟩ node4900 node361
def node4902 : BoxExpr 3 := .add ⟨(12023959925348390894001/4722366482869645213696:ℚ),(6011979962674195447043/2361183241434822606848:ℚ)⟩ node4901 node325
def node4903 : BoxExpr 3 := .mul ⟨(1837437455427214557/4722366482869645213696:ℚ),(918718727713607279/2361183241434822606848:ℚ)⟩ node4891 node4891
def node4904 : BoxExpr 3 := .neg ⟨(-918718727713607279/2361183241434822606848:ℚ),(-1837437455427214557/4722366482869645213696:ℚ)⟩ node4903
def node4905 : BoxExpr 3 := .add ⟨(2360264522707108999569/2361183241434822606848:ℚ),(4720529045414217999139/4722366482869645213696:ℚ)⟩ node12 node4904
def node4906 : BoxExpr 3 := .sqrt ⟨(4721447674757896157429/4722366482869645213696:ℚ),(2360723837378948078715/2361183241434822606848:ℚ)⟩ node4905
def node4907 : BoxExpr 3 := .mul ⟨(11696932207215313428145/4722366482869645213696:ℚ),(2924233051803828357039/1180591620717411303424:ℚ)⟩ node50 node4906
def node4908 : BoxExpr 3 := .neg ⟨(-2924233051803828357039/1180591620717411303424:ℚ),(-11696932207215313428145/4722366482869645213696:ℚ)⟩ node4907
def node4909 : BoxExpr 3 := .add ⟨(327027718133077465845/4722366482869645213696:ℚ),(327027718133077465941/4722366482869645213696:ℚ)⟩ node4902 node4908
def node4910 : BoxExpr 3 := .mul ⟨(21250020443297191407/73786976294838206464:ℚ),(1360001308371020250055/4722366482869645213696:ℚ)⟩ node78 node4893
def node4911 : BoxExpr 3 := .mul ⟨(1618315862367873942785/4722366482869645213696:ℚ),(1618315862367873942795/4722366482869645213696:ℚ)⟩ node4910 node349
def node4912 : BoxExpr 3 := .add ⟨(2748773599824622465189/2361183241434822606848:ℚ),(687193399956155616351/590295810358705651712:ℚ)⟩ node4911 node385
def node4913 : BoxExpr 3 := .add ⟨(196480071196030692601/295147905179352825856:ℚ),(49120017799007673157/73786976294838206464:ℚ)⟩ node4912 node387
def node4914 : BoxExpr 3 := .mul ⟨(730121323081195928377/1180591620717411303424:ℚ),(2920485292324783713517/4722366482869645213696:ℚ)⟩ node77 node4906
def node4915 : BoxExpr 3 := .neg ⟨(-2920485292324783713517/4722366482869645213696:ℚ),(-730121323081195928377/1180591620717411303424:ℚ)⟩ node4914
def node4916 : BoxExpr 3 := .add ⟨(223195846811707368099/4722366482869645213696:ℚ),(55798961702926842135/1180591620717411303424:ℚ)⟩ node4913 node4915
def node4917 : BoxExpr 3 := .mul ⟨(-285932217348656985639/590295810358705651712:ℚ),(-2287457738789255885099/4722366482869645213696:ℚ)⟩ node98 node4893
def node4918 : BoxExpr 3 := .mul ⟨(196095006928804453715/4722366482869645213696:ℚ),(98047503464402226859/2361183241434822606848:ℚ)⟩ node68 node4891
def node4919 : BoxExpr 3 := .add ⟨(-2091362731860451431397/4722366482869645213696:ℚ),(-2091362731860451431381/4722366482869645213696:ℚ)⟩ node4917 node4918
def node4920 : BoxExpr 3 := .mul ⟨(-2488589872746991460263/4722366482869645213696:ℚ),(-1244294936373495730121/2361183241434822606848:ℚ)⟩ node4919 node349
def node4921 : BoxExpr 3 := .mul ⟨(1428113096116657901299/1180591620717411303424:ℚ),(2856226192233315802613/2361183241434822606848:ℚ)⟩ node4894 node399
def node4922 : BoxExpr 3 := .add ⟨(3223862511719640144933/4722366482869645213696:ℚ),(402982813964955018123/590295810358705651712:ℚ)⟩ node4920 node4921
def node4923 : BoxExpr 3 := .mul ⟨(-3844764685845941499/4722366482869645213696:ℚ),(-1922382342922970749/2361183241434822606848:ℚ)⟩ node4897 node103
def node4924 : BoxExpr 3 := .add ⟨(-1391743467242666201/295147905179352825856:ℚ),(-22267895475882659213/4722366482869645213696:ℚ)⟩ node4317 node4923
def node4925 : BoxExpr 3 := .add ⟨(3201594616243757485717/4722366482869645213696:ℚ),(3201594616243757485771/4722366482869645213696:ℚ)⟩ node4922 node4924
def node4926 : BoxExpr 3 := .add ⟨(3523511850868426315991/4722366482869645213696:ℚ),(3523511850868426316161/4722366482869645213696:ℚ)⟩ node4925 node409
def node4927 : BoxExpr 3 := .add ⟨(2910959399051879963/73786976294838206464:ℚ),(93150700769660158817/2361183241434822606848:ℚ)⟩ node4891 node4891
def node4928 : BoxExpr 3 := .neg ⟨(-93150700769660158817/2361183241434822606848:ℚ),(-2910959399051879963/73786976294838206464:ℚ)⟩ node4927
def node4929 : BoxExpr 3 := .mul ⟨(4721447674757896157429/2361183241434822606848:ℚ),(2360723837378948078715/1180591620717411303424:ℚ)⟩ node86 node4906
def node4930 : BoxExpr 3 := .inv ⟨(2361642734892126989771/4722366482869645213696:ℚ),(2361642734892126989773/4722366482869645213696:ℚ)⟩ node4929
def node4931 : BoxExpr 3 := .mul ⟨(-93168828180017758837/4722366482869645213696:ℚ),(-46584414090008879417/2361183241434822606848:ℚ)⟩ node4928 node4930
def node4932 : BoxExpr 3 := .mul ⟨(-230816804954476394229/4722366482869645213696:ℚ),(-230816804954476394221/4722366482869645213696:ℚ)⟩ node50 node4931
def node4933 : BoxExpr 3 := .neg ⟨(230816804954476394221/4722366482869645213696:ℚ),(230816804954476394229/4722366482869645213696:ℚ)⟩ node4932
def node4934 : BoxExpr 3 := .add ⟨(2460056751092784889725/2361183241434822606848:ℚ),(4920113502185569779477/4722366482869645213696:ℚ)⟩ node4323 node4933
def node4935 : BoxExpr 3 := .mul ⟨(10803964177900992780153/4722366482869645213696:ℚ),(5415444272092218581829/2361183241434822606848:ℚ)⟩ node112 node4874
def node4936 : BoxExpr 3 := .mul ⟨(3207924125593407184871/1180591620717411303424:ℚ),(12912691570050112466925/4722366482869645213696:ℚ)⟩ node4935 node304
def node4937 : BoxExpr 3 := .add ⟨(24157907421236412902207/4722366482869645213696:ℚ),(23619520591355465440603/2361183241434822606848:ℚ)⟩ node4936 node448
def node4938 : BoxExpr 3 := .mul ⟨(23229395822325689393183/4722366482869645213696:ℚ),(11614823772330825971263/2361183241434822606848:ℚ)⟩ node111 node4887
def node4939 : BoxExpr 3 := .neg ⟨(-11614823772330825971263/2361183241434822606848:ℚ),(-23229395822325689393183/4722366482869645213696:ℚ)⟩ node4938
def node4940 : BoxExpr 3 := .add ⟨(928259876574760959681/4722366482869645213696:ℚ),(24009645360385241488023/4722366482869645213696:ℚ)⟩ node4937 node4939
def node4941 : BoxExpr 3 := .mul ⟨(-333064613901320639439/2361183241434822606848:ℚ),(-627190097554175052407/4722366482869645213696:ℚ)⟩ node131 node4874
def node4942 : BoxExpr 3 := .mul ⟨(50794084600994977369/4722366482869645213696:ℚ),(27442929860946972069/2361183241434822606848:ℚ)⟩ node118 node4872
def node4943 : BoxExpr 3 := .add ⟨(-615335143201646301509/4722366482869645213696:ℚ),(-572304237832281108269/4722366482869645213696:ℚ)⟩ node4941 node4942
def node4944 : BoxExpr 3 := .mul ⟨(-183402148493205200721/1180591620717411303424:ℚ),(-169929161323654467553/1180591620717411303424:ℚ)⟩ node4943 node304
def node4945 : BoxExpr 3 := .mul ⟨(1325894908612334610641/4722366482869645213696:ℚ),(697092239456381223115/2361183241434822606848:ℚ)⟩ node118 node4874
def node4946 : BoxExpr 3 := .mul ⟨(1486977024643576563225/4722366482869645213696:ℚ),(24864920556961438699/73786976294838206464:ℚ)⟩ node4945 node461
def node4947 : BoxExpr 3 := .add ⟨(753368430670755760341/4722366482869645213696:ℚ),(227909567587728551631/1180591620717411303424:ℚ)⟩ node4944 node4946
def node4948 : BoxExpr 3 := .add ⟨(-1001966147111857540809/2361183241434822606848:ℚ),(581303037730643494857/1180591620717411303424:ℚ)⟩ node4947 node476
def node4949 : BoxExpr 3 := .add ⟨(45927035940963706679/1180591620717411303424:ℚ),(47223664828696452137/1180591620717411303424:ℚ)⟩ node4872 node4872
def node4950 : BoxExpr 3 := .neg ⟨(-47223664828696452137/1180591620717411303424:ℚ),(-45927035940963706679/1180591620717411303424:ℚ)⟩ node4949
def node4951 : BoxExpr 3 := .mul ⟨(4721421915106847437639/2361183241434822606848:ℚ),(590184134772907823743/295147905179352825856:ℚ)⟩ node86 node4887
def node4952 : BoxExpr 3 := .inv ⟨(2361630028303745658949/4722366482869645213696:ℚ),(2361655619801344256523/4722366482869645213696:ℚ)⟩ node4951
def node4953 : BoxExpr 3 := .mul ⟨(-47233112396026885131/2361183241434822606848:ℚ),(-5741965791018809501/295147905179352825856:ℚ)⟩ node4950 node4952
def node4954 : BoxExpr 3 := .mul ⟨(-59827081752201185493/4722366482869645213696:ℚ),(-27735861367395506457/2361183241434822606848:ℚ)⟩ node117 node4953
def node4955 : BoxExpr 3 := .neg ⟨(27735861367395506457/2361183241434822606848:ℚ),(59827081752201185493/4722366482869645213696:ℚ)⟩ node4954
def node4956 : BoxExpr 3 := .add ⟨(1288402314841154988861/4722366482869645213696:ℚ),(1373522228481461887219/4722366482869645213696:ℚ)⟩ node479 node4955
def node4957 : BoxExpr 3 := .add ⟨(-2003932294223715081617/4722366482869645213696:ℚ),(581303037730643494857/1180591620717411303424:ℚ)⟩ node4947 node492
def node4958 : BoxExpr 3 := .mul ⟨(-1232439467924759117241/2361183241434822606848:ℚ),(-2407892474144474175085/4722366482869645213696:ℚ)⟩ node175 node4874
def node4959 : BoxExpr 3 := .mul ⟨(-22795040638609704665/1180591620717411303424:ℚ),(-43269093796528978273/2361183241434822606848:ℚ)⟩ node148 node4872
def node4960 : BoxExpr 3 := .add ⟨(-1278029549201978526571/2361183241434822606848:ℚ),(-2494430661737532131631/4722366482869645213696:ℚ)⟩ node4958 node4959
def node4961 : BoxExpr 3 := .add ⟨(-1323619630479197935901/2361183241434822606848:ℚ),(-2580968849330590088177/4722366482869645213696:ℚ)⟩ node4960 node4959
def node4962 : BoxExpr 3 := .mul ⟨(-1578032307757310468841/2361183241434822606848:ℚ),(-1532687836212581171379/2361183241434822606848:ℚ)⟩ node4961 node304
def node4963 : BoxExpr 3 := .mul ⟨(-2316115080683201269123/4722366482869645213696:ℚ),(-1129467567252182144863/2361183241434822606848:ℚ)⟩ node148 node4874
def node4964 : BoxExpr 3 := .mul ⟨(24086946591327780473/590295810358705651712:ℚ),(199517108276420747329/4722366482869645213696:ℚ)⟩ node36 node4872
def node4965 : BoxExpr 3 := .add ⟨(-2123419507952579025339/4722366482869645213696:ℚ),(-2059418026227943542397/4722366482869645213696:ℚ)⟩ node4963 node4964
def node4966 : BoxExpr 3 := .mul ⟨(-1211860454289777352605/2361183241434822606848:ℚ),(-2309615392024355800657/4722366482869645213696:ℚ)⟩ node4965 node461
def node4967 : BoxExpr 3 := .add ⟨(-1394946381023543910723/1180591620717411303424:ℚ),(-5374991064449518143415/4722366482869645213696:ℚ)⟩ node4962 node4966
def node4968 : BoxExpr 3 := .mul ⟨(387554563347163854509/73786976294838206464:ℚ),(25525976887152598871975/4722366482869645213696:ℚ)⟩ node4875 node514
def node4969 : BoxExpr 3 := .add ⟨(11189885572819465991683/2361183241434822606848:ℚ),(11608180747564121535659/2361183241434822606848:ℚ)⟩ node4966 node4968
def node4970 : BoxExpr 3 := .add ⟨(8399992810772378170237/2361183241434822606848:ℚ),(17841370430678724927903/4722366482869645213696:ℚ)⟩ node4967 node4969
def node4971 : BoxExpr 3 := .mul ⟨(-1913929278058776187/590295810358705651712:ℚ),(-14905221876489436357/4722366482869645213696:ℚ)⟩ node4878 node189
def node4972 : BoxExpr 3 := .add ⟨(-24139019430301499745/4722366482869645213696:ℚ),(-11797574564418490889/2361183241434822606848:ℚ)⟩ node4374 node4971
def node4973 : BoxExpr 3 := .add ⟨(-16483302318066394997/2361183241434822606848:ℚ),(-32285076381184527199/4722366482869645213696:ℚ)⟩ node4374 node4972
def node4974 : BoxExpr 3 := .add ⟨(1047938688556788971905/295147905179352825856:ℚ),(278266958660899068761/73786976294838206464:ℚ)⟩ node4970 node4973
def node4975 : BoxExpr 3 := .add ⟨(27870752295275194922003/4722366482869645213696:ℚ),(34402556393624986875247/4722366482869645213696:ℚ)⟩ node4974 node527
def node4976 : BoxExpr 3 := .mul ⟨(-2361655619801344256523/2361183241434822606848:ℚ),(-2361630028303745658949/2361183241434822606848:ℚ)⟩ node6 node4952
def node4977 : BoxExpr 3 := .mul ⟨(-47233112396026885131/1180591620717411303424:ℚ),(-5741965791018809501/147573952589676412928:ℚ)⟩ node86 node4953
def node4978 : BoxExpr 3 := .mul ⟨(4720477536276497355609/1180591620717411303424:ℚ),(2360289921258180655045/590295810358705651712:ℚ)⟩ node4951 node4951
def node4979 : BoxExpr 3 := .inv ⟨(1181038449857197272705/4722366482869645213696:ℚ),(590532023167972840849/2361183241434822606848:ℚ)⟩ node4978
def node4980 : BoxExpr 3 := .mul ⟨(-47252013201307408095/4722366482869645213696:ℚ),(-45953112036062055521/4722366482869645213696:ℚ)⟩ node4977 node4979
def node4981 : BoxExpr 3 := .neg ⟨(45953112036062055521/4722366482869645213696:ℚ),(47252013201307408095/4722366482869645213696:ℚ)⟩ node4980
def node4982 : BoxExpr 3 := .mul ⟨(-472520132013074081/1180591620717411303424:ℚ),(-893827379020727841/2361183241434822606848:ℚ)⟩ node4950 node4981
def node4983 : BoxExpr 3 := .add ⟨(-2362600660065370404685/2361183241434822606848:ℚ),(-1181261927841383193395/1180591620717411303424:ℚ)⟩ node4976 node4982
def node4984 : BoxExpr 3 := .mul ⟨(-5857552269865406530815/2361183241434822606848:ℚ),(-1462148428453237749885/590295810358705651712:ℚ)⟩ node11 node4983
def node4985 : BoxExpr 3 := .neg ⟨(1462148428453237749885/590295810358705651712:ℚ),(5857552269865406530815/2361183241434822606848:ℚ)⟩ node4984
def cert_iv33 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (7890174899319/400000184439400:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (109828789469/400000184439400:ℚ)],
    whole := node4890, centerValue := node4909, gradient := ![node4916, node4926, node4934],
    hessian := ![![node4940, node4948, node4956], ![node4957, node4975, node4381], ![node4956, node4381, node4985]] }
def node4986 : BoxExpr 3 := .var 2
def node4987 : BoxExpr 3 := .mul ⟨(9386268316240677217/1180591620717411303424:ℚ),(194309304035182995555/4722366482869645213696:ℚ)⟩ node13 node4986
def node4988 : BoxExpr 3 := .add ⟨(599682078674946328929/1180591620717411303424:ℚ),(2555492545470005602403/4722366482869645213696:ℚ)⟩ node4987 node301
def node4989 : BoxExpr 3 := .mul ⟨(5032159347496270756047/4722366482869645213696:ℚ),(1349600048894064528663/1180591620717411303424:ℚ)⟩ node36 node4988
def node4990 : BoxExpr 3 := .mul ⟨(2988307830135716846363/2361183241434822606848:ℚ),(3218012834902799286007/2361183241434822606848:ℚ)⟩ node4989 node304
def node4991 : BoxExpr 3 := .add ⟨(258268540320365156499/1180591620717411303424:ℚ),(1432001142776494175553/4722366482869645213696:ℚ)⟩ node4986 node306
def node4992 : BoxExpr 3 := .mul ⟨(-320084870630270891/147573952589676412928:ℚ),(-7389299338107869931/4722366482869645213696:ℚ)⟩ node4991 node4254
def node4993 : BoxExpr 3 := .mul ⟨(-11183853531635102639/4722366482869645213696:ℚ),(-8052926435798613419/4722366482869645213696:ℚ)⟩ node4992 node37
def node4994 : BoxExpr 3 := .add ⟨(5965431806739798590087/4722366482869645213696:ℚ),(6427972743369799958595/4722366482869645213696:ℚ)⟩ node4990 node4993
def node4995 : BoxExpr 3 := .add ⟨(8339938030939592474947/2361183241434822606848:ℚ),(17269736740229590455837/4722366482869645213696:ℚ)⟩ node4994 node316
def node4996 : BoxExpr 3 := .add ⟨(5958964914458681798765/2361183241434822606848:ℚ),(3130478425907711406643/1180591620717411303424:ℚ)⟩ node4995 node323
def node4997 : BoxExpr 3 := .add ⟨(5958957830908957494297/2361183241434822606848:ℚ),(12521899536531397017637/4722366482869645213696:ℚ)⟩ node4996 node325
def node4998 : BoxExpr 3 := .mul ⟨(1888946593147858085/4722366482869645213696:ℚ),(3099450210681708425/295147905179352825856:ℚ)⟩ node4986 node4986
def node4999 : BoxExpr 3 := .neg ⟨(-3099450210681708425/295147905179352825856:ℚ),(-1888946593147858085/4722366482869645213696:ℚ)⟩ node4998
def node5000 : BoxExpr 3 := .add ⟨(292048454968671117431/295147905179352825856:ℚ),(4720477536276497355611/4722366482869645213696:ℚ)⟩ node12 node4999
def node5001 : BoxExpr 3 := .sqrt ⟨(4697505440325394469047/4722366482869645213696:ℚ),(590177739388355929705/590295810358705651712:ℚ)⟩ node5000
def node5002 : BoxExpr 3 := .mul ⟨(11629004601500350588095/4722366482869645213696:ℚ),(2926433582628938692027/1180591620717411303424:ℚ)⟩ node11 node5001
def node5003 : BoxExpr 3 := .add ⟨(-1/4722366482869645213696:ℚ),(48685281066161782391/590295810358705651712:ℚ)⟩ node4986 node19
def node5004 : BoxExpr 3 := .mul ⟨(-311585798823435407303/4722366482869645213696:ℚ),(1/4722366482869645213696:ℚ)⟩ node5003 node21
def node5005 : BoxExpr 3 := .mul ⟨(-1/4722366482869645213696:ℚ),(16061483418293853175/2361183241434822606848:ℚ)⟩ node5003 node5003
def node5006 : BoxExpr 3 := .mul ⟨(-1/4722366482869645213696:ℚ),(7227667538232233929/2361183241434822606848:ℚ)⟩ node5005 node24
def node5007 : BoxExpr 3 := .add ⟨(-38948224852929425913/590295810358705651712:ℚ),(14455335076464467859/4722366482869645213696:ℚ)⟩ node5004 node5006
def node5008 : BoxExpr 3 := .add ⟨(11317418802676915180791/4722366482869645213696:ℚ),(11720189665592219235967/4722366482869645213696:ℚ)⟩ node5002 node5007
def node5009 : BoxExpr 3 := .neg ⟨(-11720189665592219235967/4722366482869645213696:ℚ),(-11317418802676915180791/4722366482869645213696:ℚ)⟩ node5008
def node5010 : BoxExpr 3 := .add ⟨(197725996225695752627/4722366482869645213696:ℚ),(602240366927240918423/2361183241434822606848:ℚ)⟩ node4997 node5009
def node5011 : BoxExpr 3 := .var 2
def node5012 : BoxExpr 3 := .mul ⟨(1805276662524118093/73786976294838206464:ℚ),(115537706401543557953/4722366482869645213696:ℚ)⟩ node51 node5011
def node5013 : BoxExpr 3 := .add ⟨(38698764809943221325/73786976294838206464:ℚ),(2476720947836366164801/4722366482869645213696:ℚ)⟩ node5012 node301
def node5014 : BoxExpr 3 := .mul ⟨(2606918721028421704669/2361183241434822606848:ℚ),(5213837442056843409353/4722366482869645213696:ℚ)⟩ node68 node5013
def node5015 : BoxExpr 3 := .mul ⟨(3102069014328576546159/2361183241434822606848:ℚ),(6204138028657153092339/4722366482869645213696:ℚ)⟩ node5014 node349
def node5016 : BoxExpr 3 := .add ⟨(616268826014488700387/2361183241434822606848:ℚ),(154067206503622175097/590295810358705651712:ℚ)⟩ node5011 node351
def node5017 : BoxExpr 3 := .mul ⟨(-4408003799569134611/2361183241434822606848:ℚ),(-8816007599138269221/4722366482869645213696:ℚ)⟩ node5016 node4254
def node5018 : BoxExpr 3 := .mul ⟨(-9616874272399166649/4722366482869645213696:ℚ),(-9616874272399166647/4722366482869645213696:ℚ)⟩ node5017 node69
def node5019 : BoxExpr 3 := .add ⟨(6194521154384753925669/4722366482869645213696:ℚ),(1548630288596188481423/1180591620717411303424:ℚ)⟩ node5015 node5018
def node5020 : BoxExpr 3 := .add ⟨(16973523667301015877565/4722366482869645213696:ℚ),(16973523667301015877641/4722366482869645213696:ℚ)⟩ node5019 node358
def node5021 : BoxExpr 3 := .add ⟨(3054659758130183196687/1180591620717411303424:ℚ),(12218639032520732786829/4722366482869645213696:ℚ)⟩ node5020 node361
def node5022 : BoxExpr 3 := .add ⟨(3054656216355321044453/1180591620717411303424:ℚ),(6109312432710642088947/2361183241434822606848:ℚ)⟩ node5021 node325
def node5023 : BoxExpr 3 := .mul ⟨(17709333272880669855/4722366482869645213696:ℚ),(553416664777520933/147573952589676412928:ℚ)⟩ node5011 node5011
def node5024 : BoxExpr 3 := .neg ⟨(-553416664777520933/147573952589676412928:ℚ),(-17709333272880669855/4722366482869645213696:ℚ)⟩ node5023
def node5025 : BoxExpr 3 := .add ⟨(147020535924898891995/147573952589676412928:ℚ),(4704657149596764543841/4722366482869645213696:ℚ)⟩ node12 node5024
def node5026 : BoxExpr 3 := .sqrt ⟨(4713503499165859669883/4722366482869645213696:ℚ),(1178375874791464917471/1180591620717411303424:ℚ)⟩ node5025
def node5027 : BoxExpr 3 := .mul ⟨(2919312819189631790701/1180591620717411303424:ℚ),(182457051199351986919/73786976294838206464:ℚ)⟩ node50 node5026
def node5028 : BoxExpr 3 := .add ⟨(194741124264647129563/4722366482869645213696:ℚ),(194741124264647129565/4722366482869645213696:ℚ)⟩ node5011 node19
def node5029 : BoxExpr 3 := .mul ⟨(-155792899411717703653/4722366482869645213696:ℚ),(-77896449705858851825/2361183241434822606848:ℚ)⟩ node5028 node21
def node5030 : BoxExpr 3 := .mul ⟨(8030741709146926587/4722366482869645213696:ℚ),(2007685427286731647/1180591620717411303424:ℚ)⟩ node5028 node5028
def node5031 : BoxExpr 3 := .mul ⟨(903458442279029241/1180591620717411303424:ℚ),(3613833769116116965/4722366482869645213696:ℚ)⟩ node5030 node24
def node5032 : BoxExpr 3 := .add ⟨(-152179065642601586689/4722366482869645213696:ℚ),(-152179065642601586685/4722366482869645213696:ℚ)⟩ node5029 node5031
def node5033 : BoxExpr 3 := .add ⟨(11525072211115925576115/4722366482869645213696:ℚ),(11525072211115925576131/4722366482869645213696:ℚ)⟩ node5027 node5032
def node5034 : BoxExpr 3 := .neg ⟨(-11525072211115925576131/4722366482869645213696:ℚ),(-11525072211115925576115/4722366482869645213696:ℚ)⟩ node5033
def node5035 : BoxExpr 3 := .add ⟨(693552654305358601681/4722366482869645213696:ℚ),(693552654305358601779/4722366482869645213696:ℚ)⟩ node5022 node5034
def node5036 : BoxExpr 3 := .mul ⟨(1404413312222358093549/4722366482869645213696:ℚ),(351103328055589523389/1180591620717411303424:ℚ)⟩ node78 node5013
def node5037 : BoxExpr 3 := .mul ⟨(1671163348520847299701/4722366482869645213696:ℚ),(1671163348520847299711/4722366482869645213696:ℚ)⟩ node5036 node349
def node5038 : BoxExpr 3 := .add ⟨(2775197342901109143647/2361183241434822606848:ℚ),(1387598671450554571931/1180591620717411303424:ℚ)⟩ node5037 node385
def node5039 : BoxExpr 3 := .add ⟨(799132156322366109633/1180591620717411303424:ℚ),(799132156322366109741/1180591620717411303424:ℚ)⟩ node5038 node387
def node5040 : BoxExpr 3 := .mul ⟨(2915571365585697745855/4722366482869645213696:ℚ),(364446420698212218233/590295810358705651712:ℚ)⟩ node77 node5026
def node5041 : BoxExpr 3 := .neg ⟨(-364446420698212218233/590295810358705651712:ℚ),(-2915571365585697745855/4722366482869645213696:ℚ)⟩ node5040
def node5042 : BoxExpr 3 := .add ⟨(70239314925941673167/1180591620717411303424:ℚ),(280957259703766693109/4722366482869645213696:ℚ)⟩ node5039 node5041
def node5043 : BoxExpr 3 := .mul ⟨(-2362156624209126516611/4722366482869645213696:ℚ),(-2362156624209126516599/4722366482869645213696:ℚ)⟩ node98 node5013
def node5044 : BoxExpr 3 := .mul ⟨(304390688459764213737/2361183241434822606848:ℚ),(608781376919528427479/4722366482869645213696:ℚ)⟩ node68 node5011
def node5045 : BoxExpr 3 := .add ⟨(-1753375247289598089137/4722366482869645213696:ℚ),(-54792976477799940285/147573952589676412928:ℚ)⟩ node5043 node5044
def node5046 : BoxExpr 3 := .mul ⟨(-260800757865691264237/590295810358705651712:ℚ),(-1043203031462765056937/2361183241434822606848:ℚ)⟩ node5045 node349
def node5047 : BoxExpr 3 := .mul ⟨(368687337137134667907/295147905179352825856:ℚ),(5898997394194154686539/4722366482869645213696:ℚ)⟩ node5014 node399
def node5048 : BoxExpr 3 := .add ⟨(476573916408578071577/590295810358705651712:ℚ),(3812591331268624572665/4722366482869645213696:ℚ)⟩ node5046 node5047
def node5049 : BoxExpr 3 := .mul ⟨(-4571941824241967041/4722366482869645213696:ℚ),(-71436591003780735/73786976294838206464:ℚ)⟩ node5017 node103
def node5050 : BoxExpr 3 := .add ⟨(-11497536307139342379/2361183241434822606848:ℚ),(-22995072614278684755/4722366482869645213696:ℚ)⟩ node4317 node5049
def node5051 : BoxExpr 3 := .add ⟨(1894798129327172943929/2361183241434822606848:ℚ),(1894798129327172943955/2361183241434822606848:ℚ)⟩ node5048 node5050
def node5052 : BoxExpr 3 := .add ⟨(1027878373319753679533/1180591620717411303424:ℚ),(1027878373319753679575/1180591620717411303424:ℚ)⟩ node5051 node409
def node5053 : BoxExpr 3 := .add ⟨(289188453922040033837/2361183241434822606848:ℚ),(144594226961020016919/1180591620717411303424:ℚ)⟩ node5011 node5011
def node5054 : BoxExpr 3 := .neg ⟨(-144594226961020016919/1180591620717411303424:ℚ),(-289188453922040033837/2361183241434822606848:ℚ)⟩ node5053
def node5055 : BoxExpr 3 := .mul ⟨(4713503499165859669883/2361183241434822606848:ℚ),(1178375874791464917471/590295810358705651712:ℚ)⟩ node86 node5026
def node5056 : BoxExpr 3 := .inv ⟨(591405766498241338739/1180591620717411303424:ℚ),(2365623065992965354957/4722366482869645213696:ℚ)⟩ node5055
def node5057 : BoxExpr 3 := .mul ⟨(-289732226204141353981/4722366482869645213696:ℚ),(-144866113102070676989/2361183241434822606848:ℚ)⟩ node5054 node5056
def node5058 : BoxExpr 3 := .mul ⟨(-358891852839308633481/2361183241434822606848:ℚ),(-717783705678617266953/4722366482869645213696:ℚ)⟩ node50 node5057
def node5059 : BoxExpr 3 := .add ⟨(194741124264647129563/2361183241434822606848:ℚ),(194741124264647129565/2361183241434822606848:ℚ)⟩ node5028 node5028
def node5060 : BoxExpr 3 := .mul ⟨(87633505919091208303/2361183241434822606848:ℚ),(175267011838182416609/4722366482869645213696:ℚ)⟩ node5059 node24
def node5061 : BoxExpr 3 := .add ⟨(-3602626174457533754351/4722366482869645213696:ℚ),(-3602626174457533754347/4722366482869645213696:ℚ)⟩ node21 node5060
def node5062 : BoxExpr 3 := .add ⟨(-4320409880136151021313/4722366482869645213696:ℚ),(-1080102470034037755325/1180591620717411303424:ℚ)⟩ node5058 node5061
def node5063 : BoxExpr 3 := .neg ⟨(1080102470034037755325/1180591620717411303424:ℚ),(4320409880136151021313/4722366482869645213696:ℚ)⟩ node5062
def node5064 : BoxExpr 3 := .add ⟨(9009706577367244406529/4722366482869645213696:ℚ),(9009706577367244406561/4722366482869645213696:ℚ)⟩ node4323 node5063
def node5065 : BoxExpr 3 := .mul ⟨(10808609306252751226155/4722366482869645213696:ℚ),(5768451609772437100709/2361183241434822606848:ℚ)⟩ node112 node4988
def node5066 : BoxExpr 3 := .mul ⟨(12837213447472933533565/4722366482869645213696:ℚ),(13754409191800863831255/4722366482869645213696:ℚ)⟩ node5065 node304
def node5067 : BoxExpr 3 := .add ⟨(755107011447991178009/147573952589676412928:ℚ),(1502523712639427570173/147573952589676412928:ℚ)⟩ node5066 node448
def node5068 : BoxExpr 3 := .mul ⟨(11555863383200470393855/2361183241434822606848:ℚ),(11614697911162844696595/2361183241434822606848:ℚ)⟩ node111 node5001
def node5069 : BoxExpr 3 := .neg ⟨(-11614697911162844696595/2361183241434822606848:ℚ),(-11555863383200470393855/2361183241434822606848:ℚ)⟩ node5068
def node5070 : BoxExpr 3 := .add ⟨(467014272005014151549/2361183241434822606848:ℚ),(12484516019030370728913/2361183241434822606848:ℚ)⟩ node5067 node5069
def node5071 : BoxExpr 3 := .mul ⟨(-709551058670590038093/4722366482869645213696:ℚ),(-627459755844050746795/4722366482869645213696:ℚ)⟩ node131 node4988
def node5072 : BoxExpr 3 := .mul ⟨(52228121787811285989/4722366482869645213696:ℚ),(17576523232564703293/295147905179352825856:ℚ)⟩ node118 node4986
def node5073 : BoxExpr 3 := .add ⟨(-82165367110347344013/590295810358705651712:ℚ),(-346235384123015494107/4722366482869645213696:ℚ)⟩ node5071 node5072
def node5074 : BoxExpr 3 := .mul ⟨(-391833426743381233187/2361183241434822606848:ℚ),(-205609130791862632941/2361183241434822606848:ℚ)⟩ node5073 node304
def node5075 : BoxExpr 3 := .mul ⟨(663232486352277064725/2361183241434822606848:ℚ),(92816550425384013973/295147905179352825856:ℚ)⟩ node118 node4988
def node5076 : BoxExpr 3 := .mul ⟨(743808172727073299595/2361183241434822606848:ℚ),(1695087856813685952139/4722366482869645213696:ℚ)⟩ node5075 node461
def node5077 : BoxExpr 3 := .add ⟨(43996843247961508301/295147905179352825856:ℚ),(1283869595229960686257/4722366482869645213696:ℚ)⟩ node5074 node5076
def node5078 : BoxExpr 3 := .add ⟨(-2053351232927086709143/4722366482869645213696:ℚ),(2697443475801620459161/4722366482869645213696:ℚ)⟩ node5077 node476
def node5079 : BoxExpr 3 := .add ⟨(94447329657392904273/2361183241434822606848:ℚ),(483929578186687163401/2361183241434822606848:ℚ)⟩ node4986 node4986
def node5080 : BoxExpr 3 := .neg ⟨(-483929578186687163401/2361183241434822606848:ℚ),(-94447329657392904273/2361183241434822606848:ℚ)⟩ node5079
def node5081 : BoxExpr 3 := .mul ⟨(4697505440325394469047/2361183241434822606848:ℚ),(590177739388355929705/295147905179352825856:ℚ)⟩ node86 node5001
def node5082 : BoxExpr 3 := .inv ⟨(1180827809900672128261/2361183241434822606848:ℚ),(2373679549904455113083/4722366482869645213696:ℚ)⟩ node5081
def node5083 : BoxExpr 3 := .mul ⟨(-7601417553985563645/73786976294838206464:ℚ),(-94466224792053770259/4722366482869645213696:ℚ)⟩ node5080 node5082
def node5084 : BoxExpr 3 := .mul ⟨(-154051463091190406319/2361183241434822606848:ℚ),(-3564902424771234887/295147905179352825856:ℚ)⟩ node117 node5083
def node5085 : BoxExpr 3 := .neg ⟨(3564902424771234887/295147905179352825856:ℚ),(154051463091190406319/2361183241434822606848:ℚ)⟩ node5084
def node5086 : BoxExpr 3 := .add ⟨(1289969030902703734139/4722366482869645213696:ℚ),(405449518227910378591/1180591620717411303424:ℚ)⟩ node479 node5085
def node5087 : BoxExpr 3 := .add ⟨(-1026675616463543354571/2361183241434822606848:ℚ),(2697443475801620459161/4722366482869645213696:ℚ)⟩ node5077 node492
def node5088 : BoxExpr 3 := .mul ⟨(-2625552798810741861283/4722366482869645213696:ℚ),(-301115967434999891515/590295810358705651712:ℚ)⟩ node175 node4988
def node5089 : BoxExpr 3 := .mul ⟨(-467189255260318098411/4722366482869645213696:ℚ),(-11122670672211888145/590295810358705651712:ℚ)⟩ node148 node4986
def node5090 : BoxExpr 3 := .add ⟨(-1546371027035529979847/2361183241434822606848:ℚ),(-78059659526802944915/147573952589676412928:ℚ)⟩ node5088 node5089
def node5091 : BoxExpr 3 := .add ⟨(-3559931309331378058105/4722366482869645213696:ℚ),(-323361308779423667805/590295810358705651712:ℚ)⟩ node5090 node5089
def node5092 : BoxExpr 3 := .mul ⟨(-4244185028812162364231/4722366482869645213696:ℚ),(-3072408687437181523941/4722366482869645213696:ℚ)⟩ node5091 node304
def node5093 : BoxExpr 3 := .mul ⟨(-2467091727715911891781/4722366482869645213696:ℚ),(-564976589032173696597/1180591620717411303424:ℚ)⟩ node148 node4988
def node5094 : BoxExpr 3 := .mul ⟨(24766978083186691707/590295810358705651712:ℚ),(1022286499782243619693/4722366482869645213696:ℚ)⟩ node36 node4986
def node5095 : BoxExpr 3 := .add ⟨(-2268955903050418358125/4722366482869645213696:ℚ),(-1237619856346451166695/4722366482869645213696:ℚ)⟩ node5093 node5094
def node5096 : BoxExpr 3 := .mul ⟨(-2589839568805127855513/4722366482869645213696:ℚ),(-1387977493296135310751/4722366482869645213696:ℚ)⟩ node5095 node461
def node5097 : BoxExpr 3 := .add ⟨(-213563268675540319367/147573952589676412928:ℚ),(-1115096545183329208673/1180591620717411303424:ℚ)⟩ node5092 node5096
def node5098 : BoxExpr 3 := .mul ⟨(3101769529109050576011/590295810358705651712:ℚ),(13594947622720363430179/2361183241434822606848:ℚ)⟩ node4989 node514
def node5099 : BoxExpr 3 := .add ⟨(22224316664067276752575/4722366482869645213696:ℚ),(25801917752144591549607/4722366482869645213696:ℚ)⟩ node5096 node5098
def node5100 : BoxExpr 3 := .add ⟨(15390292066449986532831/4722366482869645213696:ℚ),(21341531571411274714915/4722366482869645213696:ℚ)⟩ node5097 node5099
def node5101 : BoxExpr 3 := .mul ⟨(-10515872387531720977/2361183241434822606848:ℚ),(-3735682906975582657/1180591620717411303424:ℚ)⟩ node4992 node189
def node5102 : BoxExpr 3 := .add ⟨(-29859329980894732203/4722366482869645213696:ℚ),(-23632658880249876049/4722366482869645213696:ℚ)⟩ node4374 node5101
def node5103 : BoxExpr 3 := .add ⟨(-9671728796681505613/1180591620717411303424:ℚ),(-16161293066298710735/2361183241434822606848:ℚ)⟩ node4374 node5102
def node5104 : BoxExpr 3 := .add ⟨(15351605151263260510379/4722366482869645213696:ℚ),(21309208985278677293445/4722366482869645213696:ℚ)⟩ node5100 node5103
def node5105 : BoxExpr 3 := .add ⟨(13227669214814915940951/2361183241434822606848:ℚ),(9475670006151530941997/1180591620717411303424:ℚ)⟩ node5104 node527
def node5106 : BoxExpr 3 := .mul ⟨(-2373679549904455113083/2361183241434822606848:ℚ),(-1180827809900672128261/1180591620717411303424:ℚ)⟩ node6 node5082
def node5107 : BoxExpr 3 := .mul ⟨(-7601417553985563645/36893488147419103232:ℚ),(-94466224792053770259/2361183241434822606848:ℚ)⟩ node86 node5083
def node5108 : BoxExpr 3 := .mul ⟨(18691101117994951515583/4722366482869645213696:ℚ),(18881910145105989422445/4722366482869645213696:ℚ)⟩ node5081 node5081
def node5109 : BoxExpr 3 := .inv ⟨(36908251447998302553/147573952589676412928:ℚ),(1193120996871632600105/4722366482869645213696:ℚ)⟩ node5108
def node5110 : BoxExpr 3 := .mul ⟨(-122913437371511273045/2361183241434822606848:ℚ),(-11813003300326852023/1180591620717411303424:ℚ)⟩ node5107 node5109
def node5111 : BoxExpr 3 := .neg ⟨(11813003300326852023/1180591620717411303424:ℚ),(122913437371511273045/2361183241434822606848:ℚ)⟩ node5110
def node5112 : BoxExpr 3 := .mul ⟨(-25191373061129338267/2361183241434822606848:ℚ),(-1890080528052296323/4722366482869645213696:ℚ)⟩ node5080 node5111
def node5113 : BoxExpr 3 := .add ⟨(-1199435461482792225675/1180591620717411303424:ℚ),(-4725201320130740809367/4722366482869645213696:ℚ)⟩ node5106 node5112
def node5114 : BoxExpr 3 := .mul ⟨(-5947476464153020693695/2361183241434822606848:ℚ),(-5848783848455702078249/2361183241434822606848:ℚ)⟩ node11 node5113
def node5115 : BoxExpr 3 := .add ⟨(-955602886715420086883/590295810358705651712:ℚ),(-7447437862328723464171/4722366482869645213696:ℚ)⟩ node5114 node172
def node5116 : BoxExpr 3 := .neg ⟨(7447437862328723464171/4722366482869645213696:ℚ),(955602886715420086883/590295810358705651712:ℚ)⟩ node5115
def cert_iv34 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (250831/4096000:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (168911/4096000:ℚ)],
    whole := node5010, centerValue := node5035, gradient := ![node5042, node5052, node5064],
    hessian := ![![node5070, node5078, node5086], ![node5087, node5105, node4381], ![node5086, node4381, node5116]] }

end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part9
end

section
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646CheckB4Part9
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part9

theorem cert_iv32_check : cert_iv32.check = true := by decide +kernel

theorem cert_iv32_lower_pos : 0 < cert_iv32.lower := by decide +kernel

theorem positive_iv32 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (0:ℝ) ≤ r) (hrhi : r ≤ (155606922197/8000003688788:ℝ)) :
    0 < node4776.eval ![A,ρ,r] := by
  apply cert_iv32.positive_sound cert_iv32_check cert_iv32_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv32,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv32,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv32,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv33_check : cert_iv33.check = true := by decide +kernel

theorem cert_iv33_lower_pos : 0 < cert_iv33.lower := by decide +kernel

theorem positive_iv33 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (155606922197/8000003688788:ℝ) ≤ r) (hrhi : r ≤ (1/50:ℝ)) :
    0 < node4890.eval ![A,ρ,r] := by
  apply cert_iv33.positive_sound cert_iv33_check cert_iv33_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv33,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv33,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv33,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv34_check : cert_iv34.check = true := by decide +kernel

theorem cert_iv34_lower_pos : 0 < cert_iv34.lower := by decide +kernel

theorem positive_iv34 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (1/50:ℝ) ≤ r) (hrhi : r ≤ (209871/2048000:ℝ)) :
    0 < node5010.eval ![A,ρ,r] := by
  apply cert_iv34.positive_sound cert_iv34_check cert_iv34_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv34,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv34,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv34,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part9
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
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646BoundB4Part9
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part9
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate.CapacityCore
noncomputable section
namespace Parameters
def b : ℚ := (103531361122339324647880530522418473224550678173/6474633415922124204664207433178390079472570088576:ℚ)
def c : ℚ := (148022665013912365111/4722366482869645213696:ℚ)
def theta : ℚ := (105113898053531722649817636563532003778556764000751/182628568201966125342452015454275643968150995402752:ℚ)
end Parameters

theorem iv_shape32 : SplitDataB4Part9.node4776.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 1 Parameters.b Parameters.c Parameters.theta (1)).canonicalize := by decide +kernel

theorem iv_bound32 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (0:ℝ) ≤ r) (hrhi : r ≤ (155606922197/8000003688788:ℝ)) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 1 r := by
    norm_num [sourceFADomain] <;> constructor <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part9.node4776 3 4 1
    Parameters.b Parameters.c Parameters.theta (1) iv_shape32 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part9.positive_iv32 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part9.node4776.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape33 : SplitDataB4Part9.node4890.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 1 Parameters.b Parameters.c Parameters.theta (1)).canonicalize := by decide +kernel

theorem iv_bound33 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (155606922197/8000003688788:ℝ) ≤ r) (hrhi : r ≤ (1/50:ℝ)) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 1 r := by
    norm_num [sourceFADomain] <;> constructor <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part9.node4890 3 4 1
    Parameters.b Parameters.c Parameters.theta (1) iv_shape33 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part9.positive_iv33 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part9.node4890.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape34 : SplitDataB4Part9.node5010.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 2 Parameters.b Parameters.c Parameters.theta (1)).canonicalize := by decide +kernel

theorem iv_bound34 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (1/50:ℝ) ≤ r) (hrhi : r ≤ (209871/2048000:ℝ)) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 2 r := by
    norm_num [sourceFADomain] <;> constructor <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part9.node5010 3 4 2
    Parameters.b Parameters.c Parameters.theta (1) iv_shape34 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part9.positive_iv34 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part9.node5010.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem actual_bound (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (r : ℝ)
    (hrlo : (0:ℝ) ≤ r) (hrhi : r ≤ (209871/2048000:ℝ)) : fA A r+3/10^6 ≤ l40Lhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) r := by
  have hc : 0 ≤ (Parameters.c:ℝ) := by norm_num [Parameters.c]
  have hθ : 0 ≤ (Parameters.theta:ℝ) := by norm_num [Parameters.theta]
  by_cases h0 : r ≤ (155606922197/8000003688788:ℝ)
  · have h := iv_bound32 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (1) r hθ hc (Or.inr rfl))
  by_cases h1 : r ≤ (1/50:ℝ)
  · have h := iv_bound33 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (1) r hθ hc (Or.inr rfl))
  have h := iv_bound34 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
  exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
    (Parameters.theta:ℝ) (1) r hθ hc (Or.inr rfl))
end
end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part9
end

section
-- Source module: Solutions.Sol_GaussLocalMaxCase1FamilyAdaptive0Seed25646B4Part9
set_option autoImplicit false
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate
open GaussLocalMaxColoring.Certificate.CapacityCore
theorem solution (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (r : ℝ)
    (hrlo : (0:ℝ) ≤ r) (hrhi : r ≤ (209871/2048000:ℝ)) :
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
  have h := GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part9.actual_bound A ρ hAlo hAhi hρlo hρhi r hrlo hrhi
  simpa only [Case2Static,constructedA,constructedMu,constructedMass,constructedKappa,thresholdCapacity,
    GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part9.Parameters.b,GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part9.Parameters.c,GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part9.Parameters.theta,
    show ¬ (4:ℕ)=1 by decide,show ¬ (4:ℕ)=2 by decide,show ¬ (4:ℕ)=3 by decide,ite_false,and_assoc] using h
end

#print axioms solution
