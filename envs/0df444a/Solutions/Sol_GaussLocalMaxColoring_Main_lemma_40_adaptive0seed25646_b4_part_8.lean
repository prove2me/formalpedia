-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_40_adaptive0seed25646_b4_part_8
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T14:29:15.560527+00:00
-- url     : https://prove2.me/submissions/0faffbbf-423b-4305-9279-bef7a88f17c1

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
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646DefsB4Part8
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part8

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
def node407 : BoxExpr 3 := .mul ⟨(17026592217487914599/590295810358705651712:ℚ),(17026592217487914605/590295810358705651712:ℚ)⟩ node264 node382
def node408 : BoxExpr 3 := .mul ⟨(214611489749779220183/4722366482869645213696:ℚ),(53652872437444805065/1180591620717411303424:ℚ)⟩ node407 node313
def node409 : BoxExpr 3 := .mul ⟨(160958617312334415137/2361183241434822606848:ℚ),(160958617312334415195/2361183241434822606848:ℚ)⟩ node408 node315
def node411 : BoxExpr 3 := .mul ⟨(1985879505045154496735/2361183241434822606848:ℚ),(1985879505045154496741/2361183241434822606848:ℚ)⟩ node68 node51
def node412 : BoxExpr 3 := .mul ⟨(4726142958811166820663/4722366482869645213696:ℚ),(590767869851395852585/590295810358705651712:ℚ)⟩ node411 node349
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
def node546 : BoxExpr 3 := .lit (413/250:ℚ)
def node4248 : BoxExpr 3 := .var 2
def node4249 : BoxExpr 3 := .mul ⟨(-328862323967089307341/4722366482869645213696:ℚ),(-269855214091919469995/4722366482869645213696:ℚ)⟩ node13 node4248
def node4250 : BoxExpr 3 := .add ⟨(2032320917467733299507/4722366482869645213696:ℚ),(2091328027342903136853/4722366482869645213696:ℚ)⟩ node4249 node301
def node4251 : BoxExpr 3 := .mul ⟨(1065873387919237375453/1180591620717411303424:ℚ),(4417866783385829142831/4722366482869645213696:ℚ)⟩ node36 node4250
def node4252 : BoxExpr 3 := .mul ⟨(632960439266912919517/590295810358705651712:ℚ),(329189007316378672981/295147905179352825856:ℚ)⟩ node4251 node304
def node4253 : BoxExpr 3 := .add ⟨(29897848687840907493/1180591620717411303424:ℚ),(67307845669323878171/1180591620717411303424:ℚ)⟩ node4248 node306
def node4254 : BoxExpr 3 := .lit (-312036485317165491123742954302726779952711837284451442610337461713791988599992016921959547053639792687389742941247471/43624816861295183480575856049041147371514908121470076568809273260400089500027672742507792890927579075052513478012043264:ℚ)
def node4255 : BoxExpr 3 := .mul ⟨(-240717384140583815/590295810358705651712:ℚ),(-427702408597404405/2361183241434822606848:ℚ)⟩ node4253 node4254
def node4256 : BoxExpr 3 := .mul ⟨(-2102682923942634797/4722366482869645213696:ℚ),(-932228043621447455/4722366482869645213696:ℚ)⟩ node4255 node37
def node4257 : BoxExpr 3 := .add ⟨(5061580831211360721339/4722366482869645213696:ℚ),(5266091889018437320241/4722366482869645213696:ℚ)⟩ node4252 node4256
def node4258 : BoxExpr 3 := .add ⟨(7888012543175373540573/2361183241434822606848:ℚ),(16107855885878227817483/4722366482869645213696:ℚ)⟩ node4257 node316
def node4259 : BoxExpr 3 := .add ⟨(5507039426694462864391/2361183241434822606848:ℚ),(5680016424639741494109/2361183241434822606848:ℚ)⟩ node4258 node323
def node4260 : BoxExpr 3 := .add ⟨(5507032343144738559923/2361183241434822606848:ℚ),(11360018682180034379283/4722366482869645213696:ℚ)⟩ node4259 node325
def node4261 : BoxExpr 3 := .mul ⟨(6098954759370220503/295147905179352825856:ℚ),(71025729291304807957/2361183241434822606848:ℚ)⟩ node4248 node4248
def node4262 : BoxExpr 3 := .neg ⟨(-71025729291304807957/2361183241434822606848:ℚ),(-6098954759370220503/295147905179352825856:ℚ)⟩ node4261
def node4263 : BoxExpr 3 := .add ⟨(2290157512143517798891/2361183241434822606848:ℚ),(289048950419982605353/295147905179352825856:ℚ)⟩ node12 node4262
def node4264 : BoxExpr 3 := .sqrt ⟨(1162699610595890377011/1180591620717411303424:ℚ),(4673320148026626629987/4722366482869645213696:ℚ)⟩ node4263
def node4265 : BoxExpr 3 := .mul ⟨(5756689074039977093687/2361183241434822606848:ℚ),(11586476505988824961861/4722366482869645213696:ℚ)⟩ node11 node4264
def node4266 : BoxExpr 3 := .neg ⟨(169710045478127874867/1180591620717411303424:ℚ),(819035436872704091751/4722366482869645213696:ℚ)⟩ node4248
def node4267 : BoxExpr 3 := .add ⟨(560781019840770369125/4722366482869645213696:ℚ),(700976274800962961409/4722366482869645213696:ℚ)⟩ node332 node4266
def node4268 : BoxExpr 3 := .mul ⟨(400397648166310043555/4722366482869645213696:ℚ),(500497060207887554447/4722366482869645213696:ℚ)⟩ node4267 node335
def node4269 : BoxExpr 3 := .neg ⟨(-500497060207887554447/4722366482869645213696:ℚ),(-400397648166310043555/4722366482869645213696:ℚ)⟩ node4268
def node4270 : BoxExpr 3 := .add ⟨(11012881087872066632927/4722366482869645213696:ℚ),(5593039428911257459153/2361183241434822606848:ℚ)⟩ node4265 node4269
def node4271 : BoxExpr 3 := .mul ⟨(66592746106091481333/4722366482869645213696:ℚ),(104051165790767939585/4722366482869645213696:ℚ)⟩ node4267 node4267
def node4272 : BoxExpr 3 := .mul ⟨(55005608283631563581/4722366482869645213696:ℚ),(42973131471587159049/2361183241434822606848:ℚ)⟩ node4271 node340
def node4273 : BoxExpr 3 := .add ⟨(2766971674038924549127/1180591620717411303424:ℚ),(2818006280191422309101/1180591620717411303424:ℚ)⟩ node4270 node4272
def node4274 : BoxExpr 3 := .neg ⟨(-2818006280191422309101/1180591620717411303424:ℚ),(-2766971674038924549127/1180591620717411303424:ℚ)⟩ node4273
def node4275 : BoxExpr 3 := .add ⟨(-128980217238106058279/2361183241434822606848:ℚ),(292131986024336182775/4722366482869645213696:ℚ)⟩ node4260 node4274
def node4276 : BoxExpr 3 := .var 2
def node4277 : BoxExpr 3 := .mul ⟨(-74804643443636049019/1180591620717411303424:ℚ),(-299218573774544196075/4722366482869645213696:ℚ)⟩ node51 node4276
def node4278 : BoxExpr 3 := .add ⟨(515491166915069602693/1180591620717411303424:ℚ),(2061964667660278410773/4722366482869645213696:ℚ)⟩ node4277 node301
def node4279 : BoxExpr 3 := .mul ⟨(271294910056308038137/295147905179352825856:ℚ),(4340718560900928610205/4722366482869645213696:ℚ)⟩ node68 node4278
def node4280 : BoxExpr 3 := .mul ⟨(5165181575887305008455/4722366482869645213696:ℚ),(2582590787943652504237/2361183241434822606848:ℚ)⟩ node4279 node349
def node4281 : BoxExpr 3 := .add ⟨(194411388714329571327/4722366482869645213696:ℚ),(194411388714329571329/4722366482869645213696:ℚ)⟩ node4276 node351
def node4282 : BoxExpr 3 := .mul ⟨(-695285972579869833/2361183241434822606848:ℚ),(-1390571945159739665/4722366482869645213696:ℚ)⟩ node4281 node4254
def node4283 : BoxExpr 3 := .mul ⟨(-1516894740952119887/4722366482869645213696:ℚ),(-1516894740952119885/4722366482869645213696:ℚ)⟩ node4282 node69
def node4284 : BoxExpr 3 := .add ⟨(645458085143294111071/590295810358705651712:ℚ),(5163664681146352888589/4722366482869645213696:ℚ)⟩ node4280 node4283
def node4285 : BoxExpr 3 := .add ⟨(996416699628913427529/295147905179352825856:ℚ),(7971333597031307420269/2361183241434822606848:ℚ)⟩ node4284 node358
def node4286 : BoxExpr 3 := .add ⟨(11187782559282331749647/4722366482869645213696:ℚ),(5593891279641165874863/2361183241434822606848:ℚ)⟩ node4285 node361
def node4287 : BoxExpr 3 := .add ⟨(11187768392182883140711/4722366482869645213696:ℚ),(11187768392182883140791/4722366482869645213696:ℚ)⟩ node4286 node325
def node4288 : BoxExpr 3 := .mul ⟨(14847106963544861573/590295810358705651712:ℚ),(59388427854179446293/2361183241434822606848:ℚ)⟩ node4276 node4276
def node4289 : BoxExpr 3 := .neg ⟨(-59388427854179446293/2361183241434822606848:ℚ),(-14847106963544861573/590295810358705651712:ℚ)⟩ node4288
def node4290 : BoxExpr 3 := .add ⟨(2301794813580643160555/2361183241434822606848:ℚ),(575448703395160790139/590295810358705651712:ℚ)⟩ node12 node4289
def node4291 : BoxExpr 3 := .sqrt ⟨(4662599849460901895281/4722366482869645213696:ℚ),(4662599849460901895283/4722366482869645213696:ℚ)⟩ node4290
def node4292 : BoxExpr 3 := .mul ⟨(11551142383742094797445/4722366482869645213696:ℚ),(5775571191871047398729/2361183241434822606848:ℚ)⟩ node50 node4291
def node4293 : BoxExpr 3 := .neg ⟨(748937809392607795609/4722366482869645213696:ℚ),(374468904696303897805/2361183241434822606848:ℚ)⟩ node4276
def node4294 : BoxExpr 3 := .add ⟨(315439323660433332633/2361183241434822606848:ℚ),(157719661830216666317/1180591620717411303424:ℚ)⟩ node332 node4293
def node4295 : BoxExpr 3 := .mul ⟨(450447354187098798999/4722366482869645213696:ℚ),(225223677093549399501/2361183241434822606848:ℚ)⟩ node4294 node335
def node4296 : BoxExpr 3 := .neg ⟨(-225223677093549399501/2361183241434822606848:ℚ),(-450447354187098798999/4722366482869645213696:ℚ)⟩ node4295
def node4297 : BoxExpr 3 := .add ⟨(11100695029554995998443/4722366482869645213696:ℚ),(11100695029554995998459/4722366482869645213696:ℚ)⟩ node4292 node4296
def node4298 : BoxExpr 3 := .mul ⟨(42140722145261015531/2361183241434822606848:ℚ),(10535180536315253883/590295810358705651712:ℚ)⟩ node4294 node4294
def node4299 : BoxExpr 3 := .mul ⟨(69616472983971197657/4722366482869645213696:ℚ),(69616472983971197659/4722366482869645213696:ℚ)⟩ node4298 node340
def node4300 : BoxExpr 3 := .add ⟨(2792577875634741799025/1180591620717411303424:ℚ),(5585155751269483598059/2361183241434822606848:ℚ)⟩ node4297 node4299
def node4301 : BoxExpr 3 := .neg ⟨(-5585155751269483598059/2361183241434822606848:ℚ),(-2792577875634741799025/1180591620717411303424:ℚ)⟩ node4300
def node4302 : BoxExpr 3 := .add ⟨(17456889643915944593/4722366482869645213696:ℚ),(17456889643915944691/4722366482869645213696:ℚ)⟩ node4287 node4301
def node4303 : BoxExpr 3 := .mul ⟨(584613828038242649807/2361183241434822606848:ℚ),(1169227656076485299619/4722366482869645213696:ℚ)⟩ node78 node4278
def node4304 : BoxExpr 3 := .mul ⟨(695653618456513305977/2361183241434822606848:ℚ),(1391307236913026611961/4722366482869645213696:ℚ)⟩ node4303 node349
def node4305 : BoxExpr 3 := .add ⟨(5270538574194397599547/4722366482869645213696:ℚ),(2635269287097198799987/2361183241434822606848:ℚ)⟩ node4304 node385
def node4306 : BoxExpr 3 := .add ⟨(2916672513681643750785/4722366482869645213696:ℚ),(1458336256840821875607/2361183241434822606848:ℚ)⟩ node4305 node387
def node4307 : BoxExpr 3 := .mul ⟨(2884084548293667695761/4722366482869645213696:ℚ),(1442042274146833847885/2361183241434822606848:ℚ)⟩ node77 node4291
def node4308 : BoxExpr 3 := .neg ⟨(-1442042274146833847885/2361183241434822606848:ℚ),(-2884084548293667695761/4722366482869645213696:ℚ)⟩ node4307
def node4309 : BoxExpr 3 := .add ⟨(32587965387976055015/4722366482869645213696:ℚ),(32587965387976055453/4722366482869645213696:ℚ)⟩ node4306 node4308
def node4310 : BoxExpr 3 := .mul ⟨(-983292748998200148727/2361183241434822606848:ℚ),(-491646374499100074361/1180591620717411303424:ℚ)⟩ node98 node4278
def node4311 : BoxExpr 3 := .mul ⟨(-788308427680242207879/2361183241434822606848:ℚ),(-1576616855360484415751/4722366482869645213696:ℚ)⟩ node68 node4276
def node4312 : BoxExpr 3 := .add ⟨(-885800588339221178303/1180591620717411303424:ℚ),(-3543202353356884713195/4722366482869645213696:ℚ)⟩ node4310 node4311
def node4313 : BoxExpr 3 := .mul ⟨(-2108093770470232644227/2361183241434822606848:ℚ),(-4216187540940465288431/4722366482869645213696:ℚ)⟩ node4312 node349
def node4314 : BoxExpr 3 := .mul ⟨(4911140357606418265747/4722366482869645213696:ℚ),(4911140357606418265771/4722366482869645213696:ℚ)⟩ node4279 node399
def node4315 : BoxExpr 3 := .add ⟨(694952816665952977293/4722366482869645213696:ℚ),(173738204166488244335/1180591620717411303424:ℚ)⟩ node4313 node4314
def node4316 : BoxExpr 3 := .lit (-312036485317165491123742954302726779952711837284451442610337461713791988599992016921959547053639792687389742941247471/87249633722590366961151712098082294743029816242940153137618546520800179000055345485015585781855158150105026956024086528:ℚ)
def node4317 : BoxExpr 3 := .mul ⟨(-18423130790036717717/4722366482869645213696:ℚ),(-18423130790036717715/4722366482869645213696:ℚ)⟩ node4316 node69
def node4318 : BoxExpr 3 := .mul ⟨(-721144346145385923/4722366482869645213696:ℚ),(-721144346145385921/4722366482869645213696:ℚ)⟩ node4282 node103
def node4319 : BoxExpr 3 := .add ⟨(-2393034392022762955/590295810358705651712:ℚ),(-4786068784045525909/1180591620717411303424:ℚ)⟩ node4317 node4318
def node4320 : BoxExpr 3 := .add ⟨(675808541529770873653/4722366482869645213696:ℚ),(84476067691221359213/590295810358705651712:ℚ)⟩ node4315 node4319
def node4321 : BoxExpr 3 := .add ⟨(997725776154439703927/4722366482869645213696:ℚ),(498862888077219852047/2361183241434822606848:ℚ)⟩ node4320 node409
def node4322 : BoxExpr 3 := .mul ⟨(-18423130790036717717/2361183241434822606848:ℚ),(-4605782697509179429/590295810358705651712:ℚ)⟩ node4254 node69
def node4323 : BoxExpr 3 := .add ⟨(4689296697231093385229/4722366482869645213696:ℚ),(146540521788471668289/147573952589676412928:ℚ)⟩ node412 node4322
def node4324 : BoxExpr 3 := .add ⟨(-374468904696303897805/1180591620717411303424:ℚ),(-748937809392607795609/2361183241434822606848:ℚ)⟩ node4276 node4276
def node4325 : BoxExpr 3 := .neg ⟨(748937809392607795609/2361183241434822606848:ℚ),(374468904696303897805/1180591620717411303424:ℚ)⟩ node4324
def node4326 : BoxExpr 3 := .mul ⟨(4662599849460901895281/2361183241434822606848:ℚ),(4662599849460901895283/2361183241434822606848:ℚ)⟩ node86 node4291
def node4327 : BoxExpr 3 := .inv ⟨(2391449611648432048899/4722366482869645213696:ℚ),(2391449611648432048901/4722366482869645213696:ℚ)⟩ node4326
def node4328 : BoxExpr 3 := .mul ⟨(758537923694737040509/4722366482869645213696:ℚ),(5926077528865133129/36893488147419103232:ℚ)⟩ node4325 node4327
def node4329 : BoxExpr 3 := .mul ⟨(469801175468611129189/1180591620717411303424:ℚ),(939602350937222258383/2361183241434822606848:ℚ)⟩ node50 node4328
def node4330 : BoxExpr 3 := .add ⟨(2625487185321685599667/2361183241434822606848:ℚ),(5250974370643371199345/4722366482869645213696:ℚ)⟩ node4329 node335
def node4331 : BoxExpr 3 := .mul ⟨(-157719661830216666317/1180591620717411303424:ℚ),(-315439323660433332633/2361183241434822606848:ℚ)⟩ node422 node4294
def node4332 : BoxExpr 3 := .mul ⟨(-157719661830216666317/1180591620717411303424:ℚ),(-315439323660433332633/2361183241434822606848:ℚ)⟩ node4294 node422
def node4333 : BoxExpr 3 := .add ⟨(-157719661830216666317/590295810358705651712:ℚ),(-315439323660433332633/1180591620717411303424:ℚ)⟩ node4331 node4332
def node4334 : BoxExpr 3 := .mul ⟨(-1042211525374071731023/4722366482869645213696:ℚ),(-1042211525374071731019/4722366482869645213696:ℚ)⟩ node4333 node340
def node4335 : BoxExpr 3 := .add ⟨(4208762845269299468311/4722366482869645213696:ℚ),(2104381422634649734163/2361183241434822606848:ℚ)⟩ node4330 node4334
def node4336 : BoxExpr 3 := .neg ⟨(-2104381422634649734163/2361183241434822606848:ℚ),(-4208762845269299468311/4722366482869645213696:ℚ)⟩ node4335
def node4337 : BoxExpr 3 := .add ⟨(480533851961793916903/4722366482869645213696:ℚ),(480533851961793916937/4722366482869645213696:ℚ)⟩ node4323 node4336
def node4338 : BoxExpr 3 := .mul ⟨(4578793406326867353749/2361183241434822606848:ℚ),(4720704252208893650581/2361183241434822606848:ℚ)⟩ node112 node4250
def node4339 : BoxExpr 3 := .mul ⟨(10876320278298189377233/4722366482869645213696:ℚ),(5628069918135007982593/2361183241434822606848:ℚ)⟩ node4338 node304
def node4340 : BoxExpr 3 := .add ⟨(5550632799290243384989/1180591620717411303424:ℚ),(45582489448930834379467/4722366482869645213696:ℚ)⟩ node4339 node448
def node4341 : BoxExpr 3 := .mul ⟨(2860241042065890327447/590295810358705651712:ℚ),(22992735128291003019537/4722366482869645213696:ℚ)⟩ node111 node4264
def node4342 : BoxExpr 3 := .neg ⟨(-22992735128291003019537/4722366482869645213696:ℚ),(-2860241042065890327447/590295810358705651712:ℚ)⟩ node4341
def node4343 : BoxExpr 3 := .add ⟨(-790203931130029479581/4722366482869645213696:ℚ),(22700561112403711759891/4722366482869645213696:ℚ)⟩ node4340 node4342
def node4344 : BoxExpr 3 := .mul ⟨(-580672410279214610299/4722366482869645213696:ℚ),(-531614847274048094173/4722366482869645213696:ℚ)⟩ node131 node4250
def node4345 : BoxExpr 3 := .mul ⟨(-237981657387899523409/2361183241434822606848:ℚ),(-375389625349893618049/4722366482869645213696:ℚ)⟩ node118 node4248
def node4346 : BoxExpr 3 := .add ⟨(-1056635725055013657117/4722366482869645213696:ℚ),(-453502236311970856111/2361183241434822606848:ℚ)⟩ node4344 node4345
def node4347 : BoxExpr 3 := .mul ⟨(-39366608646278006719/147573952589676412928:ℚ),(-1077234793392937200277/4722366482869645213696:ℚ)⟩ node4346 node304
def node4348 : BoxExpr 3 := .mul ⟨(280961634316340499171/1180591620717411303424:ℚ),(303831609526672764817/1180591620717411303424:ℚ)⟩ node118 node4250
def node4349 : BoxExpr 3 := .mul ⟨(1260381927167834704081/4722366482869645213696:ℚ),(693601073117410035691/2361183241434822606848:ℚ)⟩ node4348 node461
def node4350 : BoxExpr 3 := .add ⟨(650450486938489073/4722366482869645213696:ℚ),(309967352841882871105/4722366482869645213696:ℚ)⟩ node4347 node4349
def node4351 : BoxExpr 3 := .add ⟨(-1378325137203766176443/2361183241434822606848:ℚ),(1723541233413542644009/4722366482869645213696:ℚ)⟩ node4350 node476
def node4352 : BoxExpr 3 := .add ⟨(-819035436872704091751/2361183241434822606848:ℚ),(-169710045478127874867/590295810358705651712:ℚ)⟩ node4248 node4248
def node4353 : BoxExpr 3 := .neg ⟨(169710045478127874867/590295810358705651712:ℚ),(819035436872704091751/2361183241434822606848:ℚ)⟩ node4352
def node4354 : BoxExpr 3 := .mul ⟨(1162699610595890377011/590295810358705651712:ℚ),(4673320148026626629987/2361183241434822606848:ℚ)⟩ node86 node4264
def node4355 : BoxExpr 3 := .inv ⟨(1192981889329121711615/2361183241434822606848:ℚ),(599379479534630194931/1180591620717411303424:ℚ)⟩ node4354
def node4356 : BoxExpr 3 := .mul ⟨(685964586364244984177/4722366482869645213696:ℚ),(207909756963574848867/1180591620717411303424:ℚ)⟩ node4353 node4355
def node4357 : BoxExpr 3 := .mul ⟨(25886467069262980919/295147905179352825856:ℚ),(526691272116396659839/4722366482869645213696:ℚ)⟩ node117 node4356
def node4358 : BoxExpr 3 := .neg ⟨(-526691272116396659839/4722366482869645213696:ℚ),(-25886467069262980919/295147905179352825856:ℚ)⟩ node4357
def node4359 : BoxExpr 3 := .add ⟨(176559829997491829027/1180591620717411303424:ℚ),(449755836810526503511/2361183241434822606848:ℚ)⟩ node479 node4358
def node4360 : BoxExpr 3 := .add ⟨(-2756650274407532352885/4722366482869645213696:ℚ),(1723541233413542644009/4722366482869645213696:ℚ)⟩ node4350 node492
def node4361 : BoxExpr 3 := .mul ⟨(-2148662951553092239189/4722366482869645213696:ℚ),(-2040962373109016113685/4722366482869645213696:ℚ)⟩ node175 node4250
def node4362 : BoxExpr 3 := .mul ⟨(639553563652183568345/4722366482869645213696:ℚ),(790702972151774130563/4722366482869645213696:ℚ)⟩ node148 node4248
def node4363 : BoxExpr 3 := .add ⟨(-377277346975227167711/1180591620717411303424:ℚ),(-625129700478620991561/2361183241434822606848:ℚ)⟩ node4361 node4362
def node4364 : BoxExpr 3 := .add ⟨(-869555824248725102499/4722366482869645213696:ℚ),(-459556428805467852559/4722366482869645213696:ℚ)⟩ node4363 node4362
def node4365 : BoxExpr 3 := .mul ⟨(-1036692983743558416611/4722366482869645213696:ℚ),(-545807864876880036119/4722366482869645213696:ℚ)⟩ node4364 node304
def node4366 : BoxExpr 3 := .mul ⟨(-31546622033197292009/73786976294838206464:ℚ),(-1914704108394807231103/4722366482869645213696:ℚ)⟩ node148 node4250
def node4367 : BoxExpr 3 := .mul ⟨(-108136713958411635515/295147905179352825856:ℚ),(-712050619891617386585/2361183241434822606848:ℚ)⟩ node36 node4248
def node4368 : BoxExpr 3 := .add ⟨(-234323202091200803551/295147905179352825856:ℚ),(-3338805348178042004273/4722366482869645213696:ℚ)⟩ node4366 node4367
def node4369 : BoxExpr 3 := .mul ⟨(-2139696059668824079705/2361183241434822606848:ℚ),(-234027165833879509919/295147905179352825856:ℚ)⟩ node4368 node461
def node4370 : BoxExpr 3 := .add ⟨(-5316085103081206576021/4722366482869645213696:ℚ),(-4290242518218952194823/4722366482869645213696:ℚ)⟩ node4365 node4369
def node4371 : BoxExpr 3 := .mul ⟨(10511888414443168102079/2361183241434822606848:ℚ),(2781410480344871655355/590295810358705651712:ℚ)⟩ node4251 node514
def node4372 : BoxExpr 3 := .add ⟨(4186096177387172011187/1180591620717411303424:ℚ),(2313356148677112635517/590295810358705651712:ℚ)⟩ node4369 node4371
def node4373 : BoxExpr 3 := .add ⟨(11428299606467481468727/4722366482869645213696:ℚ),(14216606671197948889313/4722366482869645213696:ℚ)⟩ node4370 node4372
def node4374 : BoxExpr 3 := .mul ⟨(-8827585205831290249/4722366482869645213696:ℚ),(-8689927252347545421/4722366482869645213696:ℚ)⟩ node4316 node136
def node4375 : BoxExpr 3 := .mul ⟨(-1977095393557971709/2361183241434822606848:ℚ),(-1729810098589118287/4722366482869645213696:ℚ)⟩ node4255 node189
def node4376 : BoxExpr 3 := .add ⟨(-12781775992947233667/4722366482869645213696:ℚ),(-2604934337734165927/1180591620717411303424:ℚ)⟩ node4374 node4375
def node4377 : BoxExpr 3 := .add ⟨(-5402340299694630979/1180591620717411303424:ℚ),(-19109664603284209129/4722366482869645213696:ℚ)⟩ node4374 node4376
def node4378 : BoxExpr 3 := .add ⟨(11406690245268702944811/4722366482869645213696:ℚ),(1774687125824333085023/590295810358705651712:ℚ)⟩ node4373 node4377
def node4379 : BoxExpr 3 := .add ⟨(11255211761817637158167/2361183241434822606848:ℚ),(30790968045922111154727/4722366482869645213696:ℚ)⟩ node4378 node527
def node4380 : BoxExpr 3 := .mul ⟨(-8827585205831290249/2361183241434822606848:ℚ),(-17379854504695090843/4722366482869645213696:ℚ)⟩ node4254 node136
def node4381 : BoxExpr 3 := .add ⟨(13991001436857553560029/4722366482869645213696:ℚ),(14339400081008473739423/4722366482869645213696:ℚ)⟩ node534 node4380
def node4382 : BoxExpr 3 := .mul ⟨(-599379479534630194931/590295810358705651712:ℚ),(-1192981889329121711615/1180591620717411303424:ℚ)⟩ node6 node4355
def node4383 : BoxExpr 3 := .mul ⟨(685964586364244984177/2361183241434822606848:ℚ),(207909756963574848867/590295810358705651712:ℚ)⟩ node86 node4356
def node4384 : BoxExpr 3 := .mul ⟨(9160630048574071195561/2361183241434822606848:ℚ),(18499132826878886742597/4722366482869645213696:ℚ)⟩ node4354 node4354
def node4385 : BoxExpr 3 := .inv ⟨(1205502193385414597249/4722366482869645213696:ℚ),(1217205862494246285061/4722366482869645213696:ℚ)⟩ node4384
def node4386 : BoxExpr 3 := .mul ⟨(350219245561099908159/4722366482869645213696:ℚ),(26794719973960446593/295147905179352825856:ℚ)⟩ node4383 node4385
def node4387 : BoxExpr 3 := .neg ⟨(-26794719973960446593/295147905179352825856:ℚ),(-350219245561099908159/4722366482869645213696:ℚ)⟩ node4386
def node4388 : BoxExpr 3 := .mul ⟨(-1161802311370941239/36893488147419103232:ℚ),(-100688033098816223595/4722366482869645213696:ℚ)⟩ node4353 node4387
def node4389 : BoxExpr 3 := .add ⟨(-617968316516565254755/590295810358705651712:ℚ),(-4872615590415303070055/4722366482869645213696:ℚ)⟩ node4382 node4388
def node4390 : BoxExpr 3 := .mul ⟨(-12256939655697398011699/4722366482869645213696:ℚ),(-12062502075219914065829/4722366482869645213696:ℚ)⟩ node11 node4389
def node4391 : BoxExpr 3 := .add ⟨(-2227795112998372059337/2361183241434822606848:ℚ),(-4261152645519260172803/4722366482869645213696:ℚ)⟩ node4390 node546
def node4392 : BoxExpr 3 := .neg ⟨(4261152645519260172803/4722366482869645213696:ℚ),(2227795112998372059337/2361183241434822606848:ℚ)⟩ node4391
def cert_iv28 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-203/1280:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/1280:ℚ)],
    whole := node4275, centerValue := node4302, gradient := ![node4309, node4321, node4337],
    hessian := ![![node4343, node4351, node4359], ![node4360, node4379, node4381], ![node4359, node4381, node4392]] }
def node4393 : BoxExpr 3 := .var 2
def node4394 : BoxExpr 3 := .mul ⟨(-136285287409784757997/2361183241434822606848:ℚ),(-23465670790601693043/2361183241434822606848:ℚ)⟩ node13 node4393
def node4395 : BoxExpr 3 := .add ⟨(1044306333307626545427/2361183241434822606848:ℚ),(1157125949926809610381/2361183241434822606848:ℚ)⟩ node4394 node301
def node4396 : BoxExpr 3 := .mul ⟨(4381584896129628672565/4722366482869645213696:ℚ),(2444393338366155903311/2361183241434822606848:ℚ)⟩ node36 node4395
def node4397 : BoxExpr 3 := .mul ⟨(650492340828951875709/590295810358705651712:ℚ),(5828459433488529345743/4722366482869645213696:ℚ)⟩ node4396 node304
def node4398 : BoxExpr 3 := .add ⟨(129893324855778111127/2361183241434822606848:ℚ),(415006201259032940905/2361183241434822606848:ℚ)⟩ node4393 node306
def node4399 : BoxExpr 3 := .mul ⟨(-5936853641698116765/4722366482869645213696:ℚ),(-464545864834542593/1180591620717411303424:ℚ)⟩ node4398 node4254
def node4400 : BoxExpr 3 := .mul ⟨(-3241176582165427489/2361183241434822606848:ℚ),(-1012532719110263927/2361183241434822606848:ℚ)⟩ node4399 node37
def node4401 : BoxExpr 3 := .add ⟨(2598728186733642075347/2361183241434822606848:ℚ),(5826434368050308817889/4722366482869645213696:ℚ)⟩ node4397 node4400
def node4402 : BoxExpr 3 := .add ⟨(15911900628606670510501/4722366482869645213696:ℚ),(16668198364910099315131/4722366482869645213696:ℚ)⟩ node4401 node316
def node4403 : BoxExpr 3 := .add ⟨(11149954395644849158137/4722366482869645213696:ℚ),(5960187664155677242933/2361183241434822606848:ℚ)⟩ node4402 node323
def node4404 : BoxExpr 3 := .add ⟨(11149940228545400549201/4722366482869645213696:ℚ),(11920361161211905876931/4722366482869645213696:ℚ)⟩ node4403 node325
def node4405 : BoxExpr 3 := .mul ⟨(1475739525896764129/2361183241434822606848:ℚ),(97583276149923528049/4722366482869645213696:ℚ)⟩ node4393 node4393
def node4406 : BoxExpr 3 := .neg ⟨(-97583276149923528049/4722366482869645213696:ℚ),(-1475739525896764129/2361183241434822606848:ℚ)⟩ node4405
def node4407 : BoxExpr 3 := .add ⟨(4624783206719721685647/4722366482869645213696:ℚ),(2359707501908925842719/2361183241434822606848:ℚ)⟩ node12 node4406
def node4408 : BoxExpr 3 := .sqrt ⟨(4673320148026626629985/4722366482869645213696:ℚ),(2360445256343680887171/2361183241434822606848:ℚ)⟩ node4407
def node4409 : BoxExpr 3 := .mul ⟨(723070763249629799811/295147905179352825856:ℚ),(5852208417145874382513/2361183241434822606848:ℚ)⟩ node11 node4408
def node4410 : BoxExpr 3 := .neg ⟨(59029581035870565171/2361183241434822606848:ℚ),(678840181912511499469/4722366482869645213696:ℚ)⟩ node4393
def node4411 : BoxExpr 3 := .add ⟨(-1/4722366482869645213696:ℚ),(560781019840770369127/4722366482869645213696:ℚ)⟩ node332 node4410
def node4412 : BoxExpr 3 := .mul ⟨(-1/4722366482869645213696:ℚ),(400397648166310043557/4722366482869645213696:ℚ)⟩ node4411 node335
def node4413 : BoxExpr 3 := .neg ⟨(-400397648166310043557/4722366482869645213696:ℚ),(1/4722366482869645213696:ℚ)⟩ node4412
def node4414 : BoxExpr 3 := .add ⟨(11168734563827766753419/4722366482869645213696:ℚ),(11704416834291748765027/4722366482869645213696:ℚ)⟩ node4409 node4413
def node4415 : BoxExpr 3 := .mul ⟨(-1/4722366482869645213696:ℚ),(33296373053045740667/2361183241434822606848:ℚ)⟩ node4411 node4411
def node4416 : BoxExpr 3 := .mul ⟨(-1/4722366482869645213696:ℚ),(27502804141815781791/2361183241434822606848:ℚ)⟩ node4415 node340
def node4417 : BoxExpr 3 := .add ⟨(5584367281913883376709/2361183241434822606848:ℚ),(11759422442575380328609/4722366482869645213696:ℚ)⟩ node4414 node4416
def node4418 : BoxExpr 3 := .neg ⟨(-11759422442575380328609/4722366482869645213696:ℚ),(-5584367281913883376709/2361183241434822606848:ℚ)⟩ node4417
def node4419 : BoxExpr 3 := .add ⟨(-38092638376873736213/295147905179352825856:ℚ),(751626597384139123513/4722366482869645213696:ℚ)⟩ node4404 node4418
def node4420 : BoxExpr 3 := .var 2
def node4421 : BoxExpr 3 := .mul ⟨(-159190177180545680671/4722366482869645213696:ℚ),(-79595088590272840335/2361183241434822606848:ℚ)⟩ node51 node4420
def node4422 : BoxExpr 3 := .add ⟨(2201993064254276926177/4722366482869645213696:ℚ),(1100996532127138463089/2361183241434822606848:ℚ)⟩ node4421 node301
def node4423 : BoxExpr 3 := .mul ⟨(2317748774965534365401/2361183241434822606848:ℚ),(72429649217672948919/73786976294838206464:ℚ)⟩ node68 node4422
def node4424 : BoxExpr 3 := .mul ⟨(5515949998611571295927/4722366482869645213696:ℚ),(5515949998611571295947/4722366482869645213696:ℚ)⟩ node4423 node349
def node4425 : BoxExpr 3 := .add ⟨(544899526114811052031/4722366482869645213696:ℚ),(544899526114811052033/4722366482869645213696:ℚ)⟩ node4420 node351
def node4426 : BoxExpr 3 := .mul ⟨(-3897518550518143569/4722366482869645213696:ℚ),(-243594909407383973/295147905179352825856:ℚ)⟩ node4425 node4254
def node4427 : BoxExpr 3 := .mul ⟨(-1062894554399548793/1180591620717411303424:ℚ),(-2125789108799097585/2361183241434822606848:ℚ)⟩ node4426 node69
def node4428 : BoxExpr 3 := .add ⟨(5511698420393973100755/4722366482869645213696:ℚ),(5511698420393973100777/4722366482869645213696:ℚ)⟩ node4424 node4427
def node4429 : BoxExpr 3 := .add ⟨(16290700933310235052651/4722366482869645213696:ℚ),(8145350466655117526363/2361183241434822606848:ℚ)⟩ node4428 node358
def node4430 : BoxExpr 3 := .add ⟨(5767908149264975980917/2361183241434822606848:ℚ),(5767908149264975980957/2361183241434822606848:ℚ)⟩ node4429 node361
def node4431 : BoxExpr 3 := .add ⟨(5767901065715251676449/2361183241434822606848:ℚ),(11535802131430503352979/4722366482869645213696:ℚ)⟩ node4430 node325
def node4432 : BoxExpr 3 := .mul ⟨(8404797768583914455/1180591620717411303424:ℚ),(33619191074335657821/4722366482869645213696:ℚ)⟩ node4420 node4420
def node4433 : BoxExpr 3 := .neg ⟨(-33619191074335657821/4722366482869645213696:ℚ),(-8404797768583914455/1180591620717411303424:ℚ)⟩ node4432
def node4434 : BoxExpr 3 := .add ⟨(4688747291795309555875/4722366482869645213696:ℚ),(1172186822948827388969/1180591620717411303424:ℚ)⟩ node12 node4433
def node4435 : BoxExpr 3 := .sqrt ⟨(4705526862894312506765/4722366482869645213696:ℚ),(4705526862894312506767/4722366482869645213696:ℚ)⟩ node4434
def node4436 : BoxExpr 3 := .mul ⟨(11657489928092371250075/4722366482869645213696:ℚ),(11657489928092371250089/4722366482869645213696:ℚ)⟩ node50 node4435
def node4437 : BoxExpr 3 := .neg ⟨(398449671992126314905/4722366482869645213696:ℚ),(199224835996063157453/2361183241434822606848:ℚ)⟩ node4420
def node4438 : BoxExpr 3 := .add ⟨(140195254960192592281/2361183241434822606848:ℚ),(70097627480096296141/1180591620717411303424:ℚ)⟩ node332 node4437
def node4439 : BoxExpr 3 := .mul ⟨(200198824083155021777/4722366482869645213696:ℚ),(200198824083155021779/4722366482869645213696:ℚ)⟩ node4438 node335
def node4440 : BoxExpr 3 := .neg ⟨(-200198824083155021779/4722366482869645213696:ℚ),(-200198824083155021777/4722366482869645213696:ℚ)⟩ node4439
def node4441 : BoxExpr 3 := .add ⟨(1432161388001152028537/590295810358705651712:ℚ),(1432161388001152028539/590295810358705651712:ℚ)⟩ node4436 node4440
def node4442 : BoxExpr 3 := .mul ⟨(16648186526522870333/4722366482869645213696:ℚ),(8324093263261435167/2361183241434822606848:ℚ)⟩ node4438 node4438
def node4443 : BoxExpr 3 := .mul ⟨(13751402070907890895/4722366482869645213696:ℚ),(859462629431743181/295147905179352825856:ℚ)⟩ node4442 node340
def node4444 : BoxExpr 3 := .add ⟨(11471042506080124119191/4722366482869645213696:ℚ),(1433880313260015514901/590295810358705651712:ℚ)⟩ node4441 node4443
def node4445 : BoxExpr 3 := .neg ⟨(-1433880313260015514901/590295810358705651712:ℚ),(-11471042506080124119191/4722366482869645213696:ℚ)⟩ node4444
def node4446 : BoxExpr 3 := .add ⟨(32379812675189616845/2361183241434822606848:ℚ),(16189906337594808447/1180591620717411303424:ℚ)⟩ node4431 node4445
def node4447 : BoxExpr 3 := .mul ⟨(312157529854300624971/1180591620717411303424:ℚ),(624315059708601249945/2361183241434822606848:ℚ)⟩ node78 node4422
def node4448 : BoxExpr 3 := .mul ⟨(1485791165086065400129/4722366482869645213696:ℚ),(742895582543032700069/2361183241434822606848:ℚ)⟩ node4447 node349
def node4449 : BoxExpr 3 := .add ⟨(2682511251183718193861/2361183241434822606848:ℚ),(5365022502367436388151/4722366482869645213696:ℚ)⟩ node4448 node385
def node4450 : BoxExpr 3 := .add ⟨(188197277615917658685/295147905179352825856:ℚ),(3011156441854682539391/4722366482869645213696:ℚ)⟩ node4449 node387
def node4451 : BoxExpr 3 := .mul ⟨(2910637360060692656983/4722366482869645213696:ℚ),(90957417501896645531/147573952589676412928:ℚ)⟩ node77 node4435
def node4452 : BoxExpr 3 := .neg ⟨(-90957417501896645531/147573952589676412928:ℚ),(-2910637360060692656983/4722366482869645213696:ℚ)⟩ node4451
def node4453 : BoxExpr 3 := .add ⟨(6282442612124367623/295147905179352825856:ℚ),(12564885224248735301/590295810358705651712:ℚ)⟩ node4450 node4452
def node4454 : BoxExpr 3 := .mul ⟨(-2100136677785488823531/4722366482869645213696:ℚ),(-65629271180796525735/147573952589676412928:ℚ)⟩ node98 node4422
def node4455 : BoxExpr 3 := .mul ⟨(-838791233393755255675/4722366482869645213696:ℚ),(-419395616696877627835/2361183241434822606848:ℚ)⟩ node68 node4420
def node4456 : BoxExpr 3 := .add ⟨(-1469463955589622039603/2361183241434822606848:ℚ),(-1469463955589622039595/2361183241434822606848:ℚ)⟩ node4454 node4455
def node4457 : BoxExpr 3 := .mul ⟨(-874284757621634474791/1180591620717411303424:ℚ),(-3497139030486537899143/4722366482869645213696:ℚ)⟩ node4456 node349
def node4458 : BoxExpr 3 := .mul ⟨(2622328397435548463657/2361183241434822606848:ℚ),(5244656794871096927339/4722366482869645213696:ℚ)⟩ node4423 node399
def node4459 : BoxExpr 3 := .add ⟨(873758882192279514075/2361183241434822606848:ℚ),(436879441096139757049/1180591620717411303424:ℚ)⟩ node4457 node4458
def node4460 : BoxExpr 3 := .mul ⟨(-1010617780865716891/2361183241434822606848:ℚ),(-2021235561731433781/4722366482869645213696:ℚ)⟩ node4426 node103
def node4461 : BoxExpr 3 := .add ⟨(-20444366351768151499/4722366482869645213696:ℚ),(-2555545793971018937/590295810358705651712:ℚ)⟩ node4317 node4460
def node4462 : BoxExpr 3 := .add ⟨(1727073398032790876651/4722366482869645213696:ℚ),(431768349508197719175/1180591620717411303424:ℚ)⟩ node4459 node4461
def node4463 : BoxExpr 3 := .add ⟨(2048990632657459706925/4722366482869645213696:ℚ),(1024495316328729853545/2361183241434822606848:ℚ)⟩ node4462 node409
def node4464 : BoxExpr 3 := .add ⟨(-199224835996063157453/1180591620717411303424:ℚ),(-398449671992126314905/2361183241434822606848:ℚ)⟩ node4420 node4420
def node4465 : BoxExpr 3 := .neg ⟨(398449671992126314905/2361183241434822606848:ℚ),(199224835996063157453/1180591620717411303424:ℚ)⟩ node4464
def node4466 : BoxExpr 3 := .mul ⟨(4705526862894312506765/2361183241434822606848:ℚ),(4705526862894312506767/2361183241434822606848:ℚ)⟩ node86 node4435
def node4467 : BoxExpr 3 := .inv ⟨(1184816591654398994533/2361183241434822606848:ℚ),(592408295827199497267/1180591620717411303424:ℚ)⟩ node4466
def node4468 : BoxExpr 3 := .mul ⟨(199937799841679830327/2361183241434822606848:ℚ),(24992224980209978791/295147905179352825856:ℚ)⟩ node4465 node4467
def node4469 : BoxExpr 3 := .mul ⟨(990653312928151465023/4722366482869645213696:ℚ),(495326656464075732515/2361183241434822606848:ℚ)⟩ node50 node4468
def node4470 : BoxExpr 3 := .add ⟨(4362422981697078147601/4722366482869645213696:ℚ),(4362422981697078147609/4722366482869645213696:ℚ)⟩ node4469 node335
def node4471 : BoxExpr 3 := .mul ⟨(-70097627480096296141/1180591620717411303424:ℚ),(-140195254960192592281/2361183241434822606848:ℚ)⟩ node422 node4438
def node4472 : BoxExpr 3 := .mul ⟨(-70097627480096296141/1180591620717411303424:ℚ),(-140195254960192592281/2361183241434822606848:ℚ)⟩ node4438 node422
def node4473 : BoxExpr 3 := .add ⟨(-70097627480096296141/590295810358705651712:ℚ),(-140195254960192592281/1180591620717411303424:ℚ)⟩ node4471 node4472
def node4474 : BoxExpr 3 := .mul ⟨(-115801280597119081225/1180591620717411303424:ℚ),(-14475160074639885153/147573952589676412928:ℚ)⟩ node4473 node340
def node4475 : BoxExpr 3 := .add ⟨(3899217859308601822701/4722366482869645213696:ℚ),(3899217859308601822713/4722366482869645213696:ℚ)⟩ node4470 node4474
def node4476 : BoxExpr 3 := .neg ⟨(-3899217859308601822713/4722366482869645213696:ℚ),(-3899217859308601822701/4722366482869645213696:ℚ)⟩ node4475
def node4477 : BoxExpr 3 := .add ⟨(197519709480622890629/1180591620717411303424:ℚ),(790078837922491562547/4722366482869645213696:ℚ)⟩ node4323 node4476
def node4478 : BoxExpr 3 := .mul ⟨(9411236015013392936403/4722366482869645213696:ℚ),(10447809852385436017447/4722366482869645213696:ℚ)⟩ node112 node4395
def node4479 : BoxExpr 3 := .mul ⟨(2794393850913385140155/1180591620717411303424:ℚ),(12455981395803622416051/4722366482869645213696:ℚ)⟩ node4478 node304
def node4480 : BoxExpr 3 := .add ⟨(22503786322516324723343/4722366482869645213696:ℚ),(11695582752116110207583/1180591620717411303424:ℚ)⟩ node4479 node448
def node4481 : BoxExpr 3 := .mul ⟨(22992735128291003019525/4722366482869645213696:ℚ),(5806695330605454982441/1180591620717411303424:ℚ)⟩ node111 node4408
def node4482 : BoxExpr 3 := .neg ⟨(-5806695330605454982441/1180591620717411303424:ℚ),(-22992735128291003019525/4722366482869645213696:ℚ)⟩ node4481
def node4483 : BoxExpr 3 := .add ⟨(-722994999905495206421/4722366482869645213696:ℚ),(23789595880173437810807/4722366482869645213696:ℚ)⟩ node4480 node4482
def node4484 : BoxExpr 3 := .mul ⟨(-321284420978334115479/2361183241434822606848:ℚ),(-546339652480075740029/4722366482869645213696:ℚ)⟩ node131 node4395
def node4485 : BoxExpr 3 := .mul ⟨(-394492116751112723489/4722366482869645213696:ℚ),(-32642576117382053743/2361183241434822606848:ℚ)⟩ node118 node4393
def node4486 : BoxExpr 3 := .add ⟨(-1037060958707780954447/4722366482869645213696:ℚ),(-611624804714839847515/4722366482869645213696:ℚ)⟩ node4484 node4485
def node4487 : BoxExpr 3 := .mul ⟨(-618197124109654851351/2361183241434822606848:ℚ),(-363208528748987338459/2361183241434822606848:ℚ)⟩ node4486 node304
def node4488 : BoxExpr 3 := .mul ⟨(1154975128627240221081/4722366482869645213696:ℚ),(1344873440014190769669/4722366482869645213696:ℚ)⟩ node118 node4395
def node4489 : BoxExpr 3 := .mul ⟨(647646155493913956661/2361183241434822606848:ℚ),(767535068729457165115/2361183241434822606848:ℚ)⟩ node4488 node461
def node4490 : BoxExpr 3 := .add ⟨(14724515692129552655/1180591620717411303424:ℚ),(12635204374389682083/73786976294838206464:ℚ)⟩ node4487 node4489
def node4491 : BoxExpr 3 := .add ⟨(-2698402662125952631339/4722366482869645213696:ℚ),(277778370066574928277/590295810358705651712:ℚ)⟩ node4490 node476
def node4492 : BoxExpr 3 := .add ⟨(-678840181912511499469/2361183241434822606848:ℚ),(-59029581035870565171/1180591620717411303424:ℚ)⟩ node4393 node4393
def node4493 : BoxExpr 3 := .neg ⟨(59029581035870565171/1180591620717411303424:ℚ),(678840181912511499469/2361183241434822606848:ℚ)⟩ node4492
def node4494 : BoxExpr 3 := .mul ⟨(4673320148026626629985/2361183241434822606848:ℚ),(2360445256343680887171/1180591620717411303424:ℚ)⟩ node86 node4408
def node4495 : BoxExpr 3 := .inv ⟨(1180960728627232463875/2361183241434822606848:ℚ),(2330042752595940843/4611686018427387904:ℚ)⟩ node4494
def node4496 : BoxExpr 3 := .mul ⟨(118096072862723246387/4722366482869645213696:ℚ),(171491146591061246045/1180591620717411303424:ℚ)⟩ node4493 node4495
def node4497 : BoxExpr 3 := .mul ⟨(35653037045231508785/2361183241434822606848:ℚ),(217216573848840103321/2361183241434822606848:ℚ)⟩ node117 node4496
def node4498 : BoxExpr 3 := .neg ⟨(-217216573848840103321/2361183241434822606848:ℚ),(-35653037045231508785/2361183241434822606848:ℚ)⟩ node4497
def node4499 : BoxExpr 3 := .add ⟨(798497444408683769305/4722366482869645213696:ℚ),(310597268159699421039/1180591620717411303424:ℚ)⟩ node479 node4498
def node4500 : BoxExpr 3 := .add ⟨(-1349201331062976315669/2361183241434822606848:ℚ),(277778370066574928277/590295810358705651712:ℚ)⟩ node4490 node492
def node4501 : BoxExpr 3 := .mul ⟨(-2377698406354073342231/4722366482869645213696:ℚ),(-1048746737762269884223/2361183241434822606848:ℚ)⟩ node175 node4395
def node4502 : BoxExpr 3 := .mul ⟨(111226706722118881451/4722366482869645213696:ℚ),(655357418360029009115/4722366482869645213696:ℚ)⟩ node148 node4393
def node4503 : BoxExpr 3 := .add ⟨(-566617924907988615195/1180591620717411303424:ℚ),(-1442136057164510759331/4722366482869645213696:ℚ)⟩ node4501 node4502
def node4504 : BoxExpr 3 := .add ⟨(-2155244992909835579329/4722366482869645213696:ℚ),(-98347329850560218777/590295810358705651712:ℚ)⟩ node4503 node4502
def node4505 : BoxExpr 3 := .mul ⟨(-1284752111417611326305/2361183241434822606848:ℚ),(-934444481807894957413/4722366482869645213696:ℚ)⟩ node4504 node304
def node4506 : BoxExpr 3 := .mul ⟨(-558549048411488539321/1180591620717411303424:ℚ),(-491934519204341081561/1180591620717411303424:ℚ)⟩ node148 node4395
def node4507 : BoxExpr 3 := .mul ⟨(-89626825983548382589/295147905179352825856:ℚ),(-15479361301991682317/295147905179352825856:ℚ)⟩ node36 node4393
def node4508 : BoxExpr 3 := .add ⟨(-917056352345682069677/1180591620717411303424:ℚ),(-553851964412307810829/1180591620717411303424:ℚ)⟩ node4506 node4507
def node4509 : BoxExpr 3 := .mul ⟨(-4186998654201997072381/4722366482869645213696:ℚ),(-2484556327308766053383/4722366482869645213696:ℚ)⟩ node4508 node461
def node4510 : BoxExpr 3 := .add ⟨(-6756502877037219724991/4722366482869645213696:ℚ),(-854750202279165252699/1180591620717411303424:ℚ)⟩ node4505 node4509
def node4511 : BoxExpr 3 := .mul ⟨(21606098824006921468553/4722366482869645213696:ℚ),(24623146265922318989491/4722366482869645213696:ℚ)⟩ node4396 node514
def node4512 : BoxExpr 3 := .add ⟨(4354775042451231099043/1180591620717411303424:ℚ),(5534647484653388234027/1180591620717411303424:ℚ)⟩ node4509 node4511
def node4513 : BoxExpr 3 := .add ⟨(10662597292767704671181/4722366482869645213696:ℚ),(292493580148388936333/73786976294838206464:ℚ)⟩ node4510 node4512
def node4514 : BoxExpr 3 := .mul ⟨(-3047589923016877605/1180591620717411303424:ℚ),(-1878820675534264453/2361183241434822606848:ℚ)⟩ node4399 node189
def node4515 : BoxExpr 3 := .add ⟨(-21017944897898800669/4722366482869645213696:ℚ),(-12447568603416074327/4722366482869645213696:ℚ)⟩ node4374 node4514
def node4516 : BoxExpr 3 := .add ⟨(-14922765051865045459/2361183241434822606848:ℚ),(-5284373963940904937/1180591620717411303424:ℚ)⟩ node4374 node4515
def node4517 : BoxExpr 3 := .add ⟨(10632751762663974580263/4722366482869645213696:ℚ),(4674612908410282076391/1180591620717411303424:ℚ)⟩ node4513 node4516
def node4518 : BoxExpr 3 := .add ⟨(10868242520515272975893/2361183241434822606848:ℚ),(35291922672968574780107/4722366482869645213696:ℚ)⟩ node4517 node527
def node4519 : BoxExpr 3 := .mul ⟨(-2330042752595940843/2305843009213693952:ℚ),(-1180960728627232463875/1180591620717411303424:ℚ)⟩ node6 node4495
def node4520 : BoxExpr 3 := .mul ⟨(118096072862723246387/2361183241434822606848:ℚ),(171491146591061246045/590295810358705651712:ℚ)⟩ node86 node4496
def node4521 : BoxExpr 3 := .mul ⟨(18499132826878886742581/4722366482869645213696:ℚ),(18877660015271406741755/4722366482869645213696:ℚ)⟩ node4494 node4494
def node4522 : BoxExpr 3 := .inv ⟨(1153642531188840001/4611686018427387904:ℚ),(1205502193385414597251/4722366482869645213696:ℚ)⟩ node4521
def node4523 : BoxExpr 3 := .mul ⟨(29542482267097747689/2361183241434822606848:ℚ),(175109622780549954081/2361183241434822606848:ℚ)⟩ node4520 node4522
def node4524 : BoxExpr 3 := .neg ⟨(-175109622780549954081/2361183241434822606848:ℚ),(-29542482267097747689/2361183241434822606848:ℚ)⟩ node4523
def node4525 : BoxExpr 3 := .mul ⟨(-100688033098816223597/4722366482869645213696:ℚ),(-184640514169360923/295147905179352825856:ℚ)⟩ node4493 node4524
def node4526 : BoxExpr 3 := .add ⟨(-4872615590415303070061/4722366482869645213696:ℚ),(-1181699290683909907567/1180591620717411303424:ℚ)⟩ node4519 node4525
def node4527 : BoxExpr 3 := .mul ⟨(-12080586022958705897975/4722366482869645213696:ℚ),(-11701518317348440453819/4722366482869645213696:ℚ)⟩ node11 node4526
def node4528 : BoxExpr 3 := .add ⟨(-2139618296629026002475/2361183241434822606848:ℚ),(-3900168887647786560793/4722366482869645213696:ℚ)⟩ node4527 node546
def node4529 : BoxExpr 3 := .neg ⟨(3900168887647786560793/4722366482869645213696:ℚ),(2139618296629026002475/2361183241434822606848:ℚ)⟩ node4528
def cert_iv29 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-27/320:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/320:ℚ)],
    whole := node4419, centerValue := node4446, gradient := ![node4453, node4463, node4477],
    hessian := ![![node4483, node4491, node4499], ![node4500, node4518, node4381], ![node4499, node4381, node4529]] }
def node4530 : BoxExpr 3 := .var 2
def node4531 : BoxExpr 3 := .mul ⟨(-2962723639343146913/295147905179352825856:ℚ),(-18996075496462544669/2361183241434822606848:ℚ)⟩ node13 node4530
def node4532 : BoxExpr 3 := .add ⟨(144611228950333266015/295147905179352825856:ℚ),(1161595545220948758755/2361183241434822606848:ℚ)⟩ node4531 node301
def node4533 : BoxExpr 3 := .mul ⟨(2426975136970172677785/2361183241434822606848:ℚ),(2453835222339873292157/2361183241434822606848:ℚ)⟩ node36 node4532
def node4534 : BoxExpr 3 := .mul ⟨(5764959576616861603807/4722366482869645213696:ℚ),(5850972846879395761727/4722366482869645213696:ℚ)⟩ node4533 node304
def node4535 : BoxExpr 3 := .add ⟨(205141917388081647845/1180591620717411303424:ℚ),(213124894695565570699/1180591620717411303424:ℚ)⟩ node4530 node306
def node4536 : BoxExpr 3 := .mul ⟨(-3048849157847026347/2361183241434822606848:ℚ),(-5869298027911616617/4722366482869645213696:ℚ)⟩ node4535 node4254
def node4537 : BoxExpr 3 := .mul ⟨(-6657976827026553599/4722366482869645213696:ℚ),(-6396415016616849447/4722366482869645213696:ℚ)⟩ node4536 node37
def node4538 : BoxExpr 3 := .add ⟨(179946924993432345319/147573952589676412928:ℚ),(730572053982847364035/590295810358705651712:ℚ)⟩ node4534 node4537
def node4539 : BoxExpr 3 := .add ⟨(16472745854929221410015/4722366482869645213696:ℚ),(8343170214361284704761/2361183241434822606848:ℚ)⟩ node4538 node316
def node4540 : BoxExpr 3 := .add ⟨(11710799621967400057651/4722366482869645213696:ℚ),(11938517392123824580257/4722366482869645213696:ℚ)⟩ node4539 node323
def node4541 : BoxExpr 3 := .add ⟨(11710785454867951448715/4722366482869645213696:ℚ),(5969251612512187985661/2361183241434822606848:ℚ)⟩ node4540 node325
def node4542 : BoxExpr 3 := .mul ⟨(967100340934050235/2361183241434822606848:ℚ),(2951479051793528259/4722366482869645213696:ℚ)⟩ node4530 node4530
def node4543 : BoxExpr 3 := .neg ⟨(-2951479051793528259/4722366482869645213696:ℚ),(-967100340934050235/2361183241434822606848:ℚ)⟩ node4542
def node4544 : BoxExpr 3 := .add ⟨(4719415003817851685437/4722366482869645213696:ℚ),(2360216141093888556613/2361183241434822606848:ℚ)⟩ node12 node4543
def node4545 : BoxExpr 3 := .sqrt ⟨(4720890512687361774341/4722366482869645213696:ℚ),(4721399283481479244671/4722366482869645213696:ℚ)⟩ node4544
def node4546 : BoxExpr 3 := .mul ⟨(5843447995178673808745/2361183241434822606848:ℚ),(5852839110172058832243/2361183241434822606848:ℚ)⟩ node11 node4545
def node4547 : BoxExpr 3 := .neg ⟨(-5852839110172058832243/2361183241434822606848:ℚ),(-5843447995178673808745/2361183241434822606848:ℚ)⟩ node4546
def node4548 : BoxExpr 3 := .add ⟨(5107234523833784229/4722366482869645213696:ℚ),(31450904333378544229/590295810358705651712:ℚ)⟩ node4541 node4547
def node4549 : BoxExpr 3 := .var 2
def node4550 : BoxExpr 3 := .mul ⟨(-42675377434943523573/4722366482869645213696:ℚ),(-10668844358735880893/1180591620717411303424:ℚ)⟩ node51 node4549
def node4551 : BoxExpr 3 := .add ⟨(2318507863999879083275/4722366482869645213696:ℚ),(579626965999969770819/1180591620717411303424:ℚ)⟩ node4550 node301
def node4552 : BoxExpr 3 := .mul ⟨(2440388595571499488517/2361183241434822606848:ℚ),(610097148892874872131/590295810358705651712:ℚ)⟩ node68 node4551
def node4553 : BoxExpr 3 := .mul ⟨(5807817316419238378391/4722366482869645213696:ℚ),(2903908658209619189205/2361183241434822606848:ℚ)⟩ node4552 node349
def node4554 : BoxExpr 3 := .add ⟨(836533624167294437087/4722366482869645213696:ℚ),(836533624167294437089/4722366482869645213696:ℚ)⟩ node4549 node351
def node4555 : BoxExpr 3 := .mul ⟨(-186984317868838583/147573952589676412928:ℚ),(-5983498171802834655/4722366482869645213696:ℚ)⟩ node4554 node4254
def node4556 : BoxExpr 3 := .mul ⟨(-3263526544202541971/2361183241434822606848:ℚ),(-1631763272101270985/1180591620717411303424:ℚ)⟩ node4555 node69
def node4557 : BoxExpr 3 := .add ⟨(5801290263330833294449/4722366482869645213696:ℚ),(2900645131665416647235/2361183241434822606848:ℚ)⟩ node4553 node4556
def node4558 : BoxExpr 3 := .add ⟨(16580292776247095246345/4722366482869645213696:ℚ),(16580292776247095246419/4722366482869645213696:ℚ)⟩ node4557 node358
def node4559 : BoxExpr 3 := .add ⟨(1478176017683351519441/590295810358705651712:ℚ),(11825408141466812155607/4722366482869645213696:ℚ)⟩ node4558 node361
def node4560 : BoxExpr 3 := .add ⟨(369543561698980110831/147573952589676412928:ℚ),(739087123397960221667/295147905179352825856:ℚ)⟩ node4559 node325
def node4561 : BoxExpr 3 := .mul ⟨(2416069756009716299/4722366482869645213696:ℚ),(604017439002429075/1180591620717411303424:ℚ)⟩ node4549 node4549
def node4562 : BoxExpr 3 := .neg ⟨(-604017439002429075/1180591620717411303424:ℚ),(-2416069756009716299/4722366482869645213696:ℚ)⟩ node4561
def node4563 : BoxExpr 3 := .add ⟨(1179987603278408874349/1180591620717411303424:ℚ),(4719950413113635497397/4722366482869645213696:ℚ)⟩ node12 node4562
def node4564 : BoxExpr 3 := .sqrt ⟨(590144786679699155775/590295810358705651712:ℚ),(2360579146718796623101/2361183241434822606848:ℚ)⟩ node4563
def node4565 : BoxExpr 3 := .mul ⟨(2924053823211308204795/1180591620717411303424:ℚ),(5848107646422616409597/2361183241434822606848:ℚ)⟩ node50 node4564
def node4566 : BoxExpr 3 := .neg ⟨(-5848107646422616409597/2361183241434822606848:ℚ),(-2924053823211308204795/1180591620717411303424:ℚ)⟩ node4565
def node4567 : BoxExpr 3 := .add ⟨(64589340761065363699/2361183241434822606848:ℚ),(32294670380532681873/1180591620717411303424:ℚ)⟩ node4560 node4566
def node4568 : BoxExpr 3 := .mul ⟨(657349652478649772551/2361183241434822606848:ℚ),(328674826239324886277/1180591620717411303424:ℚ)⟩ node78 node4551
def node4569 : BoxExpr 3 := .mul ⟨(391102333203783426357/1180591620717411303424:ℚ),(391102333203783426359/1180591620717411303424:ℚ)⟩ node4568 node349
def node4570 : BoxExpr 3 := .add ⟨(5443640670096504693021/4722366482869645213696:ℚ),(5443640670096504693449/4722366482869645213696:ℚ)⟩ node4569 node385
def node4571 : BoxExpr 3 := .add ⟨(3089774609583750844259/4722366482869645213696:ℚ),(3089774609583750844689/4722366482869645213696:ℚ)⟩ node4570 node387
def node4572 : BoxExpr 3 := .mul ⟨(730076573358863068049/1180591620717411303424:ℚ),(2920306293435452272205/4722366482869645213696:ℚ)⟩ node77 node4564
def node4573 : BoxExpr 3 := .neg ⟨(-2920306293435452272205/4722366482869645213696:ℚ),(-730076573358863068049/1180591620717411303424:ℚ)⟩ node4572
def node4574 : BoxExpr 3 := .add ⟨(84734158074149286027/2361183241434822606848:ℚ),(169468316148298572493/4722366482869645213696:ℚ)⟩ node4571 node4573
def node4575 : BoxExpr 3 := .mul ⟨(-2211261916290015669979/4722366482869645213696:ℚ),(-2211261916290015669967/4722366482869645213696:ℚ)⟩ node98 node4551
def node4576 : BoxExpr 3 := .mul ⟨(-112430719998516453169/2361183241434822606848:ℚ),(-224861439997032906335/4722366482869645213696:ℚ)⟩ node68 node4549
def node4577 : BoxExpr 3 := .add ⟨(-2436123356287048576317/4722366482869645213696:ℚ),(-1218061678143524288151/2361183241434822606848:ℚ)⟩ node4575 node4576
def node4578 : BoxExpr 3 := .mul ⟨(-22647135095443028309/36893488147419103232:ℚ),(-724708323054176905883/1180591620717411303424:ℚ)⟩ node4577 node349
def node4579 : BoxExpr 3 := .mul ⟨(2761084542063952374243/2361183241434822606848:ℚ),(172567783878997023391/147573952589676412928:ℚ)⟩ node4552 node399
def node4580 : BoxExpr 3 := .add ⟨(1311667895955598562467/2361183241434822606848:ℚ),(655833947977799281245/1180591620717411303424:ℚ)⟩ node4578 node4579
def node4581 : BoxExpr 3 := .mul ⟨(-3103015195859709819/4722366482869645213696:ℚ),(-3103015195859709817/4722366482869645213696:ℚ)⟩ node4555 node103
def node4582 : BoxExpr 3 := .add ⟨(-1345384124118526721/295147905179352825856:ℚ),(-5381536496474106883/1180591620717411303424:ℚ)⟩ node4317 node4581
def node4583 : BoxExpr 3 := .add ⟨(1300904822962650348699/2361183241434822606848:ℚ),(325226205740662587181/590295810358705651712:ℚ)⟩ node4580 node4582
def node4584 : BoxExpr 3 := .add ⟨(365465860068746190959/590295810358705651712:ℚ),(1461863440274984763919/2361183241434822606848:ℚ)⟩ node4583 node409
def node4585 : BoxExpr 3 := .add ⟨(-53407786969821464925/1180591620717411303424:ℚ),(-106815573939642929849/2361183241434822606848:ℚ)⟩ node4549 node4549
def node4586 : BoxExpr 3 := .neg ⟨(106815573939642929849/2361183241434822606848:ℚ),(53407786969821464925/1180591620717411303424:ℚ)⟩ node4585
def node4587 : BoxExpr 3 := .mul ⟨(590144786679699155775/295147905179352825856:ℚ),(2360579146718796623101/1180591620717411303424:ℚ)⟩ node86 node4564
def node4588 : BoxExpr 3 := .inv ⟨(2361787490744447554547/4722366482869645213696:ℚ),(2361787490744447554549/4722366482869645213696:ℚ)⟩ node4587
def node4589 : BoxExpr 3 := .mul ⟨(106842909063693277055/4722366482869645213696:ℚ),(53421454531846638529/2361183241434822606848:ℚ)⟩ node4586 node4588
def node4590 : BoxExpr 3 := .mul ⟨(132346512153581583223/2361183241434822606848:ℚ),(264693024307163166455/4722366482869645213696:ℚ)⟩ node50 node4589
def node4591 : BoxExpr 3 := .neg ⟨(-264693024307163166455/4722366482869645213696:ℚ),(-132346512153581583223/2361183241434822606848:ℚ)⟩ node4590
def node4592 : BoxExpr 3 := .add ⟨(2212301836461965109387/2361183241434822606848:ℚ),(2212301836461965109401/2361183241434822606848:ℚ)⟩ node4323 node4591
def node4593 : BoxExpr 3 := .mul ⟨(5212916412226012926007/2361183241434822606848:ℚ),(10488166290466559579387/4722366482869645213696:ℚ)⟩ node112 node4532
def node4594 : BoxExpr 3 := .mul ⟨(773912244067184080885/295147905179352825856:ℚ),(6252047368584069300093/2361183241434822606848:ℚ)⟩ node4593 node304
def node4595 : BoxExpr 3 := .add ⟨(23708806823937729456883/4722366482869645213696:ℚ),(46830444349828957014467/4722366482869645213696:ℚ)⟩ node4594 node448
def node4596 : BoxExpr 3 := .mul ⟨(23226781322421819929757/4722366482869645213696:ℚ),(11614642237364438941891/2361183241434822606848:ℚ)⟩ node111 node4545
def node4597 : BoxExpr 3 := .neg ⟨(-11614642237364438941891/2361183241434822606848:ℚ),(-23226781322421819929757/4722366482869645213696:ℚ)⟩ node4596
def node4598 : BoxExpr 3 := .add ⟨(479522349208851573101/4722366482869645213696:ℚ),(11801831513703568542355/2361183241434822606848:ℚ)⟩ node4595 node4597
def node4599 : BoxExpr 3 := .mul ⟨(-645050873123933667633/4722366482869645213696:ℚ),(-605238873304186323455/4722366482869645213696:ℚ)⟩ node131 node4532
def node4600 : BoxExpr 3 := .mul ⟨(-68607324652367430173/4722366482869645213696:ℚ),(-52850041736131843955/4722366482869645213696:ℚ)⟩ node118 node4530
def node4601 : BoxExpr 3 := .add ⟨(-356829098888150548903/2361183241434822606848:ℚ),(-329044457520159083705/2361183241434822606848:ℚ)⟩ node4599 node4600
def node4602 : BoxExpr 3 := .mul ⟨(-425415152077770027517/2361183241434822606848:ℚ),(-781601742686849083061/4722366482869645213696:ℚ)⟩ node4601 node304
def node4603 : BoxExpr 3 := .mul ⟨(1279489494074753118667/4722366482869645213696:ℚ),(1350068241841148643079/4722366482869645213696:ℚ)⟩ node118 node4532
def node4604 : BoxExpr 3 := .mul ⟨(1434933846267800750283/4722366482869645213696:ℚ),(48156237696800927051/147573952589676412928:ℚ)⟩ node4603 node461
def node4605 : BoxExpr 3 := .add ⟨(584103542112260695249/4722366482869645213696:ℚ),(759397863610780582571/4722366482869645213696:ℚ)⟩ node4602 node4604
def node4606 : BoxExpr 3 := .add ⟨(-1086598591391105073355/2361183241434822606848:ℚ),(2172971744182440355475/4722366482869645213696:ℚ)⟩ node4605 node476
def node4607 : BoxExpr 3 := .add ⟨(-118059162071741130343/2361183241434822606848:ℚ),(-23892996451886182339/590295810358705651712:ℚ)⟩ node4530 node4530
def node4608 : BoxExpr 3 := .neg ⟨(23892996451886182339/590295810358705651712:ℚ),(118059162071741130343/2361183241434822606848:ℚ)⟩ node4607
def node4609 : BoxExpr 3 := .mul ⟨(4720890512687361774341/2361183241434822606848:ℚ),(4721399283481479244671/2361183241434822606848:ℚ)⟩ node86 node4545
def node4610 : BoxExpr 3 := .inv ⟨(590416735049106942701/1180591620717411303424:ℚ),(2361921457254464927751/4722366482869645213696:ℚ)⟩ node4609
def node4611 : BoxExpr 3 := .mul ⟨(95591564148762823147/4722366482869645213696:ℚ),(118096072862723246389/4722366482869645213696:ℚ)⟩ node4608 node4610
def node4612 : BoxExpr 3 := .mul ⟨(28858957755260237525/2361183241434822606848:ℚ),(74792270161370607805/4722366482869645213696:ℚ)⟩ node117 node4611
def node4613 : BoxExpr 3 := .neg ⟨(-74792270161370607805/4722366482869645213696:ℚ),(-28858957755260237525/2361183241434822606848:ℚ)⟩ node4612
def node4614 : BoxExpr 3 := .add ⟨(579069160972496684071/2361183241434822606848:ℚ),(313994307804685056669/1180591620717411303424:ℚ)⟩ node479 node4613
def node4615 : BoxExpr 3 := .add ⟨(-2173197182782210146709/4722366482869645213696:ℚ),(2172971744182440355475/4722366482869645213696:ℚ)⟩ node4605 node492
def node4616 : BoxExpr 3 := .mul ⟨(-2386882669837745554921/4722366482869645213696:ℚ),(-72613058912082324609/147573952589676412928:ℚ)⟩ node175 node4532
def node4617 : BoxExpr 3 := .mul ⟨(45020467068056299143/2361183241434822606848:ℚ),(113975203193048523325/4722366482869645213696:ℚ)⟩ node148 node4530
def node4618 : BoxExpr 3 := .add ⟨(-2296841735701632956635/4722366482869645213696:ℚ),(-2209642681993585864163/4722366482869645213696:ℚ)⟩ node4616 node4617
def node4619 : BoxExpr 3 := .add ⟨(-2206800801565520358349/4722366482869645213696:ℚ),(-1047833739400268670419/2361183241434822606848:ℚ)⟩ node4618 node4617
def node4620 : BoxExpr 3 := .mul ⟨(-2630969563661099124141/4722366482869645213696:ℚ),(-2488990949531954642581/4722366482869645213696:ℚ)⟩ node4619 node304
def node4621 : BoxExpr 3 := .mul ⟨(-1121413077743565362243/2361183241434822606848:ℚ),(-1089936975253796353403/2361183241434822606848:ℚ)⟩ node148 node4532
def node4622 : BoxExpr 3 := .mul ⟨(-124698192672762967081/2361183241434822606848:ℚ),(-50123794636618604651/1180591620717411303424:ℚ)⟩ node36 node4530
def node4623 : BoxExpr 3 := .add ⟨(-311527817604082082331/590295810358705651712:ℚ),(-1190184564527033562705/2361183241434822606848:ℚ)⟩ node4621 node4622
def node4624 : BoxExpr 3 := .mul ⟨(-2844681354026757173001/4722366482869645213696:ℚ),(-667389659256383407111/1180591620717411303424:ℚ)⟩ node4623 node461
def node4625 : BoxExpr 3 := .add ⟨(-2737825458843928148571/2361183241434822606848:ℚ),(-5158549586557488271025/4722366482869645213696:ℚ)⟩ node4620 node4624
def node4626 : BoxExpr 3 := .mul ⟨(23935386804489262526095/4722366482869645213696:ℚ),(12359128672910819925959/2361183241434822606848:ℚ)⟩ node4533 node514
def node4627 : BoxExpr 3 := .add ⟨(10545352725231252676547/2361183241434822606848:ℚ),(11024349354398053111737/2361183241434822606848:ℚ)⟩ node4624 node4626
def node4628 : BoxExpr 3 := .add ⟨(975940908298415565997/295147905179352825856:ℚ),(16890149122238617952449/4722366482869645213696:ℚ)⟩ node4625 node4627
def node4629 : BoxExpr 3 := .mul ⟨(-6260313985167001765/2361183241434822606848:ℚ),(-741810397561635711/295147905179352825856:ℚ)⟩ node4536 node189
def node4630 : BoxExpr 3 := .add ⟨(-21348213176165293779/4722366482869645213696:ℚ),(-20558893613333716797/4722366482869645213696:ℚ)⟩ node4374 node4629
def node4631 : BoxExpr 3 := .add ⟨(-7543949595499146007/1180591620717411303424:ℚ),(-14624410432840631109/2361183241434822606848:ℚ)⟩ node4374 node4630
def node4632 : BoxExpr 3 := .add ⟨(3896219683598163117981/1180591620717411303424:ℚ),(16860900301372936690231/4722366482869645213696:ℚ)⟩ node4628 node4631
def node4633 : BoxExpr 3 := .add ⟨(26688612012759223843447/4722366482869645213696:ℚ),(16727185670350191582387/2361183241434822606848:ℚ)⟩ node4632 node527
def node4634 : BoxExpr 3 := .mul ⟨(-2361921457254464927751/2361183241434822606848:ℚ),(-590416735049106942701/590295810358705651712:ℚ)⟩ node6 node4610
def node4635 : BoxExpr 3 := .mul ⟨(95591564148762823147/2361183241434822606848:ℚ),(118096072862723246389/2361183241434822606848:ℚ)⟩ node86 node4611
def node4636 : BoxExpr 3 := .mul ⟨(9438830007635703370873/2361183241434822606848:ℚ),(4720432282187777113227/1180591620717411303424:ℚ)⟩ node4609 node4609
def node4637 : BoxExpr 3 := .inv ⟨(1181075369022924765703/4722366482869645213696:ℚ),(1181329951937372161025/4722366482869645213696:ℚ)⟩ node4636
def node4638 : BoxExpr 3 := .mul ⟨(2988460402004634013/295147905179352825856:ℚ),(14771241133548873845/1180591620717411303424:ℚ)⟩ node4635 node4637
def node4639 : BoxExpr 3 := .neg ⟨(-14771241133548873845/1180591620717411303424:ℚ),(-2988460402004634013/295147905179352825856:ℚ)⟩ node4638
def node4640 : BoxExpr 3 := .mul ⟨(-1477124113354887385/2361183241434822606848:ℚ),(-1935389613917384913/4722366482869645213696:ℚ)⟩ node4608 node4639
def node4641 : BoxExpr 3 := .add ⟨(-73856205667744369223/73786976294838206464:ℚ),(-4725269270006772926521/4722366482869645213696:ℚ)⟩ node4634 node4640
def node4642 : BoxExpr 3 := .mul ⟨(-11719061082887122164953/4722366482869645213696:ℚ),(-2924433977900331412699/1180591620717411303424:ℚ)⟩ node11 node4641
def node4643 : BoxExpr 3 := .neg ⟨(2924433977900331412699/1180591620717411303424:ℚ),(11719061082887122164953/4722366482869645213696:ℚ)⟩ node4642
def cert_iv30 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-6956533366137/307551593775760:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (732256478257/307551593775760:ℚ)],
    whole := node4548, centerValue := node4567, gradient := ![node4574, node4584, node4592],
    hessian := ![![node4598, node4606, node4614], ![node4615, node4633, node4381], ![node4614, node4381, node4643]] }
def node4644 : BoxExpr 3 := .var 2
def node4645 : BoxExpr 3 := .mul ⟨(-38374438936155268257/4722366482869645213696:ℚ),(0/1:ℚ)⟩ node13 node4644
def node4646 : BoxExpr 3 := .add ⟨(2322808802498667338591/4722366482869645213696:ℚ),(1/2:ℚ)⟩ node4645 node301
def node4647 : BoxExpr 3 := .mul ⟨(1218223001361786319939/1180591620717411303424:ℚ),(2493963853455259341605/2361183241434822606848:ℚ)⟩ node36 node4646
def node4648 : BoxExpr 3 := .mul ⟨(5787456370008852087379/4722366482869645213696:ℚ),(5946656342209891572701/4722366482869645213696:ℚ)⟩ node4647 node304
def node4649 : BoxExpr 3 := .add ⟨(421527422908261496183/2361183241434822606848:ℚ),(118508945573725876519/590295810358705651712:ℚ)⟩ node4644 node306
def node4650 : BoxExpr 3 := .mul ⟨(-6781298814029368607/4722366482869645213696:ℚ),(-6030142701907552545/4722366482869645213696:ℚ)⟩ node4649 node4254
def node4651 : BoxExpr 3 := .mul ⟨(-925548625551573193/590295810358705651712:ℚ),(-6571705022882985327/4722366482869645213696:ℚ)⟩ node4650 node37
def node4652 : BoxExpr 3 := .add ⟨(5780051981004439501835/4722366482869645213696:ℚ),(2970042318593504293687/2361183241434822606848:ℚ)⟩ node4648 node4651
def node4653 : BoxExpr 3 := .add ⟨(8247248118071912930821/2361183241434822606848:ℚ),(2097731079255849885577/590295810358705651712:ℚ)⟩ node4652 node316
def node4654 : BoxExpr 3 := .add ⟨(5866275001591002254639/2361183241434822606848:ℚ),(12034025597448054255351/4722366482869645213696:ℚ)⟩ node4653 node323
def node4655 : BoxExpr 3 := .add ⟨(5866267918041277950171/2361183241434822606848:ℚ),(752125714396787852901/295147905179352825856:ℚ)⟩ node4654 node325
def node4656 : BoxExpr 3 := .mul ⟨(0/1:ℚ),(1934200681868100471/4722366482869645213696:ℚ)⟩ node4644 node4644
def node4657 : BoxExpr 3 := .neg ⟨(-1934200681868100471/4722366482869645213696:ℚ),(0/1:ℚ)⟩ node4656
def node4658 : BoxExpr 3 := .add ⟨(4720432282187777113225/4722366482869645213696:ℚ),(1/1:ℚ)⟩ node12 node4657
def node4659 : BoxExpr 3 := .sqrt ⟨(2360699641740739622335/2361183241434822606848:ℚ),(1/1:ℚ)⟩ node4658
def node4660 : BoxExpr 3 := .mul ⟨(5844077744093396855487/2361183241434822606848:ℚ),(5854038089980057203133/2361183241434822606848:ℚ)⟩ node11 node4659
def node4661 : BoxExpr 3 := .neg ⟨(-5854038089980057203133/2361183241434822606848:ℚ),(-5844077744093396855487/2361183241434822606848:ℚ)⟩ node4660
def node4662 : BoxExpr 3 := .add ⟨(6114914030610373519/1180591620717411303424:ℚ),(172927971080905967721/2361183241434822606848:ℚ)⟩ node4655 node4661
def node4663 : BoxExpr 3 := .var 2
def node4664 : BoxExpr 3 := .mul ⟨(-2386455935283761175/590295810358705651712:ℚ),(-9545823741135044699/2361183241434822606848:ℚ)⟩ node51 node4663
def node4665 : BoxExpr 3 := .add ⟨(292761449244069064681/590295810358705651712:ℚ),(1171045796976276258725/2361183241434822606848:ℚ)⟩ node4664 node301
def node4666 : BoxExpr 3 := .mul ⟨(4930424178769127839451/4722366482869645213696:ℚ),(1232606044692281959867/1180591620717411303424:ℚ)⟩ node68 node4665
def node4667 : BoxExpr 3 := .mul ⟨(5866894103404377963647/4722366482869645213696:ℚ),(5866894103404377963671/4722366482869645213696:ℚ)⟩ node4666 node349
def node4668 : BoxExpr 3 := .add ⟨(447781602601582501129/2361183241434822606848:ℚ),(223890801300791250565/1180591620717411303424:ℚ)⟩ node4663 node351
def node4669 : BoxExpr 3 := .mul ⟨(-6405720757968460577/4722366482869645213696:ℚ),(-6405720757968460575/4722366482869645213696:ℚ)⟩ node4668 node4254
def node4670 : BoxExpr 3 := .mul ⟨(-3493815679078000943/2361183241434822606848:ℚ),(-3493815679078000941/2361183241434822606848:ℚ)⟩ node4669 node69
def node4671 : BoxExpr 3 := .add ⟨(5859906472046221961761/4722366482869645213696:ℚ),(5859906472046221961789/4722366482869645213696:ℚ)⟩ node4667 node4670
def node4672 : BoxExpr 3 := .add ⟨(16638908984962483913657/4722366482869645213696:ℚ),(8319454492481241956869/2361183241434822606848:ℚ)⟩ node4671 node358
def node4673 : BoxExpr 3 := .add ⟨(1485503043772775102855/590295810358705651712:ℚ),(5942012175091100411463/2361183241434822606848:ℚ)⟩ node4672 node361
def node4674 : BoxExpr 3 := .add ⟨(742750636442672013369/295147905179352825856:ℚ),(11884010183082752213991/4722366482869645213696:ℚ)⟩ node4673 node325
def node4675 : BoxExpr 3 := .mul ⟨(483550170467025117/4722366482869645213696:ℚ),(241775085233512559/2361183241434822606848:ℚ)⟩ node4663 node4663
def node4676 : BoxExpr 3 := .neg ⟨(-241775085233512559/2361183241434822606848:ℚ),(-483550170467025117/4722366482869645213696:ℚ)⟩ node4675
def node4677 : BoxExpr 3 := .add ⟨(2360941466349589094289/2361183241434822606848:ℚ),(4721882932699178188579/4722366482869645213696:ℚ)⟩ node12 node4676
def node4678 : BoxExpr 3 := .sqrt ⟨(4722124701594910629551/4722366482869645213696:ℚ),(4722124701594910629553/4722366482869645213696:ℚ)⟩ node4677
def node4679 : BoxExpr 3 := .mul ⟨(11698609476044821268637/4722366482869645213696:ℚ),(11698609476044821268651/4722366482869645213696:ℚ)⟩ node50 node4678
def node4680 : BoxExpr 3 := .neg ⟨(-11698609476044821268651/4722366482869645213696:ℚ),(-11698609476044821268637/4722366482869645213696:ℚ)⟩ node4679
def node4681 : BoxExpr 3 := .add ⟨(185400707037930945253/4722366482869645213696:ℚ),(92700353518965472677/2361183241434822606848:ℚ)⟩ node4674 node4680
def node4682 : BoxExpr 3 := .mul ⟨(1328072351414683494621/4722366482869645213696:ℚ),(1328072351414683494627/4722366482869645213696:ℚ)⟩ node78 node4665
def node4683 : BoxExpr 3 := .mul ⟨(395080603863700849017/1180591620717411303424:ℚ),(395080603863700849019/1180591620717411303424:ℚ)⟩ node4682 node349
def node4684 : BoxExpr 3 := .add ⟨(5459553752736174383661/4722366482869645213696:ℚ),(5459553752736174384089/4722366482869645213696:ℚ)⟩ node4683 node385
def node4685 : BoxExpr 3 := .add ⟨(3105687692223420534899/4722366482869645213696:ℚ),(3105687692223420535329/4722366482869645213696:ℚ)⟩ node4684 node387
def node4686 : BoxExpr 3 := .mul ⟨(2920904072126279940513/4722366482869645213696:ℚ),(1460452036063139970261/2361183241434822606848:ℚ)⟩ node77 node4678
def node4687 : BoxExpr 3 := .neg ⟨(-1460452036063139970261/2361183241434822606848:ℚ),(-2920904072126279940513/4722366482869645213696:ℚ)⟩ node4686
def node4688 : BoxExpr 3 := .add ⟨(184783620097140594377/4722366482869645213696:ℚ),(1443622032008910897/36893488147419103232:ℚ)⟩ node4685 node4687
def node4689 : BoxExpr 3 := .mul ⟨(-1116877373285141605607/2361183241434822606848:ℚ),(-2233754746570283211201/4722366482869645213696:ℚ)⟩ node98 node4665
def node4690 : BoxExpr 3 := .mul ⟨(-100596072086846942535/4722366482869645213696:ℚ),(-25149018021711735633/1180591620717411303424:ℚ)⟩ node68 node4663
def node4691 : BoxExpr 3 := .add ⟨(-2334350818657130153749/4722366482869645213696:ℚ),(-2334350818657130153733/4722366482869645213696:ℚ)⟩ node4689 node4690
def node4692 : BoxExpr 3 := .mul ⟨(-1388865192596444136889/2361183241434822606848:ℚ),(-2777730385192888273757/4722366482869645213696:ℚ)⟩ node4691 node349
def node4693 : BoxExpr 3 := .mul ⟨(5578340273561955891485/4722366482869645213696:ℚ),(2789170136780977945757/2361183241434822606848:ℚ)⟩ node4666 node399
def node4694 : BoxExpr 3 := .add ⟨(2800609888369067617707/4722366482869645213696:ℚ),(2800609888369067617757/4722366482869645213696:ℚ)⟩ node4692 node4693
def node4695 : BoxExpr 3 := .mul ⟨(-3321977926905781037/4722366482869645213696:ℚ),(-3321977926905781035/4722366482869645213696:ℚ)⟩ node4669 node103
def node4696 : BoxExpr 3 := .add ⟨(-10872554358471249377/2361183241434822606848:ℚ),(-10872554358471249375/2361183241434822606848:ℚ)⟩ node4317 node4695
def node4697 : BoxExpr 3 := .add ⟨(2778864779652125118953/4722366482869645213696:ℚ),(2778864779652125119007/4722366482869645213696:ℚ)⟩ node4694 node4696
def node4698 : BoxExpr 3 := .add ⟨(3100782014276793949227/4722366482869645213696:ℚ),(3100782014276793949397/4722366482869645213696:ℚ)⟩ node4697 node409
def node4699 : BoxExpr 3 := .add ⟨(-47785992903772364679/2361183241434822606848:ℚ),(-23892996451886182339/1180591620717411303424:ℚ)⟩ node4663 node4663
def node4700 : BoxExpr 3 := .neg ⟨(23892996451886182339/1180591620717411303424:ℚ),(47785992903772364679/2361183241434822606848:ℚ)⟩ node4699
def node4701 : BoxExpr 3 := .mul ⟨(4722124701594910629551/2361183241434822606848:ℚ),(4722124701594910629553/2361183241434822606848:ℚ)⟩ node86 node4678
def node4702 : BoxExpr 3 := .inv ⟨(2361304138262007884087/4722366482869645213696:ℚ),(2361304138262007884089/4722366482869645213696:ℚ)⟩ node4701
def node4703 : BoxExpr 3 := .mul ⟨(23894219816262268125/2361183241434822606848:ℚ),(11947109908131134063/1180591620717411303424:ℚ)⟩ node4700 node4702
def node4704 : BoxExpr 3 := .mul ⟨(118391259879609692907/4722366482869645213696:ℚ),(118391259879609692913/4722366482869645213696:ℚ)⟩ node50 node4703
def node4705 : BoxExpr 3 := .neg ⟨(-118391259879609692913/4722366482869645213696:ℚ),(-118391259879609692907/4722366482869645213696:ℚ)⟩ node4704
def node4706 : BoxExpr 3 := .add ⟨(1142726359337870923079/1180591620717411303424:ℚ),(4570905437351483692341/4722366482869645213696:ℚ)⟩ node4323 node4705
def node4707 : BoxExpr 3 := .mul ⟨(10466517898453667516693/4722366482869645213696:ℚ),(10659683820378625220875/4722366482869645213696:ℚ)⟩ node112 node4646
def node4708 : BoxExpr 3 := .mul ⟨(12430916920691928186127/4722366482869645213696:ℚ),(12708579618863329037285/4722366482869645213696:ℚ)⟩ node4707 node304
def node4709 : BoxExpr 3 := .add ⟨(11878563919777356174425/2361183241434822606848:ℚ),(23517464615762073725783/2361183241434822606848:ℚ)⟩ node4708 node448
def node4710 : BoxExpr 3 := .mul ⟨(181478784958819358467/36893488147419103232:ℚ),(23234043095718654451385/4722366482869645213696:ℚ)⟩ node111 node4659
def node4711 : BoxExpr 3 := .neg ⟨(-23234043095718654451385/4722366482869645213696:ℚ),(-181478784958819358467/36893488147419103232:ℚ)⟩ node4710
def node4712 : BoxExpr 3 := .add ⟨(523084743836057897465/4722366482869645213696:ℚ),(11902822378397634783895/2361183241434822606848:ℚ)⟩ node4709 node4711
def node4713 : BoxExpr 3 := .mul ⟨(-327799834839118707127/2361183241434822606848:ℚ),(-303800358539278000301/2361183241434822606848:ℚ)⟩ node131 node4646
def node4714 : BoxExpr 3 := .mul ⟨(-55539427376125305469/4722366482869645213696:ℚ),(0/1:ℚ)⟩ node118 node4644
def node4715 : BoxExpr 3 := .add ⟨(-711139097054362719723/4722366482869645213696:ℚ),(-303800358539278000301/2361183241434822606848:ℚ)⟩ node4713 node4714
def node4716 : BoxExpr 3 := .mul ⟨(-847827007563244614313/4722366482869645213696:ℚ),(-721637712583691530805/4722366482869645213696:ℚ)⟩ node4715 node304
def node4717 : BoxExpr 3 := .mul ⟨(160560311057460947791/590295810358705651712:ℚ),(1372146493047348603437/4722366482869645213696:ℚ)⟩ node118 node4646
def node4718 : BoxExpr 3 := .mul ⟨(360133359078877111455/1180591620717411303424:ℚ),(783100120437256560783/2361183241434822606848:ℚ)⟩ node4717 node461
def node4719 : BoxExpr 3 := .add ⟨(592706428752263831507/4722366482869645213696:ℚ),(844562528290821590761/4722366482869645213696:ℚ)⟩ node4716 node4718
def node4720 : BoxExpr 3 := .add ⟨(-541148574035551752613/1180591620717411303424:ℚ),(2258136408862481363665/4722366482869645213696:ℚ)⟩ node4719 node476
def node4721 : BoxExpr 3 := .add ⟨(-95571985807544729357/2361183241434822606848:ℚ),(0/1:ℚ)⟩ node4644 node4644
def node4722 : BoxExpr 3 := .neg ⟨(0/1:ℚ),(95571985807544729357/2361183241434822606848:ℚ)⟩ node4721
def node4723 : BoxExpr 3 := .mul ⟨(2360699641740739622335/1180591620717411303424:ℚ),(2/1:ℚ)⟩ node86 node4659
def node4724 : BoxExpr 3 := .inv ⟨(1/2:ℚ),(2361666940196427770805/4722366482869645213696:ℚ)⟩ node4723
def node4725 : BoxExpr 3 := .mul ⟨(0/1:ℚ),(95591564148762823149/4722366482869645213696:ℚ)⟩ node4722 node4724
def node4726 : BoxExpr 3 := .mul ⟨(0/1:ℚ),(60539778484191953591/4722366482869645213696:ℚ)⟩ node117 node4725
def node4727 : BoxExpr 3 := .neg ⟨(-60539778484191953591/4722366482869645213696:ℚ),(0/1:ℚ)⟩ node4726
def node4728 : BoxExpr 3 := .add ⟨(293097703405543005589/1180591620717411303424:ℚ),(656847573364630350863/2361183241434822606848:ℚ)⟩ node479 node4727
def node4729 : BoxExpr 3 := .add ⟨(-2164594296142207010451/4722366482869645213696:ℚ),(2258136408862481363665/4722366482869645213696:ℚ)⟩ node4719 node492
def node4730 : BoxExpr 3 := .mul ⟨(-2425916396838490416555/4722366482869645213696:ℚ),(-2332685416500644795863/4722366482869645213696:ℚ)⟩ node175 node4646
def node4731 : BoxExpr 3 := .mul ⟨(0/1:ℚ),(92265914062296996691/4722366482869645213696:ℚ)⟩ node148 node4644
def node4732 : BoxExpr 3 := .add ⟨(-2425916396838490416555/4722366482869645213696:ℚ),(-560104875609586949793/1180591620717411303424:ℚ)⟩ node4730 node4731
def node4733 : BoxExpr 3 := .add ⟨(-2425916396838490416555/4722366482869645213696:ℚ),(-2148153588376050802481/4722366482869645213696:ℚ)⟩ node4732 node4731
def node4734 : BoxExpr 3 := .mul ⟨(-723050331450472201889/1180591620717411303424:ℚ),(-2551327867497760111445/4722366482869645213696:ℚ)⟩ node4733 node304
def node4735 : BoxExpr 3 := .mul ⟨(-1139752031930485233243/2361183241434822606848:ℚ),(-1094190272543517367265/2361183241434822606848:ℚ)⟩ node148 node4646
def node4736 : BoxExpr 3 := .mul ⟨(-50473227537841441143/1180591620717411303424:ℚ),(0/1:ℚ)⟩ node36 node4644
def node4737 : BoxExpr 3 := .add ⟨(-1240698487006168115529/2361183241434822606848:ℚ),(-1094190272543517367265/2361183241434822606848:ℚ)⟩ node4735 node4736
def node4738 : BoxExpr 3 := .mul ⟨(-2832324797749785421765/4722366482869645213696:ℚ),(-2454245484000748351851/4722366482869645213696:ℚ)⟩ node4737 node461
def node4739 : BoxExpr 3 := .add ⟨(-5724526123551674229321/4722366482869645213696:ℚ),(-78212083617164194739/73786976294838206464:ℚ)⟩ node4734 node4738
def node4740 : BoxExpr 3 := .mul ⟨(24028790660065639078573/4722366482869645213696:ℚ),(12561242861715195889131/2361183241434822606848:ℚ)⟩ node4647 node514
def node4741 : BoxExpr 3 := .add ⟨(2649558232789481707101/590295810358705651712:ℚ),(22668240239429643426411/4722366482869645213696:ℚ)⟩ node4738 node4740
def node4742 : BoxExpr 3 := .add ⟨(15471939738764179427487/4722366482869645213696:ℚ),(17662666887931134963115/4722366482869645213696:ℚ)⟩ node4739 node4741
def node4743 : BoxExpr 3 := .mul ⟨(-13924289987846787685/4722366482869645213696:ℚ),(-381069638462972777/147573952589676412928:ℚ)⟩ node4650 node189
def node4744 : BoxExpr 3 := .add ⟨(-11375937596839038967/2361183241434822606848:ℚ),(-20884155683162674285/4722366482869645213696:ℚ)⟩ node4374 node4743
def node4745 : BoxExpr 3 := .add ⟨(-31579460399509368183/4722366482869645213696:ℚ),(-14787041467755109853/2361183241434822606848:ℚ)⟩ node4374 node4744
def node4746 : BoxExpr 3 := .add ⟨(1930045034795583757413/590295810358705651712:ℚ),(17633092804995624743409/4722366482869645213696:ℚ)⟩ node4742 node4745
def node4747 : BoxExpr 3 := .add ⟨(26544093556731241430827/4722366482869645213696:ℚ),(1069580120135095975561/147573952589676412928:ℚ)⟩ node4746 node527
def node4748 : BoxExpr 3 := .mul ⟨(-2361666940196427770805/2361183241434822606848:ℚ),(-1/1:ℚ)⟩ node6 node4724
def node4749 : BoxExpr 3 := .mul ⟨(0/1:ℚ),(95591564148762823149/2361183241434822606848:ℚ)⟩ node86 node4725
def node4750 : BoxExpr 3 := .mul ⟨(18881729128751108452899/4722366482869645213696:ℚ),(4/1:ℚ)⟩ node4723 node4723
def node4751 : BoxExpr 3 := .inv ⟨(1/4:ℚ),(1181075369022924765705/4722366482869645213696:ℚ)⟩ node4750
def node4752 : BoxExpr 3 := .mul ⟨(0/1:ℚ),(23907683216037072105/2361183241434822606848:ℚ)⟩ node4749 node4751
def node4753 : BoxExpr 3 := .neg ⟨(-23907683216037072105/2361183241434822606848:ℚ),(0/1:ℚ)⟩ node4752
def node4754 : BoxExpr 3 := .mul ⟨(-967694806958692457/2361183241434822606848:ℚ),(0/1:ℚ)⟩ node4722 node4753
def node4755 : BoxExpr 3 := .add ⟨(-1181317317501693231631/1180591620717411303424:ℚ),(-1/1:ℚ)⟩ node4748 node4754
def node4756 : BoxExpr 3 := .mul ⟨(-11715273006606030978513/4722366482869645213696:ℚ),(-11690549858194116419425/4722366482869645213696:ℚ)⟩ node11 node4755
def node4757 : BoxExpr 3 := .neg ⟨(11690549858194116419425/4722366482869645213696:ℚ),(11715273006606030978513/4722366482869645213696:ℚ)⟩ node4756
def cert_iv31 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-155606922197/15377579688788:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (155606922197/15377579688788:ℚ)],
    whole := node4662, centerValue := node4681, gradient := ![node4688, node4698, node4706],
    hessian := ![![node4712, node4720, node4728], ![node4729, node4747, node4381], ![node4728, node4381, node4757]] }

end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part8
end

section
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646CheckB4Part8
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part8

theorem cert_iv28_check : cert_iv28.check = true := by decide +kernel

theorem cert_iv28_lower_pos : 0 < cert_iv28.lower := by decide +kernel

theorem positive_iv28 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(111/640:ℝ)) ≤ r) (hrhi : r ≤ (-(23/160:ℝ))) :
    0 < node4275.eval ![A,ρ,r] := by
  apply cert_iv28.positive_sound cert_iv28_check cert_iv28_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv28,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv28,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv28,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv29_check : cert_iv29.check = true := by decide +kernel

theorem cert_iv29_lower_pos : 0 < cert_iv29.lower := by decide +kernel

theorem positive_iv29 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(23/160:ℝ)) ≤ r) (hrhi : r ≤ (-(1/40:ℝ))) :
    0 < node4419.eval ![A,ρ,r] := by
  apply cert_iv29.positive_sound cert_iv29_check cert_iv29_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv29,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv29,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv29,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv30_check : cert_iv30.check = true := by decide +kernel

theorem cert_iv30_lower_pos : 0 < cert_iv30.lower := by decide +kernel

theorem positive_iv30 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(1/40:ℝ)) ≤ r) (hrhi : r ≤ (-(155606922197/7688789844394:ℝ))) :
    0 < node4548.eval ![A,ρ,r] := by
  apply cert_iv30.positive_sound cert_iv30_check cert_iv30_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv30,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv30,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv30,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv31_check : cert_iv31.check = true := by decide +kernel

theorem cert_iv31_lower_pos : 0 < cert_iv31.lower := by decide +kernel

theorem positive_iv31 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(155606922197/7688789844394:ℝ)) ≤ r) (hrhi : r ≤ (0:ℝ)) :
    0 < node4662.eval ![A,ρ,r] := by
  apply cert_iv31.positive_sound cert_iv31_check cert_iv31_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv31,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv31,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv31,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part8
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
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646BoundB4Part8
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part8
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate.CapacityCore
noncomputable section
namespace Parameters
def b : ℚ := (103531361122339324647880530522418473224550678173/6474633415922124204664207433178390079472570088576:ℚ)
def c : ℚ := (148022665013912365111/4722366482869645213696:ℚ)
def theta : ℚ := (105113898053531722649817636563532003778556764000751/182628568201966125342452015454275643968150995402752:ℚ)
end Parameters

theorem iv_shape28 : SplitDataB4Part8.node4275.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (1)).canonicalize := by decide +kernel

theorem iv_bound28 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(111/640:ℝ)) ≤ r) (hrhi : r ≤ (-(23/160:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part8.node4275 3 4 0
    Parameters.b Parameters.c Parameters.theta (1) iv_shape28 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part8.positive_iv28 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part8.node4275.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape29 : SplitDataB4Part8.node4419.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (1)).canonicalize := by decide +kernel

theorem iv_bound29 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(23/160:ℝ)) ≤ r) (hrhi : r ≤ (-(1/40:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part8.node4419 3 4 0
    Parameters.b Parameters.c Parameters.theta (1) iv_shape29 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part8.positive_iv29 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part8.node4419.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape30 : SplitDataB4Part8.node4548.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 1 Parameters.b Parameters.c Parameters.theta (1)).canonicalize := by decide +kernel

theorem iv_bound30 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(1/40:ℝ)) ≤ r) (hrhi : r ≤ (-(155606922197/7688789844394:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 1 r := by
    norm_num [sourceFADomain] <;> constructor <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part8.node4548 3 4 1
    Parameters.b Parameters.c Parameters.theta (1) iv_shape30 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part8.positive_iv30 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part8.node4548.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape31 : SplitDataB4Part8.node4662.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 1 Parameters.b Parameters.c Parameters.theta (1)).canonicalize := by decide +kernel

theorem iv_bound31 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(155606922197/7688789844394:ℝ)) ≤ r) (hrhi : r ≤ (0:ℝ)) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 1 r := by
    norm_num [sourceFADomain] <;> constructor <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part8.node4662 3 4 1
    Parameters.b Parameters.c Parameters.theta (1) iv_shape31 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part8.positive_iv31 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part8.node4662.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem actual_bound (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (r : ℝ)
    (hrlo : (-(111/640:ℝ)) ≤ r) (hrhi : r ≤ (0:ℝ)) : fA A r+3/10^6 ≤ l40Lhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) r := by
  have hc : 0 ≤ (Parameters.c:ℝ) := by norm_num [Parameters.c]
  have hθ : 0 ≤ (Parameters.theta:ℝ) := by norm_num [Parameters.theta]
  by_cases h0 : r ≤ (-(23/160:ℝ))
  · have h := iv_bound28 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (1) r hθ hc (Or.inr rfl))
  by_cases h1 : r ≤ (-(1/40:ℝ))
  · have h := iv_bound29 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (1) r hθ hc (Or.inr rfl))
  by_cases h2 : r ≤ (-(155606922197/7688789844394:ℝ))
  · have h := iv_bound30 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (1) r hθ hc (Or.inr rfl))
  have h := iv_bound31 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
  exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
    (Parameters.theta:ℝ) (1) r hθ hc (Or.inr rfl))
end
end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part8
end

section
-- Source module: Solutions.Sol_GaussLocalMaxCase1FamilyAdaptive0Seed25646B4Part8
set_option autoImplicit false
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate
open GaussLocalMaxColoring.Certificate.CapacityCore
theorem solution (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (r : ℝ)
    (hrlo : (-(111/640:ℝ)) ≤ r) (hrhi : r ≤ (0:ℝ)) :
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
  have h := GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part8.actual_bound A ρ hAlo hAhi hρlo hρhi r hrlo hrhi
  simpa only [Case2Static,constructedA,constructedMu,constructedMass,constructedKappa,thresholdCapacity,
    GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part8.Parameters.b,GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part8.Parameters.c,GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part8.Parameters.theta,
    show ¬ (4:ℕ)=1 by decide,show ¬ (4:ℕ)=2 by decide,show ¬ (4:ℕ)=3 by decide,ite_false,and_assoc] using h
end

#print axioms solution
