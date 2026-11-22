-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_40_adaptive0seed25646_b4_part_4
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T14:29:08.885337+00:00
-- url     : https://prove2.me/submissions/25d142c3-ec0b-4508-bba8-ba82b57c0826

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
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646DefsB4Part4
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part4

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
def node2056 : BoxExpr 3 := .var 2
def node2057 : BoxExpr 3 := .mul ⟨(-434409353618688916115/4722366482869645213696:ℚ),(-428340154705006685899/4722366482869645213696:ℚ)⟩ node13 node2056
def node2058 : BoxExpr 3 := .add ⟨(1926773887816133690733/4722366482869645213696:ℚ),(1932843086729815920949/4722366482869645213696:ℚ)⟩ node2057 node301
def node2059 : BoxExpr 3 := .mul ⟨(4042072280828176056655/4722366482869645213696:ℚ),(4083072171709814124041/4722366482869645213696:ℚ)⟩ node36 node2058
def node2060 : BoxExpr 3 := .mul ⟨(2400352495352359506631/2361183241434822606848:ℚ),(2433939348395057420557/2361183241434822606848:ℚ)⟩ node2059 node304
def node2061 : BoxExpr 3 := .add ⟨(-35818677074749370139/1180591620717411303424:ℚ),(-129448873615752171617/4722366482869645213696:ℚ)⟩ node2056 node306
def node2062 : BoxExpr 3 := .mul ⟨(2798339990768703813/2361183241434822606848:ℚ),(6194435450846865249/4722366482869645213696:ℚ)⟩ node2061 node308
def node2063 : BoxExpr 3 := .mul ⟨(381207085017483029/295147905179352825856:ℚ),(1690900629754914103/1180591620717411303424:ℚ)⟩ node2062 node37
def node2064 : BoxExpr 3 := .add ⟨(2403402152032499370863/2361183241434822606848:ℚ),(2437321149654567248763/2361183241434822606848:ℚ)⟩ node2060 node2063
def node2065 : BoxExpr 3 := .add ⟨(15521248559204385101533/4722366482869645213696:ℚ),(982275393510557812173/295147905179352825856:ℚ)⟩ node2064 node316
def node2066 : BoxExpr 3 := .add ⟨(10759302326242563749169/4722366482869645213696:ℚ),(10968583259570180165503/4722366482869645213696:ℚ)⟩ node2065 node323
def node2067 : BoxExpr 3 := .add ⟨(10759288159143115140233/4722366482869645213696:ℚ),(1371071136558841444571/590295810358705651712:ℚ)⟩ node2066 node325
def node2068 : BoxExpr 3 := .mul ⟨(30732745408536243077/590295810358705651712:ℚ),(15491583329220647977/295147905179352825856:ℚ)⟩ node2056 node2056
def node2069 : BoxExpr 3 := .neg ⟨(-15491583329220647977/295147905179352825856:ℚ),(-30732745408536243077/590295810358705651712:ℚ)⟩ node2068
def node2070 : BoxExpr 3 := .add ⟨(279656321850132177879/295147905179352825856:ℚ),(559563064950169408635/590295810358705651712:ℚ)⟩ node12 node2069
def node2071 : BoxExpr 3 := .sqrt ⟨(4596763454479980449475/4722366482869645213696:ℚ),(4597792394593292514121/4722366482869645213696:ℚ)⟩ node2070
def node2072 : BoxExpr 3 := .mul ⟨(11379610740898573097155/4722366482869645213696:ℚ),(11399221939002874786565/4722366482869645213696:ℚ)⟩ node11 node2071
def node2073 : BoxExpr 3 := .neg ⟨(1077520438205559183769/4722366482869645213696:ℚ),(1081901539923065202279/4722366482869645213696:ℚ)⟩ node2056
def node2074 : BoxExpr 3 := .add ⟨(479730638066909026713/2361183241434822606848:ℚ),(963842377851324071937/4722366482869645213696:ℚ)⟩ node332 node2073
def node2075 : BoxExpr 3 := .mul ⟨(685055351159546090145/4722366482869645213696:ℚ),(172045864446461346841/1180591620717411303424:ℚ)⟩ node2074 node335
def node2076 : BoxExpr 3 := .neg ⟨(-172045864446461346841/1180591620717411303424:ℚ),(-685055351159546090145/4722366482869645213696:ℚ)⟩ node2075
def node2077 : BoxExpr 3 := .add ⟨(10691427283112727709791/4722366482869645213696:ℚ),(2678541646960832174105/1180591620717411303424:ℚ)⟩ node2072 node2076
def node2078 : BoxExpr 3 := .mul ⟨(97468710204902756843/2361183241434822606848:ℚ),(196721735323170635777/4722366482869645213696:ℚ)⟩ node2074 node2074
def node2079 : BoxExpr 3 := .mul ⟨(2515911082164052411/73786976294838206464:ℚ),(1269469948257335509/36893488147419103232:ℚ)⟩ node2078 node340
def node2080 : BoxExpr 3 := .add ⟨(10852445592371227064095/4722366482869645213696:ℚ),(2719164685305066910393/1180591620717411303424:ℚ)⟩ node2077 node2079
def node2081 : BoxExpr 3 := .neg ⟨(-2719164685305066910393/1180591620717411303424:ℚ),(-10852445592371227064095/4722366482869645213696:ℚ)⟩ node2080
def node2082 : BoxExpr 3 := .add ⟨(-117370582077152501339/4722366482869645213696:ℚ),(116123500099504492473/4722366482869645213696:ℚ)⟩ node2067 node2081
def node2083 : BoxExpr 3 := .var 2
def node2084 : BoxExpr 3 := .mul ⟨(-431370373060130294989/4722366482869645213696:ℚ),(-107842593265032573747/1180591620717411303424:ℚ)⟩ node51 node2083
def node2085 : BoxExpr 3 := .add ⟨(1929812868374692311859/4722366482869645213696:ℚ),(482453217093673077965/1180591620717411303424:ℚ)⟩ node2084 node301
def node2086 : BoxExpr 3 := .mul ⟨(507815111250466733921/590295810358705651712:ℚ),(1015630222500933467845/1180591620717411303424:ℚ)⟩ node68 node2085
def node2087 : BoxExpr 3 := .mul ⟨(4834143876941278699655/4722366482869645213696:ℚ),(604267984617659837459/590295810358705651712:ℚ)⟩ node2086 node349
def node2088 : BoxExpr 3 := .add ⟨(-136361790957374826087/4722366482869645213696:ℚ),(-68180895478687413043/2361183241434822606848:ℚ)⟩ node2083 node351
def node2089 : BoxExpr 3 := .mul ⟨(5895557716192136437/4722366482869645213696:ℚ),(2947778858096068219/2361183241434822606848:ℚ)⟩ node2088 node308
def node2090 : BoxExpr 3 := .mul ⟨(6431123916888914903/4722366482869645213696:ℚ),(6431123916888914905/4722366482869645213696:ℚ)⟩ node2089 node69
def node2091 : BoxExpr 3 := .add ⟨(2420287500429083807279/2361183241434822606848:ℚ),(4840575000858167614577/4722366482869645213696:ℚ)⟩ node2087 node2090
def node2092 : BoxExpr 3 := .add ⟨(7809788756887214783227/2361183241434822606848:ℚ),(7809788756887214783263/2361183241434822606848:ℚ)⟩ node2091 node358
def node2093 : BoxExpr 3 := .add ⟨(10864692878994146475637/4722366482869645213696:ℚ),(5432346439497073237857/2361183241434822606848:ℚ)⟩ node2092 node361
def node2094 : BoxExpr 3 := .add ⟨(10864678711894697866701/4722366482869645213696:ℚ),(10864678711894697866779/4722366482869645213696:ℚ)⟩ node2093 node325
def node2095 : BoxExpr 3 := .mul ⟨(3508129/67108864:ℚ),(3508129/67108864:ℚ)⟩ node2083 node2083
def node2096 : BoxExpr 3 := .neg ⟨(-3508129/67108864:ℚ),(-3508129/67108864:ℚ)⟩ node2095
def node2097 : BoxExpr 3 := .add ⟨(63600735/67108864:ℚ),(63600735/67108864:ℚ)⟩ node12 node2096
def node2098 : BoxExpr 3 := .sqrt ⟨(4597278475209478525489/4722366482869645213696:ℚ),(2298639237604739262745/2361183241434822606848:ℚ)⟩ node2097
def node2099 : BoxExpr 3 := .mul ⟨(5694657482884510961203/2361183241434822606848:ℚ),(11389314965769021922417/4722366482869645213696:ℚ)⟩ node50 node2098
def node2100 : BoxExpr 3 := .neg ⟨(1873/8192:ℚ),(1873/8192:ℚ)⟩ node2083
def node2101 : BoxExpr 3 := .add ⟨(961651826992571062681/4722366482869645213696:ℚ),(480825913496285531341/2361183241434822606848:ℚ)⟩ node332 node2100
def node2102 : BoxExpr 3 := .mul ⟨(343309702236347869377/2361183241434822606848:ℚ),(686619404472695738755/4722366482869645213696:ℚ)⟩ node2101 node335
def node2103 : BoxExpr 3 := .neg ⟨(-686619404472695738755/4722366482869645213696:ℚ),(-343309702236347869377/2361183241434822606848:ℚ)⟩ node2102
def node2104 : BoxExpr 3 := .add ⟨(10702695561296326183651/4722366482869645213696:ℚ),(10702695561296326183663/4722366482869645213696:ℚ)⟩ node2099 node2103
def node2105 : BoxExpr 3 := .mul ⟨(195828561741822149263/4722366482869645213696:ℚ),(12239285108863884329/295147905179352825856:ℚ)⟩ node2101 node2101
def node2106 : BoxExpr 3 := .mul ⟨(161754391998745095291/4722366482869645213696:ℚ),(161754391998745095293/4722366482869645213696:ℚ)⟩ node2105 node340
def node2107 : BoxExpr 3 := .add ⟨(5432224976647535639471/2361183241434822606848:ℚ),(2716112488323767819739/1180591620717411303424:ℚ)⟩ node2104 node2106
def node2108 : BoxExpr 3 := .neg ⟨(-2716112488323767819739/1180591620717411303424:ℚ),(-5432224976647535639471/2361183241434822606848:ℚ)⟩ node2107
def node2109 : BoxExpr 3 := .add ⟨(228758599626587745/4722366482869645213696:ℚ),(228758599626587837/4722366482869645213696:ℚ)⟩ node2094 node2108
def node2110 : BoxExpr 3 := .mul ⟨(1094291581298683441859/4722366482869645213696:ℚ),(136786447662335430233/590295810358705651712:ℚ)⟩ node78 node2085
def node2111 : BoxExpr 3 := .mul ⟨(1302138029699721255613/4722366482869645213696:ℚ),(1302138029699721255621/4722366482869645213696:ℚ)⟩ node2110 node349
def node2112 : BoxExpr 3 := .add ⟨(2590684683490546121603/2361183241434822606848:ℚ),(2590684683490546121817/2361183241434822606848:ℚ)⟩ node2111 node385
def node2113 : BoxExpr 3 := .add ⟨(706875826617084598611/1180591620717411303424:ℚ),(1413751653234169197437/2361183241434822606848:ℚ)⟩ node2112 node387
def node2114 : BoxExpr 3 := .mul ⟨(177729971510526371191/295147905179352825856:ℚ),(355459943021052742383/590295810358705651712:ℚ)⟩ node77 node2098
def node2115 : BoxExpr 3 := .neg ⟨(-355459943021052742383/590295810358705651712:ℚ),(-177729971510526371191/295147905179352825856:ℚ)⟩ node2114
def node2116 : BoxExpr 3 := .add ⟨(-4044059425020886155/1180591620717411303424:ℚ),(-8088118850041772091/2361183241434822606848:ℚ)⟩ node2113 node2115
def node2117 : BoxExpr 3 := .mul ⟨(-920273286035224000485/2361183241434822606848:ℚ),(-28758540188600750015/73786976294838206464:ℚ)⟩ node98 node2085
def node2118 : BoxExpr 3 := .mul ⟨(-2272939786091585060585/4722366482869645213696:ℚ),(-2272939786091585060579/4722366482869645213696:ℚ)⟩ node68 node2083
def node2119 : BoxExpr 3 := .add ⟨(-4113486358162033061555/4722366482869645213696:ℚ),(-4113486358162033061539/4722366482869645213696:ℚ)⟩ node2117 node2118
def node2120 : BoxExpr 3 := .mul ⟨(-305924348292584953881/295147905179352825856:ℚ),(-2447394786340679631037/2361183241434822606848:ℚ)⟩ node2119 node349
def node2121 : BoxExpr 3 := .mul ⟨(287274013746117361181/295147905179352825856:ℚ),(2298192109968938889459/2361183241434822606848:ℚ)⟩ node2086 node399
def node2122 : BoxExpr 3 := .add ⟨(-4662583636616898175/73786976294838206464:ℚ),(-74601338185870370789/1180591620717411303424:ℚ)⟩ node2120 node2121
def node2123 : BoxExpr 3 := .mul ⟨(3057409671757309427/4722366482869645213696:ℚ),(764352417939327357/1180591620717411303424:ℚ)⟩ node2089 node103
def node2124 : BoxExpr 3 := .add ⟨(-54150609397004447053/2361183241434822606848:ℚ),(-108301218794008894103/4722366482869645213696:ℚ)⟩ node403 node2123
def node2125 : BoxExpr 3 := .add ⟨(-203353285768745188653/2361183241434822606848:ℚ),(-406706571537490377259/4722366482869645213696:ℚ)⟩ node2122 node2124
def node2126 : BoxExpr 3 := .add ⟨(-10598667114102693379/590295810358705651712:ℚ),(-84789336912821546869/4722366482869645213696:ℚ)⟩ node2125 node409
def node2127 : BoxExpr 3 := .add ⟨(-1873/4096:ℚ),(-1873/4096:ℚ)⟩ node2083 node2083
def node2128 : BoxExpr 3 := .neg ⟨(1873/4096:ℚ),(1873/4096:ℚ)⟩ node2127
def node2129 : BoxExpr 3 := .mul ⟨(4597278475209478525489/2361183241434822606848:ℚ),(2298639237604739262745/1180591620717411303424:ℚ)⟩ node86 node2098
def node2130 : BoxExpr 3 := .inv ⟨(1212714507005934231255/2361183241434822606848:ℚ),(151589313375741778907/295147905179352825856:ℚ)⟩ node2129
def node2131 : BoxExpr 3 := .mul ⟨(277272249953871437395/1180591620717411303424:ℚ),(554544499907742874791/2361183241434822606848:ℚ)⟩ node2128 node2130
def node2132 : BoxExpr 3 := .mul ⟨(1373830627411876742249/2361183241434822606848:ℚ),(2747661254823753484505/4722366482869645213696:ℚ)⟩ node50 node2131
def node2133 : BoxExpr 3 := .add ⟨(1529857730898170041769/1180591620717411303424:ℚ),(1529857730898170041771/1180591620717411303424:ℚ)⟩ node2132 node335
def node2134 : BoxExpr 3 := .mul ⟨(-480825913496285531341/2361183241434822606848:ℚ),(-961651826992571062681/4722366482869645213696:ℚ)⟩ node422 node2101
def node2135 : BoxExpr 3 := .mul ⟨(-480825913496285531341/2361183241434822606848:ℚ),(-961651826992571062681/4722366482869645213696:ℚ)⟩ node2101 node422
def node2136 : BoxExpr 3 := .add ⟨(-480825913496285531341/1180591620717411303424:ℚ),(-961651826992571062681/2361183241434822606848:ℚ)⟩ node2134 node2135
def node2137 : BoxExpr 3 := .mul ⟨(-1588648818191727395551/4722366482869645213696:ℚ),(-397162204547931848887/1180591620717411303424:ℚ)⟩ node2136 node340
def node2138 : BoxExpr 3 := .add ⟨(4530782105400952771525/4722366482869645213696:ℚ),(283173881587559548221/295147905179352825856:ℚ)⟩ node2133 node2137
def node2139 : BoxExpr 3 := .neg ⟨(-283173881587559548221/295147905179352825856:ℚ),(-4530782105400952771525/4722366482869645213696:ℚ)⟩ node2138
def node2140 : BoxExpr 3 := .add ⟨(-27356403521318357937/4722366482869645213696:ℚ),(-27356403521318357907/4722366482869645213696:ℚ)⟩ node414 node2139
def node2141 : BoxExpr 3 := .mul ⟨(2170498639557343882077/1180591620717411303424:ℚ),(1090740005762129630241/590295810358705651712:ℚ)⟩ node112 node2058
def node2142 : BoxExpr 3 := .mul ⟨(10311466918256905908389/4722366482869645213696:ℚ),(325097733673096644657/147573952589676412928:ℚ)⟩ node2141 node304
def node2143 : BoxExpr 3 := .add ⟨(2704709729639961258889/590295810358705651712:ℚ),(44729477090199911043305/4722366482869645213696:ℚ)⟩ node2142 node448
def node2144 : BoxExpr 3 := .mul ⟨(2827009524505187976427/590295810358705651712:ℚ),(5655284645349749792369/1180591620717411303424:ℚ)⟩ node111 node2071
def node2145 : BoxExpr 3 := .neg ⟨(-5655284645349749792369/1180591620717411303424:ℚ),(-2827009524505187976427/590295810358705651712:ℚ)⟩ node2144
def node2146 : BoxExpr 3 := .add ⟨(-245865186069827274591/1180591620717411303424:ℚ),(22113400894158407231889/4722366482869645213696:ℚ)⟩ node2143 node2145
def node2147 : BoxExpr 3 := .mul ⟨(-268333957941762463431/2361183241434822606848:ℚ),(-31500364844546641137/295147905179352825856:ℚ)⟩ node131 node2058
def node2148 : BoxExpr 3 := .mul ⟨(-157180452768021475765/1180591620717411303424:ℚ),(-595854524205181004465/4722366482869645213696:ℚ)⟩ node118 node2056
def node2149 : BoxExpr 3 := .add ⟨(-582694863477805414961/2361183241434822606848:ℚ),(-1099860361717927262657/4722366482869645213696:ℚ)⟩ node2147 node2148
def node2150 : BoxExpr 3 := .mul ⟨(-1389389064589977494611/4722366482869645213696:ℚ),(-326571666755036079561/1180591620717411303424:ℚ)⟩ node2149 node304
def node2151 : BoxExpr 3 := .mul ⟨(1065480428461840325941/4722366482869645213696:ℚ),(35100831763689936997/147573952589676412928:ℚ)⟩ node118 node2058
def node2152 : BoxExpr 3 := .mul ⟨(1194924957505347436755/4722366482869645213696:ℚ),(1282077246223940559231/4722366482869645213696:ℚ)⟩ node2151 node461
def node2153 : BoxExpr 3 := .add ⟨(-1519250836598672327/36893488147419103232:ℚ),(-24209420796203759013/4722366482869645213696:ℚ)⟩ node2150 node2152
def node2154 : BoxExpr 3 := .add ⟨(-2951764831979100899815/4722366482869645213696:ℚ),(1389364459775456013891/4722366482869645213696:ℚ)⟩ node2153 node476
def node2155 : BoxExpr 3 := .add ⟨(-1081901539923065202279/2361183241434822606848:ℚ),(-1077520438205559183769/2361183241434822606848:ℚ)⟩ node2056 node2056
def node2156 : BoxExpr 3 := .neg ⟨(1077520438205559183769/2361183241434822606848:ℚ),(1081901539923065202279/2361183241434822606848:ℚ)⟩ node2155
def node2157 : BoxExpr 3 := .mul ⟨(4596763454479980449475/2361183241434822606848:ℚ),(4597792394593292514121/2361183241434822606848:ℚ)⟩ node86 node2071
def node2158 : BoxExpr 3 := .inv ⟨(2425157911083029978269/4722366482869645213696:ℚ),(2425700758736719331371/4722366482869645213696:ℚ)⟩ node2157
def node2159 : BoxExpr 3 := .mul ⟨(553357564379443314865/2361183241434822606848:ℚ),(1111463667968035849883/4722366482869645213696:ℚ)⟩ node2156 node2158
def node2160 : BoxExpr 3 := .mul ⟨(668231458128587675807/4722366482869645213696:ℚ),(351954510061666493463/2361183241434822606848:ℚ)⟩ node117 node2159
def node2161 : BoxExpr 3 := .neg ⟨(-351954510061666493463/2361183241434822606848:ℚ),(-668231458128587675807/4722366482869645213696:ℚ)⟩ node2160
def node2162 : BoxExpr 3 := .add ⟨(529021571983030989021/4722366482869645213696:ℚ),(645463688600673025919/4722366482869645213696:ℚ)⟩ node479 node2161
def node2163 : BoxExpr 3 := .add ⟨(-1475882415989550449907/2361183241434822606848:ℚ),(1389364459775456013891/4722366482869645213696:ℚ)⟩ node2153 node492
def node2164 : BoxExpr 3 := .mul ⟨(-1985833057905519736245/4722366482869645213696:ℚ),(-967483278039954630505/2361183241434822606848:ℚ)⟩ node175 node2058
def node2165 : BoxExpr 3 := .mul ⟨(1015160938500901431685/4722366482869645213696:ℚ),(1044475885511296233277/4722366482869645213696:ℚ)⟩ node148 node2056
def node2166 : BoxExpr 3 := .add ⟨(-60667007462788644035/295147905179352825856:ℚ),(-890490670568613027733/4722366482869645213696:ℚ)⟩ node2164 node2165
def node2167 : BoxExpr 3 := .add ⟨(44488819096283127125/4722366482869645213696:ℚ),(19248151867835400693/590295810358705651712:ℚ)⟩ node2166 node2165
def node2168 : BoxExpr 3 := .mul ⟨(26419331598682606909/2361183241434822606848:ℚ),(45895670950523645489/1180591620717411303424:ℚ)⟩ node2167 node304
def node2169 : BoxExpr 3 := .mul ⟨(-1865981256214932941291/4722366482869645213696:ℚ),(-1815265417602512677715/4722366482869645213696:ℚ)⟩ node148 node2058
def node2170 : BoxExpr 3 := .mul ⟨(-2285484062580483756019/4722366482869645213696:ℚ),(-2260470480131472858365/4722366482869645213696:ℚ)⟩ node36 node2056
def node2171 : BoxExpr 3 := .add ⟨(-2075732659397708348655/2361183241434822606848:ℚ),(-254733493608374096005/295147905179352825856:ℚ)⟩ node2169 node2170
def node2172 : BoxExpr 3 := .mul ⟨(-2369290019405822979473/2361183241434822606848:ℚ),(-2285447209684352073555/2361183241434822606848:ℚ)⟩ node2171 node461
def node2173 : BoxExpr 3 := .add ⟨(-585717671951785093141/590295810358705651712:ℚ),(-2193655867783304782577/2361183241434822606848:ℚ)⟩ node2168 node2172
def node2174 : BoxExpr 3 := .mul ⟨(19931923088035238833443/4722366482869645213696:ℚ),(20565037901291282126075/4722366482869645213696:ℚ)⟩ node2059 node514
def node2175 : BoxExpr 3 := .add ⟨(15193343049223592874497/4722366482869645213696:ℚ),(15994143481922577978965/4722366482869645213696:ℚ)⟩ node2172 node2174
def node2176 : BoxExpr 3 := .add ⟨(10507601673609312129369/4722366482869645213696:ℚ),(11606831746355968413811/4722366482869645213696:ℚ)⟩ node2173 node2175
def node2177 : BoxExpr 3 := .mul ⟨(5658837404249843639/2361183241434822606848:ℚ),(12719261883895603411/4722366482869645213696:ℚ)⟩ node2062 node189
def node2178 : BoxExpr 3 := .add ⟨(-21020335435300456613/2361183241434822606848:ℚ),(-39807010187735182523/4722366482869645213696:ℚ)⟩ node518 node2177
def node2179 : BoxExpr 3 := .add ⟨(-47699508274850756865/2361183241434822606848:ℚ),(-92333282259365968457/4722366482869645213696:ℚ)⟩ node518 node2178
def node2180 : BoxExpr 3 := .add ⟨(10412202657059610615639/4722366482869645213696:ℚ),(5757249232048301222677/2361183241434822606848:ℚ)⟩ node2176 node2179
def node2181 : BoxExpr 3 := .add ⟨(10757967967713090993581/2361183241434822606848:ℚ),(28107969503424048919897/4722366482869645213696:ℚ)⟩ node2180 node527
def node2182 : BoxExpr 3 := .mul ⟨(-2425700758736719331371/2361183241434822606848:ℚ),(-2425157911083029978269/2361183241434822606848:ℚ)⟩ node6 node2158
def node2183 : BoxExpr 3 := .mul ⟨(553357564379443314865/1180591620717411303424:ℚ),(1111463667968035849883/2361183241434822606848:ℚ)⟩ node86 node2159
def node2184 : BoxExpr 3 := .mul ⟨(17898004598408459384253/4722366482869645213696:ℚ),(17906018078405421076321/4722366482869645213696:ℚ)⟩ node2157 node2157
def node2185 : BoxExpr 3 := .inv ⟨(311358241414728934243/1180591620717411303424:ℚ),(1245990583805843236989/4722366482869645213696:ℚ)⟩ node2184
def node2186 : BoxExpr 3 := .mul ⟨(583749486597318046329/4722366482869645213696:ℚ),(586516641414467077769/4722366482869645213696:ℚ)⟩ node2183 node2185
def node2187 : BoxExpr 3 := .neg ⟨(-586516641414467077769/4722366482869645213696:ℚ),(-583749486597318046329/4722366482869645213696:ℚ)⟩ node2186
def node2188 : BoxExpr 3 := .mul ⟨(-67185939490153308811/1180591620717411303424:ℚ),(-266392710045826877977/4722366482869645213696:ℚ)⟩ node2156 node2187
def node2189 : BoxExpr 3 := .add ⟨(-2560072637717025948993/2361183241434822606848:ℚ),(-5116708532211886834515/4722366482869645213696:ℚ)⟩ node2182 node2188
def node2190 : BoxExpr 3 := .mul ⟨(-793392613040282521655/295147905179352825856:ℚ),(-12666771294150207414953/4722366482869645213696:ℚ)⟩ node11 node2189
def node2191 : BoxExpr 3 := .add ⟨(-4892932378943866453455/4722366482869645213696:ℚ),(-4865421864449553521927/4722366482869645213696:ℚ)⟩ node2190 node546
def node2192 : BoxExpr 3 := .neg ⟨(4865421864449553521927/4722366482869645213696:ℚ),(4892932378943866453455/4722366482869645213696:ℚ)⟩ node2191
def cert_iv12 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-1873/8192:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/40960:ℚ)],
    whole := node2082, centerValue := node2109, gradient := ![node2116, node2126, node2140],
    hessian := ![![node2146, node2154, node2162], ![node2163, node2181, node536], ![node2162, node536, node2192]] }
def node2193 : BoxExpr 3 := .var 2
def node2194 : BoxExpr 3 := .mul ⟨(-108162559114457230659/1180591620717411303424:ℚ),(-426598561951016716493/4722366482869645213696:ℚ)⟩ node13 node2193
def node2195 : BoxExpr 3 := .add ⟨(482133251244248421053/1180591620717411303424:ℚ),(1934584679483805890355/4722366482869645213696:ℚ)⟩ node2194 node301
def node2196 : BoxExpr 3 := .mul ⟨(1011440658835580570185/1180591620717411303424:ℚ),(4086751233376583519853/4722366482869645213696:ℚ)⟩ node36 node2195
def node2197 : BoxExpr 3 := .mul ⟨(4805087966095228752309/4722366482869645213696:ℚ),(2436132455099848321253/2361183241434822606848:ℚ)⟩ node2196 node304
def node2198 : BoxExpr 3 := .add ⟨(-138893606581491462047/4722366482869645213696:ℚ),(-31266942974561538277/1180591620717411303424:ℚ)⟩ node2193 node306
def node2199 : BoxExpr 3 := .mul ⟨(5407264472583443403/4722366482869645213696:ℚ),(3002509970946450513/2361183241434822606848:ℚ)⟩ node2198 node308
def node2200 : BoxExpr 3 := .mul ⟨(5892886595087101453/4722366482869645213696:ℚ),(6556782830015184779/4722366482869645213696:ℚ)⟩ node2199 node37
def node2201 : BoxExpr 3 := .add ⟨(2405490426345157926881/2361183241434822606848:ℚ),(4878821693029711827285/4722366482869645213696:ℚ)⟩ node2197 node2200
def node2202 : BoxExpr 3 := .add ⟨(15525425107829702213569/4722366482869645213696:ℚ),(15720585689889502324527/4722366482869645213696:ℚ)⟩ node2201 node316
def node2203 : BoxExpr 3 := .add ⟨(10763478874867880861205/4722366482869645213696:ℚ),(5486381326645378747631/2361183241434822606848:ℚ)⟩ node2202 node323
def node2204 : BoxExpr 3 := .add ⟨(10763464707768432252269/4722366482869645213696:ℚ),(10972748486191308886327/4722366482869645213696:ℚ)⟩ node2203 node325
def node2205 : BoxExpr 3 := .mul ⟨(243866722266376925347/4722366482869645213696:ℚ),(122930981634144972309/2361183241434822606848:ℚ)⟩ node2193 node2193
def node2206 : BoxExpr 3 := .neg ⟨(-122930981634144972309/2361183241434822606848:ℚ),(-243866722266376925347/4722366482869645213696:ℚ)⟩ node2205
def node2207 : BoxExpr 3 := .add ⟨(2238252259800677634539/2361183241434822606848:ℚ),(4478499760603268288349/4722366482869645213696:ℚ)⟩ node12 node2206
def node2208 : BoxExpr 3 := .sqrt ⟨(4597792394593292514119/4722366482869645213696:ℚ),(1149704232699996525119/1180591620717411303424:ℚ)⟩ node2207
def node2209 : BoxExpr 3 := .mul ⟨(5691078977203379572331/2361183241434822606848:ℚ),(89076266037001833813/36893488147419103232:ℚ)⟩ node11 node2208
def node2210 : BoxExpr 3 := .neg ⟨(268284834122013291315/1180591620717411303424:ℚ),(538760219102779591885/2361183241434822606848:ℚ)⟩ node2193
def node2211 : BoxExpr 3 := .add ⟨(955080174416312034917/4722366482869645213696:ℚ),(239865319033454513357/1180591620717411303424:ℚ)⟩ node332 node2210
def node2212 : BoxExpr 3 := .mul ⟨(340963622266623396465/2361183241434822606848:ℚ),(171263837789886522537/1180591620717411303424:ℚ)⟩ node2211 node335
def node2213 : BoxExpr 3 := .neg ⟨(-171263837789886522537/1180591620717411303424:ℚ),(-340963622266623396465/2361183241434822606848:ℚ)⟩ node2212
def node2214 : BoxExpr 3 := .add ⟨(5348551301623606527257/2361183241434822606848:ℚ),(5359917404101493967567/2361183241434822606848:ℚ)⟩ node2209 node2213
def node2215 : BoxExpr 3 := .mul ⟨(96580617246883897671/2361183241434822606848:ℚ),(24367177551225689211/590295810358705651712:ℚ)⟩ node2211 node2211
def node2216 : BoxExpr 3 := .mul ⟨(19943897461481524869/590295810358705651712:ℚ),(161018309258499354307/4722366482869645213696:ℚ)⟩ node2215 node340
def node2217 : BoxExpr 3 := .add ⟨(5428326891469532626733/2361183241434822606848:ℚ),(10880853117461487289441/4722366482869645213696:ℚ)⟩ node2214 node2216
def node2218 : BoxExpr 3 := .neg ⟨(-10880853117461487289441/4722366482869645213696:ℚ),(-5428326891469532626733/2361183241434822606848:ℚ)⟩ node2217
def node2219 : BoxExpr 3 := .add ⟨(-29347102423263759293/1180591620717411303424:ℚ),(116094703252243632861/4722366482869645213696:ℚ)⟩ node2204 node2218
def node2220 : BoxExpr 3 := .var 2
def node2221 : BoxExpr 3 := .mul ⟨(-429620018102705313547/4722366482869645213696:ℚ),(-214810009051352656773/2361183241434822606848:ℚ)⟩ node51 node2220
def node2222 : BoxExpr 3 := .add ⟨(1931563223332117293301/4722366482869645213696:ℚ),(965781611666058646651/2361183241434822606848:ℚ)⟩ node2221 node301
def node2223 : BoxExpr 3 := .mul ⟨(2033102813683305311437/2361183241434822606848:ℚ),(4066205627366610622887/4722366482869645213696:ℚ)⟩ node68 node2222
def node2224 : BoxExpr 3 := .mul ⟨(4838528482225332028247/4722366482869645213696:ℚ),(4838528482225332028265/4722366482869645213696:ℚ)⟩ node2223 node349
def node2225 : BoxExpr 3 := .add ⟨(-131980689239868807579/4722366482869645213696:ℚ),(-131980689239868807577/4722366482869645213696:ℚ)⟩ node2220 node351
def node2226 : BoxExpr 3 := .mul ⟨(2853071103619086107/2361183241434822606848:ℚ),(5706142207238172215/4722366482869645213696:ℚ)⟩ node2225 node308
def node2227 : BoxExpr 3 := .mul ⟨(6224501461727825267/4722366482869645213696:ℚ),(6224501461727825269/4722366482869645213696:ℚ)⟩ node2226 node69
def node2228 : BoxExpr 3 := .add ⟨(2422376491843529926757/2361183241434822606848:ℚ),(2422376491843529926767/2361183241434822606848:ℚ)⟩ node2224 node2227
def node2229 : BoxExpr 3 := .add ⟨(7811877748301660902705/2361183241434822606848:ℚ),(15623755496603321805483/4722366482869645213696:ℚ)⟩ node2228 node358
def node2230 : BoxExpr 3 := .add ⟨(10868870861823038714593/4722366482869645213696:ℚ),(10868870861823038714671/4722366482869645213696:ℚ)⟩ node2229 node361
def node2231 : BoxExpr 3 := .add ⟨(10868856694723590105657/4722366482869645213696:ℚ),(1358607086840448763217/590295810358705651712:ℚ)⟩ node2230 node325
def node2232 : BoxExpr 3 := .mul ⟨(122431663321333754757/2361183241434822606848:ℚ),(244863326642667509515/4722366482869645213696:ℚ)⟩ node2220 node2220
def node2233 : BoxExpr 3 := .neg ⟨(-244863326642667509515/4722366482869645213696:ℚ),(-122431663321333754757/2361183241434822606848:ℚ)⟩ node2232
def node2234 : BoxExpr 3 := .add ⟨(4477503156226977704181/4722366482869645213696:ℚ),(2238751578113488852091/2361183241434822606848:ℚ)⟩ node12 node2233
def node2235 : BoxExpr 3 := .sqrt ⟨(2299152606500345394347/2361183241434822606848:ℚ),(4598305213000690788695/4722366482869645213696:ℚ)⟩ node2234
def node2236 : BoxExpr 3 := .mul ⟨(5695929304915135462351/2361183241434822606848:ℚ),(5695929304915135462357/2361183241434822606848:ℚ)⟩ node50 node2235
def node2237 : BoxExpr 3 := .neg ⟨(1075329887346806174515/4722366482869645213696:ℚ),(268832471836701543629/1180591620717411303424:ℚ)⟩ node2220
def node2238 : BoxExpr 3 := .add ⟨(239317681318766261043/1180591620717411303424:ℚ),(478635362637532522087/2361183241434822606848:ℚ)⟩ node332 node2237
def node2239 : BoxExpr 3 := .mul ⟨(341745648923198220769/2361183241434822606848:ℚ),(683491297846396441541/4722366482869645213696:ℚ)⟩ node2238 node335
def node2240 : BoxExpr 3 := .neg ⟨(-683491297846396441541/4722366482869645213696:ℚ),(-341745648923198220769/2361183241434822606848:ℚ)⟩ node2239
def node2241 : BoxExpr 3 := .add ⟨(10708367311983874483161/4722366482869645213696:ℚ),(1338545913997984310397/590295810358705651712:ℚ)⟩ node2236 node2240
def node2242 : BoxExpr 3 := .mul ⟨(97024155663560364523/2361183241434822606848:ℚ),(24256038915890091131/590295810358705651712:ℚ)⟩ node2238 node2238
def node2243 : BoxExpr 3 := .mul ⟨(160283905156201722191/4722366482869645213696:ℚ),(80141952578100861097/2361183241434822606848:ℚ)⟩ node2242 node340
def node2244 : BoxExpr 3 := .add ⟨(1358581402142509525669/590295810358705651712:ℚ),(5434325608570038102685/2361183241434822606848:ℚ)⟩ node2241 node2243
def node2245 : BoxExpr 3 := .neg ⟨(-5434325608570038102685/2361183241434822606848:ℚ),(-1358581402142509525669/590295810358705651712:ℚ)⟩ node2244
def node2246 : BoxExpr 3 := .add ⟨(205477583513900287/4722366482869645213696:ℚ),(6421174484809387/147573952589676412928:ℚ)⟩ node2231 node2245
def node2247 : BoxExpr 3 := .mul ⟨(547642056045221203431/2361183241434822606848:ℚ),(1095284112090442406867/4722366482869645213696:ℚ)⟩ node78 node2222
def node2248 : BoxExpr 3 := .mul ⟨(1303319078801884240465/4722366482869645213696:ℚ),(162914884850235530059/590295810358705651712:ℚ)⟩ node2247 node349
def node2249 : BoxExpr 3 := .add ⟨(2591275208041627614029/2361183241434822606848:ℚ),(5182550416083255228485/4722366482869645213696:ℚ)⟩ node2248 node385
def node2250 : BoxExpr 3 := .add ⟨(88396386111578168103/147573952589676412928:ℚ),(2828684355570501379725/4722366482869645213696:ℚ)⟩ node2249 node387
def node2251 : BoxExpr 3 := .mul ⟨(1422157320093303668881/2361183241434822606848:ℚ),(1422157320093303668885/2361183241434822606848:ℚ)⟩ node77 node2235
def node2252 : BoxExpr 3 := .neg ⟨(-1422157320093303668885/2361183241434822606848:ℚ),(-1422157320093303668881/2361183241434822606848:ℚ)⟩ node2251
def node2253 : BoxExpr 3 := .add ⟨(-7815142308052979237/2361183241434822606848:ℚ),(-15630284616105958037/4722366482869645213696:ℚ)⟩ node2250 node2252
def node2254 : BoxExpr 3 := .mul ⟨(-1842215961817811607545/4722366482869645213696:ℚ),(-1842215961817811607535/4722366482869645213696:ℚ)⟩ node98 node2222
def node2255 : BoxExpr 3 := .mul ⟨(-1131858482908500473043/2361183241434822606848:ℚ),(-1131858482908500473039/2361183241434822606848:ℚ)⟩ node68 node2220
def node2256 : BoxExpr 3 := .add ⟨(-4105932927634812553631/4722366482869645213696:ℚ),(-4105932927634812553613/4722366482869645213696:ℚ)⟩ node2254 node2255
def node2257 : BoxExpr 3 := .mul ⟨(-4885801466300685169731/4722366482869645213696:ℚ),(-4885801466300685169707/4722366482869645213696:ℚ)⟩ node2256 node349
def node2258 : BoxExpr 3 := .mul ⟨(4600553175403686262163/4722366482869645213696:ℚ),(4600553175403686262187/4722366482869645213696:ℚ)⟩ node2223 node399
def node2259 : BoxExpr 3 := .add ⟨(-17828018181062431723/295147905179352825856:ℚ),(-2228502272632803965/36893488147419103232:ℚ)⟩ node2257 node2258
def node2260 : BoxExpr 3 := .mul ⟨(1479589821071308377/2361183241434822606848:ℚ),(739794910535654189/1180591620717411303424:ℚ)⟩ node2226 node103
def node2261 : BoxExpr 3 := .add ⟨(-108399448823623586779/4722366482869645213696:ℚ),(-108399448823623586775/4722366482869645213696:ℚ)⟩ node403 node2260
def node2262 : BoxExpr 3 := .add ⟨(-393647739720622494347/4722366482869645213696:ℚ),(-393647739720622494295/4722366482869645213696:ℚ)⟩ node2259 node2261
def node2263 : BoxExpr 3 := .add ⟨(-71730505095953664073/4722366482869645213696:ℚ),(-71730505095953663905/4722366482869645213696:ℚ)⟩ node2262 node409
def node2264 : BoxExpr 3 := .add ⟨(-268832471836701543629/590295810358705651712:ℚ),(-1075329887346806174515/2361183241434822606848:ℚ)⟩ node2220 node2220
def node2265 : BoxExpr 3 := .neg ⟨(1075329887346806174515/2361183241434822606848:ℚ),(268832471836701543629/590295810358705651712:ℚ)⟩ node2264
def node2266 : BoxExpr 3 := .mul ⟨(2299152606500345394347/1180591620717411303424:ℚ),(4598305213000690788695/2361183241434822606848:ℚ)⟩ node86 node2235
def node2267 : BoxExpr 3 := .inv ⟨(2424887449345489212947/4722366482869645213696:ℚ),(606221862336372303237/1180591620717411303424:ℚ)⟩ node2266
def node2268 : BoxExpr 3 := .mul ⟨(1104342052736590717243/4722366482869645213696:ℚ),(552171026368295358623/2361183241434822606848:ℚ)⟩ node2265 node2267
def node2269 : BoxExpr 3 := .mul ⟨(2735901150296931396681/4722366482869645213696:ℚ),(683975287574232849173/1180591620717411303424:ℚ)⟩ node50 node2268
def node2270 : BoxExpr 3 := .add ⟨(6107670819065858079259/4722366482869645213696:ℚ),(6107670819065858079271/4722366482869645213696:ℚ)⟩ node2269 node335
def node2271 : BoxExpr 3 := .mul ⟨(-478635362637532522087/2361183241434822606848:ℚ),(-239317681318766261043/1180591620717411303424:ℚ)⟩ node422 node2238
def node2272 : BoxExpr 3 := .mul ⟨(-478635362637532522087/2361183241434822606848:ℚ),(-239317681318766261043/1180591620717411303424:ℚ)⟩ node2238 node422
def node2273 : BoxExpr 3 := .add ⟨(-478635362637532522087/1180591620717411303424:ℚ),(-239317681318766261043/590295810358705651712:ℚ)⟩ node2271 node2272
def node2274 : BoxExpr 3 := .mul ⟨(-98838202384650465811/295147905179352825856:ℚ),(-1581411238154407452971/4722366482869645213696:ℚ)⟩ node2273 node340
def node2275 : BoxExpr 3 := .add ⟨(4526259580911450626283/4722366482869645213696:ℚ),(1131564895227862656575/1180591620717411303424:ℚ)⟩ node2270 node2274
def node2276 : BoxExpr 3 := .neg ⟨(-1131564895227862656575/1180591620717411303424:ℚ),(-4526259580911450626283/4722366482869645213696:ℚ)⟩ node2275
def node2277 : BoxExpr 3 := .add ⟨(-22833879031816212701/4722366482869645213696:ℚ),(-22833879031816212665/4722366482869645213696:ℚ)⟩ node414 node2276
def node2278 : BoxExpr 3 := .mul ⟨(8689921095803114847959/4722366482869645213696:ℚ),(4366891278314017148763/2361183241434822606848:ℚ)⟩ node112 node2195
def node2279 : BoxExpr 3 := .mul ⟨(10320881140924260632867/4722366482869645213696:ℚ),(650781327482684308089/295147905179352825856:ℚ)⟩ node2278 node304
def node2280 : BoxExpr 3 := .add ⟨(10823546029893522397795/2361183241434822606848:ℚ),(44738850852383767343705/4722366482869645213696:ℚ)⟩ node2279 node448
def node2281 : BoxExpr 3 := .mul ⟨(22621138581398999169465/4722366482869645213696:ℚ),(22626179299535931614343/4722366482869645213696:ℚ)⟩ node111 node2208
def node2282 : BoxExpr 3 := .neg ⟨(-22626179299535931614343/4722366482869645213696:ℚ),(-22621138581398999169465/4722366482869645213696:ℚ)⟩ node2281
def node2283 : BoxExpr 3 := .add ⟨(-979087239748886818753/4722366482869645213696:ℚ),(691178508468274005445/147573952589676412928:ℚ)⟩ node2280 node2282
def node2284 : BoxExpr 3 := .mul ⟨(-268575740878002516637/2361183241434822606848:ℚ),(-504465987675434622125/4722366482869645213696:ℚ)⟩ node131 node2195
def node2285 : BoxExpr 3 := .mul ⟨(-19567994879181701733/147573952589676412928:ℚ),(-593431833008969055163/4722366482869645213696:ℚ)⟩ node118 node2193
def node2286 : BoxExpr 3 := .add ⟨(-581663658944909744365/2361183241434822606848:ℚ),(-137237227585550459661/590295810358705651712:ℚ)⟩ node2284 node2285
def node2287 : BoxExpr 3 := .mul ⟨(-346732560067536182537/1180591620717411303424:ℚ),(-81497236764583945893/295147905179352825856:ℚ)⟩ node2286 node304
def node2288 : BoxExpr 3 := .mul ⟨(1066453196941899020453/4722366482869645213696:ℚ),(70264918899405020337/295147905179352825856:ℚ)⟩ node118 node2195
def node2289 : BoxExpr 3 := .mul ⟨(1196015906999722224543/4722366482869645213696:ℚ),(1283232464905378795629/4722366482869645213696:ℚ)⟩ node2288 node461
def node2290 : BoxExpr 3 := .add ⟨(-190914333270422505605/4722366482869645213696:ℚ),(-20723323327964338659/4722366482869645213696:ℚ)⟩ node2287 node2289
def node2291 : BoxExpr 3 := .add ⟨(-737053764541223336891/1180591620717411303424:ℚ),(1392850557243695434245/4722366482869645213696:ℚ)⟩ node2290 node476
def node2292 : BoxExpr 3 := .add ⟨(-538760219102779591885/1180591620717411303424:ℚ),(-268284834122013291315/590295810358705651712:ℚ)⟩ node2193 node2193
def node2293 : BoxExpr 3 := .neg ⟨(268284834122013291315/590295810358705651712:ℚ),(538760219102779591885/1180591620717411303424:ℚ)⟩ node2292
def node2294 : BoxExpr 3 := .mul ⟨(4597792394593292514119/2361183241434822606848:ℚ),(1149704232699996525119/590295810358705651712:ℚ)⟩ node86 node2208
def node2295 : BoxExpr 3 := .inv ⟨(2424617628196313343841/4722366482869645213696:ℚ),(2425157911083029978271/4722366482869645213696:ℚ)⟩ node2294
def node2296 : BoxExpr 3 := .mul ⟨(275492442422501032769/1180591620717411303424:ℚ),(1106715128758886629733/4722366482869645213696:ℚ)⟩ node2293 node2295
def node2297 : BoxExpr 3 := .mul ⟨(332683111885969389647/2361183241434822606848:ℚ),(350450844364775004561/2361183241434822606848:ℚ)⟩ node117 node2296
def node2298 : BoxExpr 3 := .neg ⟨(-350450844364775004561/2361183241434822606848:ℚ),(-332683111885969389647/2361183241434822606848:ℚ)⟩ node2297
def node2299 : BoxExpr 3 := .add ⟨(532028903376813966825/4722366482869645213696:ℚ),(5065069710604077519/36893488147419103232:ℚ)⟩ node479 node2298
def node2300 : BoxExpr 3 := .add ⟨(-2948215058164893347563/4722366482869645213696:ℚ),(1392850557243695434245/4722366482869645213696:ℚ)⟩ node2290 node492
def node2301 : BoxExpr 3 := .mul ⟨(-1987622397396152401113/4722366482869645213696:ℚ),(-1936733153030394375221/4722366482869645213696:ℚ)⟩ node175 node2195
def node2302 : BoxExpr 3 := .mul ⟨(505516692465567650659/2361183241434822606848:ℚ),(130030792119413024779/590295810358705651712:ℚ)⟩ node148 node2193
def node2303 : BoxExpr 3 := .add ⟨(-976589012465017099795/4722366482869645213696:ℚ),(-896486816075090176989/4722366482869645213696:ℚ)⟩ node2301 node2302
def node2304 : BoxExpr 3 := .add ⟨(34444372466118201523/4722366482869645213696:ℚ),(143759520880214021243/4722366482869645213696:ℚ)⟩ node2303 node2302
def node2305 : BoxExpr 3 := .mul ⟨(40909033612309866467/4722366482869645213696:ℚ),(85695755514958226495/2361183241434822606848:ℚ)⟩ node2304 node304
def node2306 : BoxExpr 3 := .mul ⟨(-1867662602961193312141/4722366482869645213696:ℚ),(-1816922729115717586937/4722366482869645213696:ℚ)⟩ node148 node2195
def node2307 : BoxExpr 3 := .mul ⟨(-569057279648263032389/1180591620717411303424:ℚ),(-2251279609358415296989/4722366482869645213696:ℚ)⟩ node36 node2193
def node2308 : BoxExpr 3 := .add ⟨(-4143891721554245441697/4722366482869645213696:ℚ),(-2034101169237066441963/2361183241434822606848:ℚ)⟩ node2306 node2307
def node2309 : BoxExpr 3 := .mul ⟨(-4729935357005794741443/4722366482869645213696:ℚ),(-2281222806430207339743/2361183241434822606848:ℚ)⟩ node2308 node461
def node2310 : BoxExpr 3 := .add ⟨(-146532072606046402343/147573952589676412928:ℚ),(-68610220341101534789/73786976294838206464:ℚ)⟩ node2305 node2309
def node2311 : BoxExpr 3 := .mul ⟨(19950120650382757122951/4722366482869645213696:ℚ),(10291784038236122882363/2361183241434822606848:ℚ)⟩ node2196 node514
def node2312 : BoxExpr 3 := .add ⟨(3805046323344240595377/1180591620717411303424:ℚ),(2002640307951478885655/590295810358705651712:ℚ)⟩ node2309 node2311
def node2313 : BoxExpr 3 := .add ⟨(2632789742495869376633/1180591620717411303424:ℚ),(1453758545222666607343/590295810358705651712:ℚ)⟩ node2310 node2312
def node2314 : BoxExpr 3 := .mul ⟨(10934636446274348509/4722366482869645213696:ℚ),(6165164030283763865/2361183241434822606848:ℚ)⟩ node2199 node189
def node2315 : BoxExpr 3 := .add ⟨(-42423709232826251995/4722366482869645213696:ℚ),(-10048986002765814551/1180591620717411303424:ℚ)⟩ node518 node2314
def node2316 : BoxExpr 3 := .add ⟨(-95782054911926852499/4722366482869645213696:ℚ),(-46361108041347022069/2361183241434822606848:ℚ)⟩ node518 node2315
def node2317 : BoxExpr 3 := .add ⟨(10435376915071550654033/4722366482869645213696:ℚ),(5768673072849319407303/2361183241434822606848:ℚ)⟩ node2313 node2316
def node2318 : BoxExpr 3 := .add ⟨(5384777548359530506389/1180591620717411303424:ℚ),(28130817185026085289149/4722366482869645213696:ℚ)⟩ node2317 node527
def node2319 : BoxExpr 3 := .mul ⟨(-2425157911083029978271/2361183241434822606848:ℚ),(-2424617628196313343841/2361183241434822606848:ℚ)⟩ node6 node2295
def node2320 : BoxExpr 3 := .mul ⟨(275492442422501032769/590295810358705651712:ℚ),(1106715128758886629733/2361183241434822606848:ℚ)⟩ node86 node2296
def node2321 : BoxExpr 3 := .mul ⟨(1119126129900338817269/295147905179352825856:ℚ),(17913999042413073153403/4722366482869645213696:ℚ)⟩ node2294 node2294
def node2322 : BoxExpr 3 := .inv ⟨(1244878105984683652451/4722366482869645213696:ℚ),(622716482829457868487/2361183241434822606848:ℚ)⟩ node2321
def node2323 : BoxExpr 3 := .mul ⟨(290493769325259216877/2361183241434822606848:ℚ),(145937371649329511583/1180591620717411303424:ℚ)⟩ node2320 node2322
def node2324 : BoxExpr 3 := .neg ⟨(-145937371649329511583/1180591620717411303424:ℚ),(-290493769325259216877/2361183241434822606848:ℚ)⟩ node2323
def node2325 : BoxExpr 3 := .mul ⟨(-66598177511456719495/1180591620717411303424:ℚ),(-264054297351514920965/4722366482869645213696:ℚ)⟩ node2293 node2324
def node2326 : BoxExpr 3 := .add ⟨(-2558354266105943417261/2361183241434822606848:ℚ),(-5113289553744141608647/4722366482869645213696:ℚ)⟩ node2319 node2325
def node2327 : BoxExpr 3 := .mul ⟨(-1585720144314832968639/590295810358705651712:ℚ),(-6329153686427168221911/2361183241434822606848:ℚ)⟩ node11 node2326
def node2328 : BoxExpr 3 := .add ⟨(-4884411724818009856087/4722366482869645213696:ℚ),(-1214239485788420637699/1180591620717411303424:ℚ)⟩ node2327 node546
def node2329 : BoxExpr 3 := .neg ⟨(1214239485788420637699/1180591620717411303424:ℚ),(4884411724818009856087/4722366482869645213696:ℚ)⟩ node2328
def cert_iv13 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-9327/40960:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/40960:ℚ)],
    whole := node2219, centerValue := node2246, gradient := ![node2253, node2263, node2277],
    hessian := ![![node2283, node2291, node2299], ![node2300, node2318, node536], ![node2299, node536, node2329]] }
def node2330 : BoxExpr 3 := .var 2
def node2331 : BoxExpr 3 := .mul ⟨(-107722779824242232289/1180591620717411303424:ℚ),(-423115376443036777683/4722366482869645213696:ℚ)⟩ node13 node2330
def node2332 : BoxExpr 3 := .add ⟨(482573030534463419423/1180591620717411303424:ℚ),(1938067864991785829165/4722366482869645213696:ℚ)⟩ node2331 node301
def node2333 : BoxExpr 3 := .mul ⟨(4049452989856468504827/4722366482869645213696:ℚ),(255881834794382644467/295147905179352825856:ℚ)⟩ node36 node2332
def node2334 : BoxExpr 3 := .mul ⟨(2404735470742869245679/2361183241434822606848:ℚ),(4881037337018860245285/4722366482869645213696:ℚ)⟩ node2333 node304
def node2335 : BoxExpr 3 := .add ⟨(-67256252431992721769/2361183241434822606848:ℚ),(-116305568463234116091/4722366482869645213696:ℚ)⟩ node2330 node306
def node2336 : BoxExpr 3 := .mul ⟨(2514216727337757479/2361183241434822606848:ℚ),(5815604432938936803/4722366482869645213696:ℚ)⟩ node2335 node308
def node2337 : BoxExpr 3 := .mul ⟨(685004133087730929/590295810358705651712:ℚ),(6349963141010713145/4722366482869645213696:ℚ)⟩ node2336 node37
def node2338 : BoxExpr 3 := .add ⟨(2407475487275220169395/2361183241434822606848:ℚ),(2443693650079935479215/2361183241434822606848:ℚ)⟩ node2334 node2337
def node2339 : BoxExpr 3 := .add ⟨(15529395229689826698597/4722366482869645213696:ℚ),(1966143912127457681959/590295810358705651712:ℚ)⟩ node2338 node316
def node2340 : BoxExpr 3 := .add ⟨(10767448996728005346233/4722366482869645213696:ℚ),(10981328260420916626407/4722366482869645213696:ℚ)⟩ node2339 node323
def node2341 : BoxExpr 3 := .add ⟨(10767434829628556737297/4722366482869645213696:ℚ),(171583032708147937773/73786976294838206464:ℚ)⟩ node2340 node325
def node2342 : BoxExpr 3 := .mul ⟨(239900627254533098045/4722366482869645213696:ℚ),(60966680566594231337/1180591620717411303424:ℚ)⟩ node2330 node2330
def node2343 : BoxExpr 3 := .neg ⟨(-60966680566594231337/1180591620717411303424:ℚ),(-239900627254533098045/4722366482869645213696:ℚ)⟩ node2342
def node2344 : BoxExpr 3 := .add ⟨(1119624940150817072087/1180591620717411303424:ℚ),(4482465855615112115651/4722366482869645213696:ℚ)⟩ node12 node2343
def node2345 : BoxExpr 3 := .sqrt ⟨(2299408465399993050237/2361183241434822606848:ℚ),(2300426401624512520481/2361183241434822606848:ℚ)⟩ node2344
def node2346 : BoxExpr 3 := .mul ⟨(5692347132867422627525/2361183241434822606848:ℚ),(11406809553774643196485/4722366482869645213696:ℚ)⟩ node11 node2345
def node2347 : BoxExpr 3 := .neg ⟨(1064377133053041128243/4722366482869645213696:ℚ),(1073139336488053165261/4722366482869645213696:ℚ)⟩ node2330
def node2348 : BoxExpr 3 := .add ⟨(236579492745324999475/1180591620717411303424:ℚ),(955080174416312034919/4722366482869645213696:ℚ)⟩ node332 node2347
def node2349 : BoxExpr 3 := .mul ⟨(168917757820162049625/1180591620717411303424:ℚ),(681927244533246792933/4722366482869645213696:ℚ)⟩ node2348 node335
def node2350 : BoxExpr 3 := .neg ⟨(-681927244533246792933/4722366482869645213696:ℚ),(-168917757820162049625/1180591620717411303424:ℚ)⟩ node2349
def node2351 : BoxExpr 3 := .add ⟨(10702767021201598462117/4722366482869645213696:ℚ),(10731138522493994997985/4722366482869645213696:ℚ)⟩ node2346 node2350
def node2352 : BoxExpr 3 := .mul ⟨(189633249653674569891/4722366482869645213696:ℚ),(12072577155860487209/295147905179352825856:ℚ)⟩ node2348 node2348
def node2353 : BoxExpr 3 := .mul ⟨(156637064213935194729/4722366482869645213696:ℚ),(159551179691852198955/4722366482869645213696:ℚ)⟩ node2352 node340
def node2354 : BoxExpr 3 := .add ⟨(5429702042707766828423/2361183241434822606848:ℚ),(2722672425546461799235/1180591620717411303424:ℚ)⟩ node2351 node2353
def node2355 : BoxExpr 3 := .neg ⟨(-2722672425546461799235/1180591620717411303424:ℚ),(-5429702042707766828423/2361183241434822606848:ℚ)⟩ node2354
def node2356 : BoxExpr 3 := .add ⟨(-123254872557290459643/4722366482869645213696:ℚ),(60955003952967180313/2361183241434822606848:ℚ)⟩ node2341 node2355
def node2357 : BoxExpr 3 := .var 2
def node2358 : BoxExpr 3 := .mul ⟨(-426994485666567841383/4722366482869645213696:ℚ),(-213497242833283920691/2361183241434822606848:ℚ)⟩ node51 node2357
def node2359 : BoxExpr 3 := .add ⟨(1934188755768254765465/4722366482869645213696:ℚ),(967094377884127382733/2361183241434822606848:ℚ)⟩ node2358 node301
def node2360 : BoxExpr 3 := .mul ⟨(508966591676365718767/590295810358705651712:ℚ),(4071732733410925750149/4722366482869645213696:ℚ)⟩ node68 node2359
def node2361 : BoxExpr 3 := .mul ⟨(2422552695075706010569/2361183241434822606848:ℚ),(1211276347537853005289/1180591620717411303424:ℚ)⟩ node2360 node349
def node2362 : BoxExpr 3 := .add ⟨(-125409036663609779815/4722366482869645213696:ℚ),(-62704518331804889907/2361183241434822606848:ℚ)⟩ node2357 node351
def node2363 : BoxExpr 3 := .mul ⟨(677752367975903235/590295810358705651712:ℚ),(5422018943807225881/4722366482869645213696:ℚ)⟩ node2362 node308
def node2364 : BoxExpr 3 := .mul ⟨(2957283889493095407/2361183241434822606848:ℚ),(184830243093318463/147573952589676412928:ℚ)⟩ node2363 node69
def node2365 : BoxExpr 3 := .add ⟨(303188747370649888247/295147905179352825856:ℚ),(1212754989482599552993/1180591620717411303424:ℚ)⟩ node2361 node2364
def node2366 : BoxExpr 3 := .add ⟨(1953752808855832520481/590295810358705651712:ℚ),(15630022470846660163921/4722366482869645213696:ℚ)⟩ node2365 node358
def node2367 : BoxExpr 3 := .add ⟨(10875137836066377073031/4722366482869645213696:ℚ),(10875137836066377073109/4722366482869645213696:ℚ)⟩ node2366 node361
def node2368 : BoxExpr 3 := .add ⟨(10875123668966928464095/4722366482869645213696:ℚ),(5437561834483464232087/2361183241434822606848:ℚ)⟩ node2367 node325
def node2369 : BoxExpr 3 := .mul ⟨(859329/16777216:ℚ),(859329/16777216:ℚ)⟩ node2357 node2357
def node2370 : BoxExpr 3 := .neg ⟨(-859329/16777216:ℚ),(-859329/16777216:ℚ)⟩ node2369
def node2371 : BoxExpr 3 := .add ⟨(15917887/16777216:ℚ),(15917887/16777216:ℚ)⟩ node12 node2370
def node2372 : BoxExpr 3 := .sqrt ⟨(2299918533021374605651/2361183241434822606848:ℚ),(4599837066042749211303/4722366482869645213696:ℚ)⟩ node2371
def node2373 : BoxExpr 3 := .mul ⟨(11395653628311608368745/4722366482869645213696:ℚ),(2848913407077902092189/1180591620717411303424:ℚ)⟩ node50 node2372
def node2374 : BoxExpr 3 := .neg ⟨(927/4096:ℚ),(927/4096:ℚ)⟩ node2357
def node2375 : BoxExpr 3 := .add ⟨(950699072698806016409/4722366482869645213696:ℚ),(475349536349403008205/2361183241434822606848:ℚ)⟩ node332 node2374
def node2376 : BoxExpr 3 := .mul ⟨(678799137906947495715/4722366482869645213696:ℚ),(678799137906947495717/4722366482869645213696:ℚ)⟩ node2375 node335
def node2377 : BoxExpr 3 := .neg ⟨(-678799137906947495717/4722366482869645213696:ℚ),(-678799137906947495715/4722366482869645213696:ℚ)⟩ node2376
def node2378 : BoxExpr 3 := .add ⟨(2679213622601165218257/1180591620717411303424:ℚ),(10716854490404660873041/4722366482869645213696:ℚ)⟩ node2373 node2377
def node2379 : BoxExpr 3 := .mul ⟨(23924147196882185093/590295810358705651712:ℚ),(95696588787528740373/2361183241434822606848:ℚ)⟩ node2375 node2375
def node2380 : BoxExpr 3 := .mul ⟨(79045382338498739547/2361183241434822606848:ℚ),(158090764676997479097/4722366482869645213696:ℚ)⟩ node2379 node340
def node2381 : BoxExpr 3 := .add ⟨(5437472627540829176061/2361183241434822606848:ℚ),(5437472627540829176069/2361183241434822606848:ℚ)⟩ node2378 node2380
def node2382 : BoxExpr 3 := .neg ⟨(-5437472627540829176069/2361183241434822606848:ℚ),(-5437472627540829176061/2361183241434822606848:ℚ)⟩ node2381
def node2383 : BoxExpr 3 := .add ⟨(178413885270111957/4722366482869645213696:ℚ),(44603471317528013/1180591620717411303424:ℚ)⟩ node2368 node2382
def node2384 : BoxExpr 3 := .mul ⟨(1096772908278080854367/4722366482869645213696:ℚ),(274193227069520213593/1180591620717411303424:ℚ)⟩ node78 node2359
def node2385 : BoxExpr 3 := .mul ⟨(1305090652455128717743/4722366482869645213696:ℚ),(1305090652455128717751/4722366482869645213696:ℚ)⟩ node2384 node349
def node2386 : BoxExpr 3 := .add ⟨(648040248717062463167/590295810358705651712:ℚ),(1296080497434124926441/1180591620717411303424:ℚ)⟩ node2385 node385
def node2387 : BoxExpr 3 := .add ⟨(1415227964611872928287/2361183241434822606848:ℚ),(707613982305936464251/1180591620717411303424:ℚ)⟩ node2386 node387
def node2388 : BoxExpr 3 := .mul ⟨(2845262178862774918991/4722366482869645213696:ℚ),(2845262178862774918999/4722366482869645213696:ℚ)⟩ node77 node2372
def node2389 : BoxExpr 3 := .neg ⟨(-2845262178862774918999/4722366482869645213696:ℚ),(-2845262178862774918991/4722366482869645213696:ℚ)⟩ node2388
def node2390 : BoxExpr 3 := .add ⟨(-14806249639029062425/4722366482869645213696:ℚ),(-14806249639029061987/4722366482869645213696:ℚ)⟩ node2387 node2389
def node2391 : BoxExpr 3 := .mul ⟨(-1844720046438857017409/4722366482869645213696:ℚ),(-1844720046438857017399/4722366482869645213696:ℚ)⟩ node98 node2359
def node2392 : BoxExpr 3 := .mul ⟨(-2249882735405124774333/4722366482869645213696:ℚ),(-2249882735405124774327/4722366482869645213696:ℚ)⟩ node68 node2357
def node2393 : BoxExpr 3 := .add ⟨(-2047301390921990895871/2361183241434822606848:ℚ),(-2047301390921990895863/2361183241434822606848:ℚ)⟩ node2391 node2392
def node2394 : BoxExpr 3 := .mul ⟨(-1218079826682418507795/1180591620717411303424:ℚ),(-4872319306729674031159/4722366482869645213696:ℚ)⟩ node2393 node349
def node2395 : BoxExpr 3 := .mul ⟨(1151701652150599746767/1180591620717411303424:ℚ),(1151701652150599746773/1180591620717411303424:ℚ)⟩ node2360 node399
def node2396 : BoxExpr 3 := .add ⟨(-16594543632954690257/295147905179352825856:ℚ),(-265512698127275044067/4722366482869645213696:ℚ)⟩ node2394 node2395
def node2397 : BoxExpr 3 := .mul ⟨(1405917298860288873/2361183241434822606848:ℚ),(2811834597720577747/4722366482869645213696:ℚ)⟩ node2363 node103
def node2398 : BoxExpr 3 := .add ⟨(-108546793868045625787/4722366482869645213696:ℚ),(-13568349233505703223/590295810358705651712:ℚ)⟩ node403 node2397
def node2399 : BoxExpr 3 := .add ⟨(-374059491995320669899/4722366482869645213696:ℚ),(-374059491995320669851/4722366482869645213696:ℚ)⟩ node2396 node2398
def node2400 : BoxExpr 3 := .add ⟨(-52142257370651839625/4722366482869645213696:ℚ),(-52142257370651839461/4722366482869645213696:ℚ)⟩ node2399 node409
def node2401 : BoxExpr 3 := .add ⟨(-927/2048:ℚ),(-927/2048:ℚ)⟩ node2357 node2357
def node2402 : BoxExpr 3 := .neg ⟨(927/2048:ℚ),(927/2048:ℚ)⟩ node2401
def node2403 : BoxExpr 3 := .mul ⟨(2299918533021374605651/1180591620717411303424:ℚ),(4599837066042749211303/2361183241434822606848:ℚ)⟩ node86 node2372
def node2404 : BoxExpr 3 := .inv ⟨(2424079905260210376913/4722366482869645213696:ℚ),(1212039952630105188457/2361183241434822606848:ℚ)⟩ node2403
def node2405 : BoxExpr 3 := .mul ⟨(274306893576198122485/1180591620717411303424:ℚ),(548613787152396244971/2361183241434822606848:ℚ)⟩ node2402 node2404
def node2406 : BoxExpr 3 := .mul ⟨(1359137857350983534537/2361183241434822606848:ℚ),(1359137857350983534541/2361183241434822606848:ℚ)⟩ node50 node2405
def node2407 : BoxExpr 3 := .add ⟨(1522511345867723437913/1180591620717411303424:ℚ),(6090045383470893751661/4722366482869645213696:ℚ)⟩ node2406 node335
def node2408 : BoxExpr 3 := .mul ⟨(-475349536349403008205/2361183241434822606848:ℚ),(-950699072698806016409/4722366482869645213696:ℚ)⟩ node422 node2375
def node2409 : BoxExpr 3 := .mul ⟨(-475349536349403008205/2361183241434822606848:ℚ),(-950699072698806016409/4722366482869645213696:ℚ)⟩ node2375 node422
def node2410 : BoxExpr 3 := .add ⟨(-475349536349403008205/1180591620717411303424:ℚ),(-950699072698806016409/2361183241434822606848:ℚ)⟩ node2408 node2409
def node2411 : BoxExpr 3 := .mul ⟨(-785277434049213769555/2361183241434822606848:ℚ),(-1570554868098427539107/4722366482869645213696:ℚ)⟩ node2410 node340
def node2412 : BoxExpr 3 := .add ⟨(2259745257686233106271/2361183241434822606848:ℚ),(2259745257686233106277/2361183241434822606848:ℚ)⟩ node2407 node2411
def node2413 : BoxExpr 3 := .neg ⟨(-2259745257686233106277/2361183241434822606848:ℚ),(-2259745257686233106271/2361183241434822606848:ℚ)⟩ node2412
def node2414 : BoxExpr 3 := .add ⟨(-16064813492831798955/4722366482869645213696:ℚ),(-4016203373207949731/1180591620717411303424:ℚ)⟩ node414 node2413
def node2415 : BoxExpr 3 := .mul ⟨(4348923816688427083807/2361183241434822606848:ℚ),(8749507577690028808713/4722366482869645213696:ℚ)⟩ node112 node2332
def node2416 : BoxExpr 3 := .mul ⟨(5165147681795807678675/2361183241434822606848:ℚ),(10431248764090661530213/4722366482869645213696:ℚ)⟩ node2415 node304
def node2417 : BoxExpr 3 := .add ⟨(21656506282454399520073/4722366482869645213696:ℚ),(22378799188375739972247/2361183241434822606848:ℚ)⟩ node2416 node448
def node2418 : BoxExpr 3 := .mul ⟨(22626179299535931614331/4722366482869645213696:ℚ),(11318097895992601600767/2361183241434822606848:ℚ)⟩ node111 node2345
def node2419 : BoxExpr 3 := .neg ⟨(-11318097895992601600767/2361183241434822606848:ℚ),(-22626179299535931614331/4722366482869645213696:ℚ)⟩ node2418
def node2420 : BoxExpr 3 := .add ⟨(-979689509530803681461/4722366482869645213696:ℚ),(22131419077215548330163/4722366482869645213696:ℚ)⟩ node2417 node2419
def node2421 : BoxExpr 3 := .mul ⟨(-33632413343810327881/295147905179352825856:ℚ),(-252463068919061493029/2361183241434822606848:ℚ)⟩ node131 node2332
def node2422 : BoxExpr 3 := .mul ⟨(-155907465298885751963/1180591620717411303424:ℚ),(-588586450616545156561/4722366482869645213696:ℚ)⟩ node118 node2330
def node2423 : BoxExpr 3 := .add ⟨(-290437118674127063487/1180591620717411303424:ℚ),(-1093512588454668142619/4722366482869645213696:ℚ)⟩ node2421 node2422
def node2424 : BoxExpr 3 := .mul ⟨(-1385047927927114694335/4722366482869645213696:ℚ),(-324686879406642454675/1180591620717411303424:ℚ)⟩ node2423 node304
def node2425 : BoxExpr 3 := .mul ⟨(533712982710978857483/2361183241434822606848:ℚ),(563131437147642504183/2361183241434822606848:ℚ)⟩ node118 node2332
def node2426 : BoxExpr 3 := .mul ⟨(1197106856494097012333/4722366482869645213696:ℚ),(642771451134127634211/2361183241434822606848:ℚ)⟩ node2425 node461
def node2427 : BoxExpr 3 := .add ⟨(-93970535716508841001/2361183241434822606848:ℚ),(-6602307679157275139/2361183241434822606848:ℚ)⟩ node2424 node2426
def node2428 : BoxExpr 3 := .add ⟨(-2945241796327488523961/4722366482869645213696:ℚ),(700184632606672611313/2361183241434822606848:ℚ)⟩ node2427 node476
def node2429 : BoxExpr 3 := .add ⟨(-1073139336488053165261/2361183241434822606848:ℚ),(-1064377133053041128243/2361183241434822606848:ℚ)⟩ node2330 node2330
def node2430 : BoxExpr 3 := .neg ⟨(1064377133053041128243/2361183241434822606848:ℚ),(1073139336488053165261/2361183241434822606848:ℚ)⟩ node2429
def node2431 : BoxExpr 3 := .mul ⟨(2299408465399993050237/1180591620717411303424:ℚ),(2300426401624512520481/1180591620717411303424:ℚ)⟩ node86 node2345
def node2432 : BoxExpr 3 := .inv ⟨(2423544737486744638033/4722366482869645213696:ℚ),(2424617628196313343843/4722366482869645213696:ℚ)⟩ node2431
def node2433 : BoxExpr 3 := .mul ⟨(1092488526195196606363/4722366482869645213696:ℚ),(1101969769690004131079/4722366482869645213696:ℚ)⟩ node2430 node2432
def node2434 : BoxExpr 3 := .mul ⟨(329820737910602991631/2361183241434822606848:ℚ),(697896371373187701249/4722366482869645213696:ℚ)⟩ node117 node2433
def node2435 : BoxExpr 3 := .neg ⟨(-697896371373187701249/4722366482869645213696:ℚ),(-329820737910602991631/2361183241434822606848:ℚ)⟩ node2434
def node2436 : BoxExpr 3 := .add ⟨(267517110366588137349/2361183241434822606848:ℚ),(319362143998073593/2305843009213693952:ℚ)⟩ node479 node2435
def node2437 : BoxExpr 3 := .add ⟨(-368155224540936065495/590295810358705651712:ℚ),(700184632606672611313/2361183241434822606848:ℚ)⟩ node2427 node492
def node2438 : BoxExpr 3 := .mul ⟨(-1991201076377417730847/4722366482869645213696:ℚ),(-242312468747609936179/590295810358705651712:ℚ)⟩ node175 node2332
def node2439 : BoxExpr 3 := .mul ⟨(501389138895801520293/2361183241434822606848:ℚ),(1036016788399312163187/4722366482869645213696:ℚ)⟩ node148 node2330
def node2440 : BoxExpr 3 := .add ⟨(-988422798585814690261/4722366482869645213696:ℚ),(-902482961581567326245/4722366482869645213696:ℚ)⟩ node2438 node2439
def node2441 : BoxExpr 3 := .add ⟨(14355479205788350325/4722366482869645213696:ℚ),(66766913408872418471/2361183241434822606848:ℚ)⟩ node2440 node2439
def node2442 : BoxExpr 3 := .mul ⟨(17049774442199171773/4722366482869645213696:ℚ),(159200338257738324025/4722366482869645213696:ℚ)⟩ node2441 node304
def node2443 : BoxExpr 3 := .mul ⟨(-935512648226857026919/2361183241434822606848:ℚ),(-1818580040628922496161/4722366482869645213696:ℚ)⟩ node148 node2332
def node2444 : BoxExpr 3 := .mul ⟨(-566743543651405125773/1180591620717411303424:ℚ),(-2232897867812300174239/4722366482869645213696:ℚ)⟩ node36 node2330
def node2445 : BoxExpr 3 := .add ⟨(-2068999735529667278465/2361183241434822606848:ℚ),(-63304342319394104225/73786976294838206464:ℚ)⟩ node2443 node2444
def node2446 : BoxExpr 3 := .mul ⟨(-4723209803873397564281/4722366482869645213696:ℚ),(-4543689342625374762477/4722366482869645213696:ℚ)⟩ node2445 node461
def node2447 : BoxExpr 3 := .add ⟨(-1176540007357799598127/1180591620717411303424:ℚ),(-1096122251091909109613/1180591620717411303424:ℚ)⟩ node2442 node2446
def node2448 : BoxExpr 3 := .mul ⟨(4992079553182568853117/1180591620717411303424:ℚ),(5155157106708543260501/1180591620717411303424:ℚ)⟩ node2333 node514
def node2449 : BoxExpr 3 := .add ⟨(15245108408856877848187/4722366482869645213696:ℚ),(16076939084208798279527/4722366482869645213696:ℚ)⟩ node2446 node2448
def node2450 : BoxExpr 3 := .add ⟨(10538948379425679455679/4722366482869645213696:ℚ),(11692450079841161841075/4722366482869645213696:ℚ)⟩ node2447 node2449
def node2451 : BoxExpr 3 := .mul ⟨(2542139930455917743/1180591620717411303424:ℚ),(746337139827465753/295147905179352825856:ℚ)⟩ node2336 node189
def node2452 : BoxExpr 3 := .add ⟨(-10797446489319232383/1180591620717411303424:ℚ),(-20292438917195666943/2361183241434822606848:ℚ)⟩ node518 node2451
def node2453 : BoxExpr 3 := .add ⟨(-24137032909094382509/1180591620717411303424:ℚ),(-23277787476505529955/1180591620717411303424:ℚ)⟩ node518 node2452
def node2454 : BoxExpr 3 := .add ⟨(10442400247789301925643/4722366482869645213696:ℚ),(11599338929935139721255/4722366482869645213696:ℚ)⟩ node2450 node2453
def node2455 : BoxExpr 3 := .add ⟨(10773066763077936648583/2361183241434822606848:ℚ),(14096404984631293097899/2361183241434822606848:ℚ)⟩ node2454 node527
def node2456 : BoxExpr 3 := .mul ⟨(-2424617628196313343843/2361183241434822606848:ℚ),(-2423544737486744638033/2361183241434822606848:ℚ)⟩ node6 node2432
def node2457 : BoxExpr 3 := .mul ⟨(1092488526195196606363/2361183241434822606848:ℚ),(1101969769690004131079/2361183241434822606848:ℚ)⟩ node86 node2433
def node2458 : BoxExpr 3 := .mul ⟨(8956999521206536576693/2361183241434822606848:ℚ),(17929863422460448462607/4722366482869645213696:ℚ)⟩ node2431 node2431
def node2459 : BoxExpr 3 := .inv ⟨(1243776635275137797533/4722366482869645213696:ℚ),(1244878105984683652453/4722366482869645213696:ℚ)⟩ node2458
def node2460 : BoxExpr 3 := .mul ⟨(575479140857380215049/4722366482869645213696:ℚ),(290493769325259216879/2361183241434822606848:ℚ)⟩ node2457 node2459
def node2461 : BoxExpr 3 := .neg ⟨(-290493769325259216879/2361183241434822606848:ℚ),(-575479140857380215049/4722366482869645213696:ℚ)⟩ node2460
def node2462 : BoxExpr 3 := .mul ⟨(-33006787168939365121/590295810358705651712:ℚ),(-259415206464615925065/4722366482869645213696:ℚ)⟩ node2430 node2461
def node2463 : BoxExpr 3 := .add ⟨(-2556644776872070804327/2361183241434822606848:ℚ),(-5106504681438105201131/4722366482869645213696:ℚ)⟩ node2456 node2462
def node2464 : BoxExpr 3 := .mul ⟨(-6338642272110503236299/2361183241434822606848:ℚ),(-3160377736247673699301/1180591620717411303424:ℚ)⟩ node11 node2463
def node2465 : BoxExpr 3 := .add ⟨(-4875935114520352579573/4722366482869645213696:ℚ),(-2420080757645020452089/2361183241434822606848:ℚ)⟩ node2464 node546
def node2466 : BoxExpr 3 := .neg ⟨(2420080757645020452089/2361183241434822606848:ℚ),(4875935114520352579573/4722366482869645213696:ℚ)⟩ node2465
def cert_iv14 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-927/4096:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/20480:ℚ)],
    whole := node2356, centerValue := node2383, gradient := ![node2390, node2400, node2414],
    hessian := ![![node2420, node2428, node2436], ![node2437, node2455, node536], ![node2436, node536, node2466]] }
def node2467 : BoxExpr 3 := .var 2
def node2468 : BoxExpr 3 := .mul ⟨(-427372884975248942197/4722366482869645213696:ℚ),(-416149005427076900061/4722366482869645213696:ℚ)⟩ node13 node2467
def node2469 : BoxExpr 3 := .add ⟨(1933810356459573664651/4722366482869645213696:ℚ),(1945034236007745706787/4722366482869645213696:ℚ)⟩ node2468 node301
def node2470 : BoxExpr 3 := .mul ⟨(2028416849442380476499/2361183241434822606848:ℚ),(1027206400844299973679/1180591620717411303424:ℚ)⟩ node36 node2469
def node2471 : BoxExpr 3 := .mul ⟨(4818236892266757969453/4722366482869645213696:ℚ),(2449291095328593725425/2361183241434822606848:ℚ)⟩ node2470 node304
def node2472 : BoxExpr 3 := .add ⟨(-125750301428973406521/4722366482869645213696:ℚ),(-12347645199151255257/590295810358705651712:ℚ)⟩ node2467 node306
def node2473 : BoxExpr 3 := .mul ⟨(2135385709429829033/2361183241434822606848:ℚ),(5436773415031008357/4722366482869645213696:ℚ)⟩ node2472 node308
def node2474 : BoxExpr 3 := .mul ⟨(1163581500982834847/1180591620717411303424:ℚ),(2968161881500884939/2361183241434822606848:ℚ)⟩ node2473 node37
def node2475 : BoxExpr 3 := .add ⟨(4822891218270689308841/4722366482869645213696:ℚ),(613064814302523652591/590295810358705651712:ℚ)⟩ node2471 node2474
def node2476 : BoxExpr 3 := .add ⟨(1942166934176259458581/590295810358705651712:ℚ),(7873141255639989858985/2361183241434822606848:ℚ)⟩ node2475 node316
def node2477 : BoxExpr 3 := .add ⟨(2693847310112063579071/1180591620717411303424:ℚ),(10998459474681234888705/4722366482869645213696:ℚ)⟩ node2476 node323
def node2478 : BoxExpr 3 := .add ⟨(2693843768337201426837/1180591620717411303424:ℚ),(5499222653790893139885/2361183241434822606848:ℚ)⟩ node2477 node325
def node2479 : BoxExpr 3 := .mul ⟨(51529/1048576:ℚ),(119950313627266549023/2361183241434822606848:ℚ)⟩ node2467 node2467
def node2480 : BoxExpr 3 := .neg ⟨(-119950313627266549023/2361183241434822606848:ℚ),(-51529/1048576:ℚ)⟩ node2479
def node2481 : BoxExpr 3 := .add ⟨(2241232927807556057825/2361183241434822606848:ℚ),(997047/1048576:ℚ)⟩ node12 node2480
def node2482 : BoxExpr 3 := .sqrt ⟨(4600852803249025040961/4722366482869645213696:ℚ),(4604871829727056394665/4722366482869645213696:ℚ)⟩ node2481
def node2483 : BoxExpr 3 := .mul ⟨(711858388184518829953/295147905179352825856:ℚ),(11416773852044326383693/4722366482869645213696:ℚ)⟩ node11 node2482
def node2484 : BoxExpr 3 := .neg ⟨(227/1024:ℚ),(266094283263260282061/1180591620717411303424:ℚ)⟩ node2467
def node2485 : BoxExpr 3 := .add ⟨(928793564111275923865/4722366482869645213696:ℚ),(473158985490649998951/2361183241434822606848:ℚ)⟩ node332 node2484
def node2486 : BoxExpr 3 := .mul ⟨(663158604775451009639/4722366482869645213696:ℚ),(675671031280648198503/4722366482869645213696:ℚ)⟩ node2485 node335
def node2487 : BoxExpr 3 := .neg ⟨(-675671031280648198503/4722366482869645213696:ℚ),(-663158604775451009639/4722366482869645213696:ℚ)⟩ node2486
def node2488 : BoxExpr 3 := .add ⟨(10714063179671653080745/4722366482869645213696:ℚ),(5376807623634437687027/2361183241434822606848:ℚ)⟩ node2483 node2487
def node2489 : BoxExpr 3 := .mul ⟨(182674827941416963931/4722366482869645213696:ℚ),(189633249653674569893/4722366482869645213696:ℚ)⟩ node2485 node2485
def node2490 : BoxExpr 3 := .mul ⟨(75444703939805206103/2361183241434822606848:ℚ),(39159266053483798683/1180591620717411303424:ℚ)⟩ node2489 node340
def node2491 : BoxExpr 3 := .add ⟨(10864952587551263492951/4722366482869645213696:ℚ),(5455126155741405284393/2361183241434822606848:ℚ)⟩ node2488 node2490
def node2492 : BoxExpr 3 := .neg ⟨(-5455126155741405284393/2361183241434822606848:ℚ),(-10864952587551263492951/4722366482869645213696:ℚ)⟩ node2491
def node2493 : BoxExpr 3 := .add ⟨(-67438619067002430719/2361183241434822606848:ℚ),(133492720030522786819/4722366482869645213696:ℚ)⟩ node2478 node2492
def node2494 : BoxExpr 3 := .var 2
def node2495 : BoxExpr 3 := .mul ⟨(-13179481899821653033/147573952589676412928:ℚ),(-210871710397146448527/2361183241434822606848:ℚ)⟩ node51 node2494
def node2496 : BoxExpr 3 := .add ⟨(60607494395016553431/147573952589676412928:ℚ),(969719910320264854897/2361183241434822606848:ℚ)⟩ node2495 node301
def node2497 : BoxExpr 3 := .mul ⟨(2041393472749778002329/2361183241434822606848:ℚ),(63793546023430562573/73786976294838206464:ℚ)⟩ node68 node2496
def node2498 : BoxExpr 3 := .mul ⟨(4858259206003572006917/4722366482869645213696:ℚ),(607282400750446500867/590295810358705651712:ℚ)⟩ node2497 node349
def node2499 : BoxExpr 3 := .add ⟨(-112265731511091724289/4722366482869645213696:ℚ),(-112265731511091724287/4722366482869645213696:ℚ)⟩ node2494 node351
def node2500 : BoxExpr 3 := .mul ⟨(4853772416945333211/4722366482869645213696:ℚ),(1213443104236333303/1180591620717411303424:ℚ)⟩ node2499 node308
def node2501 : BoxExpr 3 := .mul ⟨(5294700413502921907/4722366482869645213696:ℚ),(2647350206751460955/2361183241434822606848:ℚ)⟩ node2500 node69
def node2502 : BoxExpr 3 := .add ⟨(607944238302134366103/590295810358705651712:ℚ),(2431776953208537464423/2361183241434822606848:ℚ)⟩ node2498 node2501
def node2503 : BoxExpr 3 := .add ⟨(977659776208333555045/295147905179352825856:ℚ),(15642556419333336880795/4722366482869645213696:ℚ)⟩ node2502 node358
def node2504 : BoxExpr 3 := .add ⟨(10887671784553053789903/4722366482869645213696:ℚ),(10887671784553053789983/4722366482869645213696:ℚ)⟩ node2503 node361
def node2505 : BoxExpr 3 := .add ⟨(10887657617453605180967/4722366482869645213696:ℚ),(1360957202181700647631/590295810358705651712:ℚ)⟩ node2504 node325
def node2506 : BoxExpr 3 := .mul ⟨(235967048231998885723/4722366482869645213696:ℚ),(235967048231998885725/4722366482869645213696:ℚ)⟩ node2494 node2494
def node2507 : BoxExpr 3 := .neg ⟨(-235967048231998885725/4722366482869645213696:ℚ),(-235967048231998885723/4722366482869645213696:ℚ)⟩ node2506
def node2508 : BoxExpr 3 := .add ⟨(4486399434637646327971/4722366482869645213696:ℚ),(4486399434637646327973/4722366482869645213696:ℚ)⟩ node12 node2507
def node2509 : BoxExpr 3 := .sqrt ⟨(2301435547592966301319/2361183241434822606848:ℚ),(287679443449120787665/295147905179352825856:ℚ)⟩ node2508
def node2510 : BoxExpr 3 := .mul ⟨(11403170143509322906385/4722366482869645213696:ℚ),(11403170143509322906399/4722366482869645213696:ℚ)⟩ node50 node2509
def node2511 : BoxExpr 3 := .neg ⟨(1055614929618029091225/4722366482869645213696:ℚ),(527807464809014545613/2361183241434822606848:ℚ)⟩ node2494
def node2512 : BoxExpr 3 := .add ⟨(468777883773143980441/2361183241434822606848:ℚ),(234388941886571990221/1180591620717411303424:ℚ)⟩ node332 node2511
def node2513 : BoxExpr 3 := .mul ⟨(669414818028049604069/4722366482869645213696:ℚ),(83676852253506200509/590295810358705651712:ℚ)⟩ node2512 node335
def node2514 : BoxExpr 3 := .neg ⟨(-83676852253506200509/590295810358705651712:ℚ),(-669414818028049604069/4722366482869645213696:ℚ)⟩ node2513
def node2515 : BoxExpr 3 := .add ⟨(10733755325481273302313/4722366482869645213696:ℚ),(5366877662740636651165/2361183241434822606848:ℚ)⟩ node2510 node2514
def node2516 : BoxExpr 3 := .mul ⟨(46534445200722739855/1180591620717411303424:ℚ),(93068890401445479711/2361183241434822606848:ℚ)⟩ node2512 node2512
def node2517 : BoxExpr 3 := .mul ⟨(2402340733487311445/73786976294838206464:ℚ),(153749806943187932483/4722366482869645213696:ℚ)⟩ node2516 node340
def node2518 : BoxExpr 3 := .add ⟨(10887505132424461234793/4722366482869645213696:ℚ),(10887505132424461234813/4722366482869645213696:ℚ)⟩ node2515 node2517
def node2519 : BoxExpr 3 := .neg ⟨(-10887505132424461234813/4722366482869645213696:ℚ),(-10887505132424461234793/4722366482869645213696:ℚ)⟩ node2518
def node2520 : BoxExpr 3 := .add ⟨(76242514571973077/2361183241434822606848:ℚ),(152485029143946255/4722366482869645213696:ℚ)⟩ node2505 node2519
def node2521 : BoxExpr 3 := .mul ⟨(1099750500653357749377/4722366482869645213696:ℚ),(1099750500653357749383/4722366482869645213696:ℚ)⟩ node78 node2496
def node2522 : BoxExpr 3 := .mul ⟨(327158449940404418075/1180591620717411303424:ℚ),(327158449940404418077/1180591620717411303424:ℚ)⟩ node2521 node349
def node2523 : BoxExpr 3 := .add ⟨(5187865137042988659893/4722366482869645213696:ℚ),(5187865137042988660321/4722366482869645213696:ℚ)⟩ node2522 node385
def node2524 : BoxExpr 3 := .add ⟨(2833999076530234811131/4722366482869645213696:ℚ),(2833999076530234811561/4722366482869645213696:ℚ)⟩ node2523 node387
def node2525 : BoxExpr 3 := .mul ⟨(2847138899330635705131/4722366482869645213696:ℚ),(711784724832658926285/1180591620717411303424:ℚ)⟩ node77 node2509
def node2526 : BoxExpr 3 := .neg ⟨(-711784724832658926285/1180591620717411303424:ℚ),(-2847138899330635705131/4722366482869645213696:ℚ)⟩ node2525
def node2527 : BoxExpr 3 := .add ⟨(-13139822800400894009/4722366482869645213696:ℚ),(-6569911400200446785/2361183241434822606848:ℚ)⟩ node2524 node2526
def node2528 : BoxExpr 3 := .mul ⟨(-924864107840473918569/2361183241434822606848:ℚ),(-1849728215680947837127/4722366482869645213696:ℚ)⟩ node98 node2496
def node2529 : BoxExpr 3 := .mul ⟨(-1111107137290686215415/2361183241434822606848:ℚ),(-1111107137290686215411/2361183241434822606848:ℚ)⟩ node68 node2494
def node2530 : BoxExpr 3 := .add ⟨(-63624101410348754187/73786976294838206464:ℚ),(-4071942490262320267949/4722366482869645213696:ℚ)⟩ node2528 node2529
def node2531 : BoxExpr 3 := .mul ⟨(-4845354987587651754083/4722366482869645213696:ℚ),(-2422677493793825877029/2361183241434822606848:ℚ)⟩ node2530 node349
def node2532 : BoxExpr 3 := .mul ⟨(1154828368749956109219/1180591620717411303424:ℚ),(4619313474999824436901/4722366482869645213696:ℚ)⟩ node2497 node399
def node2533 : BoxExpr 3 := .add ⟨(-226041512587827317207/4722366482869645213696:ℚ),(-226041512587827317157/4722366482869645213696:ℚ)⟩ node2531 node2532
def node2534 : BoxExpr 3 := .mul ⟨(2517144508876499729/4722366482869645213696:ℚ),(1258572254438249865/2361183241434822606848:ℚ)⟩ node2500 node103
def node2535 : BoxExpr 3 := .add ⟨(-27210370989222425951/1180591620717411303424:ℚ),(-108841483956889703801/4722366482869645213696:ℚ)⟩ node403 node2534
def node2536 : BoxExpr 3 := .add ⟨(-334882996544717021011/4722366482869645213696:ℚ),(-167441498272358510479/2361183241434822606848:ℚ)⟩ node2533 node2535
def node2537 : BoxExpr 3 := .add ⟨(-12965761920048190737/4722366482869645213696:ℚ),(-1620720240006023821/590295810358705651712:ℚ)⟩ node2536 node409
def node2538 : BoxExpr 3 := .add ⟨(-527807464809014545613/1180591620717411303424:ℚ),(-1055614929618029091225/2361183241434822606848:ℚ)⟩ node2494 node2494
def node2539 : BoxExpr 3 := .neg ⟨(1055614929618029091225/2361183241434822606848:ℚ),(527807464809014545613/1180591620717411303424:ℚ)⟩ node2538
def node2540 : BoxExpr 3 := .mul ⟨(2301435547592966301319/1180591620717411303424:ℚ),(287679443449120787665/147573952589676412928:ℚ)⟩ node86 node2509
def node2541 : BoxExpr 3 := .inv ⟨(2422482048416976834467/4722366482869645213696:ℚ),(2422482048416976834469/4722366482869645213696:ℚ)⟩ node2540
def node2542 : BoxExpr 3 := .mul ⟨(1083019806411417963689/4722366482869645213696:ℚ),(270754951602854490923/1180591620717411303424:ℚ)⟩ node2539 node2541
def node2543 : BoxExpr 3 := .mul ⟨(2683077337146469999271/4722366482869645213696:ℚ),(2683077337146469999281/4722366482869645213696:ℚ)⟩ node50 node2542
def node2544 : BoxExpr 3 := .add ⟨(6054847005915396681849/4722366482869645213696:ℚ),(1513711751478849170465/1180591620717411303424:ℚ)⟩ node2543 node335
def node2545 : BoxExpr 3 := .mul ⟨(-234388941886571990221/1180591620717411303424:ℚ),(-468777883773143980441/2361183241434822606848:ℚ)⟩ node422 node2512
def node2546 : BoxExpr 3 := .mul ⟨(-234388941886571990221/1180591620717411303424:ℚ),(-468777883773143980441/2361183241434822606848:ℚ)⟩ node2512 node422
def node2547 : BoxExpr 3 := .add ⟨(-234388941886571990221/590295810358705651712:ℚ),(-468777883773143980441/1180591620717411303424:ℚ)⟩ node2545 node2546
def node2548 : BoxExpr 3 := .mul ⟨(-1548842127986467711381/4722366482869645213696:ℚ),(-96802632999154231961/295147905179352825856:ℚ)⟩ node2547 node340
def node2549 : BoxExpr 3 := .add ⟨(1126501219482232242617/1180591620717411303424:ℚ),(1126501219482232242621/1180591620717411303424:ℚ)⟩ node2544 node2548
def node2550 : BoxExpr 3 := .neg ⟨(-1126501219482232242621/1180591620717411303424:ℚ),(-1126501219482232242617/1180591620717411303424:ℚ)⟩ node2549
def node2551 : BoxExpr 3 := .add ⟨(-2579176049294556885/4722366482869645213696:ℚ),(-1289588024647278425/2361183241434822606848:ℚ)⟩ node414 node2550
def node2552 : BoxExpr 3 := .mul ⟨(1089212588565541600865/590295810358705651712:ℚ),(8780957619814017831097/4722366482869645213696:ℚ)⟩ node112 node2469
def node2553 : BoxExpr 3 := .mul ⟨(10349123808926324806311/4722366482869645213696:ℚ),(5234371906413043365901/2361183241434822606848:ℚ)⟩ node2552 node304
def node2554 : BoxExpr 3 := .add ⟨(10837667363894554484517/2361183241434822606848:ℚ),(44795093425486905146083/4722366482869645213696:ℚ)⟩ node2553 node448
def node2555 : BoxExpr 3 := .mul ⟨(22636195791985203201527/4722366482869645213696:ℚ),(22655969402257117461753/4722366482869645213696:ℚ)⟩ node111 node2482
def node2556 : BoxExpr 3 := .neg ⟨(-22655969402257117461753/4722366482869645213696:ℚ),(-22636195791985203201527/4722366482869645213696:ℚ)⟩ node2555
def node2557 : BoxExpr 3 := .add ⟨(-980634674468008492719/4722366482869645213696:ℚ),(5539724408375425486139/1180591620717411303424:ℚ)⟩ node2554 node2556
def node2558 : BoxExpr 3 := .mul ⟨(-270026438495442835871/2361183241434822606848:ℚ),(-126461609540874928481/1180591620717411303424:ℚ)⟩ node131 node2469
def node2559 : BoxExpr 3 := .mul ⟨(-154634477829750028161/1180591620717411303424:ℚ),(-144723921457924339839/1180591620717411303424:ℚ)⟩ node118 node2467
def node2560 : BoxExpr 3 := .add ⟨(-579295394154942892193/2361183241434822606848:ℚ),(-8474547843712477135/36893488147419103232:ℚ)⟩ node2558 node2559
def node2561 : BoxExpr 3 := .mul ⟨(-172660412905131827839/590295810358705651712:ℚ),(-644165488206511593761/2361183241434822606848:ℚ)⟩ node2560 node304
def node2562 : BoxExpr 3 := .mul ⟨(1069371502382075103991/4722366482869645213696:ℚ),(282577804526223593579/1180591620717411303424:ℚ)⟩ node118 node2469
def node2563 : BoxExpr 3 := .mul ⟨(1199288755482846587911/4722366482869645213696:ℚ),(1290163776994008214011/4722366482869645213696:ℚ)⟩ node2562 node461
def node2564 : BoxExpr 3 := .add ⟨(-181994547758208034801/4722366482869645213696:ℚ),(1832800580985026489/4722366482869645213696:ℚ)⟩ node2561 node2563
def node2565 : BoxExpr 3 := .add ⟨(-367411909081584859595/590295810358705651712:ℚ),(1415406681152644799393/4722366482869645213696:ℚ)⟩ node2564 node476
def node2566 : BoxExpr 3 := .add ⟨(-266094283263260282061/590295810358705651712:ℚ),(-227/512:ℚ)⟩ node2467 node2467
def node2567 : BoxExpr 3 := .neg ⟨(227/512:ℚ),(266094283263260282061/590295810358705651712:ℚ)⟩ node2566
def node2568 : BoxExpr 3 := .mul ⟨(4600852803249025040961/2361183241434822606848:ℚ),(4604871829727056394665/2361183241434822606848:ℚ)⟩ node86 node2482
def node2569 : BoxExpr 3 := .inv ⟨(151339345202880289435/295147905179352825856:ℚ),(2423544737486744638035/4722366482869645213696:ℚ)⟩ node2568
def node2570 : BoxExpr 3 := .mul ⟨(1073563480032932053179/4722366482869645213696:ℚ),(546244263097598303183/2361183241434822606848:ℚ)⟩ node2567 node2569
def node2571 : BoxExpr 3 := .mul ⟨(648214586585181045509/4722366482869645213696:ℚ),(691891737114488187087/4722366482869645213696:ℚ)⟩ node117 node2570
def node2572 : BoxExpr 3 := .neg ⟨(-691891737114488187087/4722366482869645213696:ℚ),(-648214586585181045509/4722366482869645213696:ℚ)⟩ node2571
def node2573 : BoxExpr 3 := .add ⟨(135259713747968947215/1180591620717411303424:ℚ),(665480560144079656217/4722366482869645213696:ℚ)⟩ node479 node2572
def node2574 : BoxExpr 3 := .add ⟨(-2939295272652678876759/4722366482869645213696:ℚ),(1415406681152644799393/4722366482869645213696:ℚ)⟩ node2564 node492
def node2575 : BoxExpr 3 := .mul ⟨(-1998358434339948390317/4722366482869645213696:ℚ),(-1942032943881849717855/4722366482869645213696:ℚ)⟩ node175 node2469
def node2576 : BoxExpr 3 := .mul ⟨(986268063512538519121/4722366482869645213696:ℚ),(1027557691287328093097/4722366482869645213696:ℚ)⟩ node148 node2467
def node2577 : BoxExpr 3 := .add ⟨(-253022592706852467799/1180591620717411303424:ℚ),(-457237626297260812379/2361183241434822606848:ℚ)⟩ node2575 node2576
def node2578 : BoxExpr 3 := .add ⟨(-25822307314871352075/4722366482869645213696:ℚ),(113082438692806468339/4722366482869645213696:ℚ)⟩ node2577 node2576
def node2579 : BoxExpr 3 := .mul ⟨(-30785608089653761731/4722366482869645213696:ℚ),(67408996356691033047/2361183241434822606848:ℚ)⟩ node2578 node304
def node2580 : BoxExpr 3 := .mul ⟨(-1877750683438755537235/4722366482869645213696:ℚ),(-1821894663655332314607/4722366482869645213696:ℚ)⟩ node148 node2469
def node2581 : BoxExpr 3 := .mul ⟨(-281058035828844656271/590295810358705651712:ℚ),(-68629199522502185273/147573952589676412928:ℚ)⟩ node36 node2467
def node2582 : BoxExpr 3 := .add ⟨(-4126214970069512787403/4722366482869645213696:ℚ),(-4018029048375402243343/4722366482869645213696:ℚ)⟩ node2580 node2581
def node2583 : BoxExpr 3 := .mul ⟨(-4709758697608603209965/4722366482869645213696:ℚ),(-2253088401077647464227/2361183241434822606848:ℚ)⟩ node2582 node461
def node2584 : BoxExpr 3 := .add ⟨(-296284019106141060731/295147905179352825856:ℚ),(-546419851180239107795/590295810358705651712:ℚ)⟩ node2579 node2583
def node2585 : BoxExpr 3 := .mul ⟨(20004713337425311991487/4722366482869645213696:ℚ),(10347374563779013798295/2361183241434822606848:ℚ)⟩ node2470 node514
def node2586 : BoxExpr 3 := .add ⟨(7647477319908354390761/2361183241434822606848:ℚ),(2023571540675341583517/590295810358705651712:ℚ)⟩ node2583 node2585
def node2587 : BoxExpr 3 := .add ⟨(5277205167059225904913/2361183241434822606848:ℚ),(738575844747551237861/295147905179352825856:ℚ)⟩ node2584 node2586
def node2588 : BoxExpr 3 := .mul ⟨(4318203136461157947/2361183241434822606848:ℚ),(5581763295291650343/2361183241434822606848:ℚ)⟩ node2473 node189
def node2589 : BoxExpr 3 := .add ⟨(-22360969703089142305/2361183241434822606848:ℚ),(-646292898141366957/73786976294838206464:ℚ)⟩ node518 node2588
def node2590 : BoxExpr 3 := .add ⟨(-49040142542639442557/2361183241434822606848:ℚ),(-46944508776339135591/2361183241434822606848:ℚ)⟩ node518 node2589
def node2591 : BoxExpr 3 := .add ⟨(1307041256129146615589/590295810358705651712:ℚ),(5861662249204070767297/2361183241434822606848:ℚ)⟩ node2587 node2590
def node2592 : BoxExpr 3 := .add ⟨(21560063327399744296235/4722366482869645213696:ℚ),(28316795537735588009137/4722366482869645213696:ℚ)⟩ node2591 node527
def node2593 : BoxExpr 3 := .mul ⟨(-2423544737486744638035/2361183241434822606848:ℚ),(-151339345202880289435/147573952589676412928:ℚ)⟩ node6 node2569
def node2594 : BoxExpr 3 := .mul ⟨(1073563480032932053179/2361183241434822606848:ℚ),(546244263097598303183/1180591620717411303424:ℚ)⟩ node86 node2570
def node2595 : BoxExpr 3 := .mul ⟨(8964931711230224231299/2361183241434822606848:ℚ),(17961201990683483701253/4722366482869645213696:ℚ)⟩ node2568 node2568
def node2596 : BoxExpr 3 := .inv ⟨(1241606503289594447301/4722366482869645213696:ℚ),(621888317637568898767/2361183241434822606848:ℚ)⟩ node2595
def node2597 : BoxExpr 3 := .mul ⟨(564523487678620847659/4722366482869645213696:ℚ),(143869785214345053763/1180591620717411303424:ℚ)⟩ node2594 node2596
def node2598 : BoxExpr 3 := .neg ⟨(-143869785214345053763/1180591620717411303424:ℚ),(-564523487678620847659/4722366482869645213696:ℚ)⟩ node2597
def node2599 : BoxExpr 3 := .mul ⟨(-259415206464615925067/4722366482869645213696:ℚ),(-31285847583751692485/590295810358705651712:ℚ)⟩ node2567 node2598
def node2600 : BoxExpr 3 := .add ⟨(-5106504681438105201137/4722366482869645213696:ℚ),(-636643228395272850225/590295810358705651712:ℚ)⟩ node2593 node2599
def node2601 : BoxExpr 3 := .mul ⟨(-12660462935369059881389/4722366482869645213696:ℚ),(-6304220081550200013481/2361183241434822606848:ℚ)⟩ node11 node2600
def node2602 : BoxExpr 3 := .add ⟨(-1214778376417101497091/1180591620717411303424:ℚ),(-300443170837484133371/295147905179352825856:ℚ)⟩ node2601 node546
def node2603 : BoxExpr 3 := .neg ⟨(300443170837484133371/295147905179352825856:ℚ),(1214778376417101497091/1180591620717411303424:ℚ)⟩ node2602
def cert_iv15 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-2289/10240:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/10240:ℚ)],
    whole := node2493, centerValue := node2520, gradient := ![node2527, node2537, node2551],
    hessian := ![![node2557, node2565, node2573], ![node2574, node2592, node536], ![node2573, node536, node2603]] }

end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part4
end

section
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646CheckB4Part4
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part4

theorem cert_iv12_check : cert_iv12.check = true := by decide +kernel

theorem cert_iv12_lower_pos : 0 < cert_iv12.lower := by decide +kernel

theorem positive_iv12 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(1173/5120:ℝ)) ≤ r) (hrhi : r ≤ (-(4673/20480:ℝ))) :
    0 < node2082.eval ![A,ρ,r] := by
  apply cert_iv12.positive_sound cert_iv12_check cert_iv12_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv12,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv12,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv12,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv13_check : cert_iv13.check = true := by decide +kernel

theorem cert_iv13_lower_pos : 0 < cert_iv13.lower := by decide +kernel

theorem positive_iv13 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(4673/20480:ℝ)) ≤ r) (hrhi : r ≤ (-(2327/10240:ℝ))) :
    0 < node2219.eval ![A,ρ,r] := by
  apply cert_iv13.positive_sound cert_iv13_check cert_iv13_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv13,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv13,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv13,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv14_check : cert_iv14.check = true := by decide +kernel

theorem cert_iv14_lower_pos : 0 < cert_iv14.lower := by decide +kernel

theorem positive_iv14 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(2327/10240:ℝ)) ≤ r) (hrhi : r ≤ (-(577/2560:ℝ))) :
    0 < node2356.eval ![A,ρ,r] := by
  apply cert_iv14.positive_sound cert_iv14_check cert_iv14_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv14,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv14,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv14,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv15_check : cert_iv15.check = true := by decide +kernel

theorem cert_iv15_lower_pos : 0 < cert_iv15.lower := by decide +kernel

theorem positive_iv15 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(577/2560:ℝ)) ≤ r) (hrhi : r ≤ (-(227/1024:ℝ))) :
    0 < node2493.eval ![A,ρ,r] := by
  apply cert_iv15.positive_sound cert_iv15_check cert_iv15_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv15,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv15,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv15,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part4
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
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646BoundB4Part4
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part4
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate.CapacityCore
noncomputable section
namespace Parameters
def b : ℚ := (103531361122339324647880530522418473224550678173/6474633415922124204664207433178390079472570088576:ℚ)
def c : ℚ := (148022665013912365111/4722366482869645213696:ℚ)
def theta : ℚ := (105113898053531722649817636563532003778556764000751/182628568201966125342452015454275643968150995402752:ℚ)
end Parameters

theorem iv_shape12 : SplitDataB4Part4.node2082.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound12 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(1173/5120:ℝ)) ≤ r) (hrhi : r ≤ (-(4673/20480:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part4.node2082 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape12 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part4.positive_iv12 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part4.node2082.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape13 : SplitDataB4Part4.node2219.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound13 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(4673/20480:ℝ)) ≤ r) (hrhi : r ≤ (-(2327/10240:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part4.node2219 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape13 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part4.positive_iv13 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part4.node2219.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape14 : SplitDataB4Part4.node2356.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound14 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(2327/10240:ℝ)) ≤ r) (hrhi : r ≤ (-(577/2560:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part4.node2356 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape14 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part4.positive_iv14 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part4.node2356.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape15 : SplitDataB4Part4.node2493.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound15 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(577/2560:ℝ)) ≤ r) (hrhi : r ≤ (-(227/1024:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part4.node2493 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape15 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part4.positive_iv15 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part4.node2493.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem actual_bound (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (r : ℝ)
    (hrlo : (-(1173/5120:ℝ)) ≤ r) (hrhi : r ≤ (-(227/1024:ℝ))) : fA A r+3/10^6 ≤ l40Lhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) r := by
  have hc : 0 ≤ (Parameters.c:ℝ) := by norm_num [Parameters.c]
  have hθ : 0 ≤ (Parameters.theta:ℝ) := by norm_num [Parameters.theta]
  by_cases h0 : r ≤ (-(4673/20480:ℝ))
  · have h := iv_bound12 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  by_cases h1 : r ≤ (-(2327/10240:ℝ))
  · have h := iv_bound13 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  by_cases h2 : r ≤ (-(577/2560:ℝ))
  · have h := iv_bound14 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  have h := iv_bound15 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
  exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
    (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
end
end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part4
end

section
-- Source module: Solutions.Sol_GaussLocalMaxCase1FamilyAdaptive0Seed25646B4Part4
set_option autoImplicit false
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate
open GaussLocalMaxColoring.Certificate.CapacityCore
theorem solution (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (r : ℝ)
    (hrlo : (-(1173/5120:ℝ)) ≤ r) (hrhi : r ≤ (-(227/1024:ℝ))) :
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
  have h := GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part4.actual_bound A ρ hAlo hAhi hρlo hρhi r hrlo hrhi
  simpa only [Case2Static,constructedA,constructedMu,constructedMass,constructedKappa,thresholdCapacity,
    GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part4.Parameters.b,GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part4.Parameters.c,GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part4.Parameters.theta,
    show ¬ (4:ℕ)=1 by decide,show ¬ (4:ℕ)=2 by decide,show ¬ (4:ℕ)=3 by decide,ite_false,and_assoc] using h
end

#print axioms solution
