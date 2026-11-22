-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_40_adaptive0seed25646_b4_part_6
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T14:29:12.237826+00:00
-- url     : https://prove2.me/submissions/9bee3a79-4fc0-4916-a16c-564996ab618c

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
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646DefsB4Part6
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part6

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
def node3152 : BoxExpr 3 := .var 2
def node3153 : BoxExpr 3 := .mul ⟨(-51662493461046124295/590295810358705651712:ℚ),(-405699448903137083627/4722366482869645213696:ℚ)⟩ node13 node3152
def node3154 : BoxExpr 3 := .add ⟨(243485411718306701561/590295810358705651712:ℚ),(1955483792531685523221/4722366482869645213696:ℚ)⟩ node3153 node301
def node3155 : BoxExpr 3 := .mul ⟨(4086356534997930745687/4722366482869645213696:ℚ),(2065449986688908134791/2361183241434822606848:ℚ)⟩ node36 node3154
def node3156 : BoxExpr 3 := .mul ⟨(2426650347695417940919/2361183241434822606848:ℚ),(1231224867778669564799/1180591620717411303424:ℚ)⟩ node3155 node304
def node3157 : BoxExpr 3 := .add ⟨(-45350743844462629225/2361183241434822606848:ℚ),(-72494551288173931003/4722366482869645213696:ℚ)⟩ node3152 node306
def node3158 : BoxExpr 3 := .mul ⟨(3134278365135872729/4722366482869645213696:ℚ),(1960724671699647287/2361183241434822606848:ℚ)⟩ node3157 node308
def node3159 : BoxExpr 3 := .mul ⟨(1707882706387788661/2361183241434822606848:ℚ),(2140883125482998405/2361183241434822606848:ℚ)⟩ node3158 node37
def node3160 : BoxExpr 3 := .add ⟨(607089557600451432395/590295810358705651712:ℚ),(2464590618682822128003/2361183241434822606848:ℚ)⟩ node3156 node3159
def node3161 : BoxExpr 3 := .add ⟨(15571160715942997818967/4722366482869645213696:ℚ),(492842038569544836039/147573952589676412928:ℚ)⟩ node3160 node316
def node3162 : BoxExpr 3 := .add ⟨(10809214482981176466603/4722366482869645213696:ℚ),(11023122197626689923983/4722366482869645213696:ℚ)⟩ node3161 node323
def node3163 : BoxExpr 3 := .add ⟨(10809200315881727857667/4722366482869645213696:ℚ),(1377888503815905164381/590295810358705651712:ℚ)⟩ node3162 node325
def node3164 : BoxExpr 3 := .mul ⟨(110278946017479093125/2361183241434822606848:ℚ),(28045175887531742331/590295810358705651712:ℚ)⟩ node3152 node3152
def node3165 : BoxExpr 3 := .neg ⟨(-28045175887531742331/590295810358705651712:ℚ),(-110278946017479093125/2361183241434822606848:ℚ)⟩ node3164
def node3166 : BoxExpr 3 := .add ⟨(562250634471173909381/590295810358705651712:ℚ),(2250904295417343513723/2361183241434822606848:ℚ)⟩ node12 node3165
def node3167 : BoxExpr 3 := .sqrt ⟨(4608820717883362438501/4722366482869645213696:ℚ),(1152692229132855813975/1180591620717411303424:ℚ)⟩ node3166
def node3168 : BoxExpr 3 := .mul ⟨(5704729671589608203861/2361183241434822606848:ℚ),(11431394390665337644243/4722366482869645213696:ℚ)⟩ node11 node3167
def node3169 : BoxExpr 3 := .neg ⟨(1020566115877980943155/4722366482869645213696:ℚ),(1029328319312992980173/4722366482869645213696:ℚ)⟩ node3152
def node3170 : BoxExpr 3 := .add ⟨(225626738451559953203/1180591620717411303424:ℚ),(911269157241251849831/4722366482869645213696:ℚ)⟩ node332 node3169
def node3171 : BoxExpr 3 := .mul ⟨(644389965017655226347/4722366482869645213696:ℚ),(162661544567563455195/1180591620717411303424:ℚ)⟩ node3170 node335
def node3172 : BoxExpr 3 := .neg ⟨(-162661544567563455195/1180591620717411303424:ℚ),(-644389965017655226347/4722366482869645213696:ℚ)⟩ node3171
def node3173 : BoxExpr 3 := .add ⟨(5379406582454481293471/2361183241434822606848:ℚ),(1348375553205960302237/590295810358705651712:ℚ)⟩ node3168 node3172
def node3174 : BoxExpr 3 := .mul ⟨(86240532646426333675/2361183241434822606848:ℚ),(87923235093198908949/2361183241434822606848:ℚ)⟩ node3170 node3170
def node3175 : BoxExpr 3 := .mul ⟨(142469359931896303231/4722366482869645213696:ℚ),(9078074023372787349/295147905179352825856:ℚ)⟩ node3174 node340
def node3176 : BoxExpr 3 := .add ⟨(10901282524840858890173/4722366482869645213696:ℚ),(1366531701252705876935/590295810358705651712:ℚ)⟩ node3173 node3175
def node3177 : BoxExpr 3 := .neg ⟨(-1366531701252705876935/590295810358705651712:ℚ),(-10901282524840858890173/4722366482869645213696:ℚ)⟩ node3176
def node3178 : BoxExpr 3 := .add ⟨(-123053294139919157813/4722366482869645213696:ℚ),(121825505686382424875/4722366482869645213696:ℚ)⟩ node3163 node3177
def node3179 : BoxExpr 3 := .var 2
def node3180 : BoxExpr 3 := .mul ⟨(-409490936092318026957/4722366482869645213696:ℚ),(-102372734023079506739/1180591620717411303424:ℚ)⟩ node51 node3179
def node3181 : BoxExpr 3 := .add ⟨(1951692305342504579891/4722366482869645213696:ℚ),(487923076335626144973/1180591620717411303424:ℚ)⟩ node3180 node301
def node3182 : BoxExpr 3 := .mul ⟨(4108580107039693265213/4722366482869645213696:ℚ),(2054290053519846632613/2361183241434822606848:ℚ)⟩ node68 node3181
def node3183 : BoxExpr 3 := .mul ⟨(4888951442991945307073/4722366482869645213696:ℚ),(4888951442991945307091/4722366482869645213696:ℚ)⟩ node3182 node349
def node3184 : BoxExpr 3 := .add ⟨(-81598019488549594727/4722366482869645213696:ℚ),(-40799009744274797363/2361183241434822606848:ℚ)⟩ node3179 node351
def node3185 : BoxExpr 3 := .mul ⟨(3527863854267583651/4722366482869645213696:ℚ),(881965963566895913/1180591620717411303424:ℚ)⟩ node3184 node308
def node3186 : BoxExpr 3 := .mul ⟨(962085806843823615/1180591620717411303424:ℚ),(1924171613687647231/2361183241434822606848:ℚ)⟩ node3185 node69
def node3187 : BoxExpr 3 := .add ⟨(4892799786219320601533/4722366482869645213696:ℚ),(4892799786219320601553/4722366482869645213696:ℚ)⟩ node3183 node3186
def node3188 : BoxExpr 3 := .add ⟨(15671802299135582553429/4722366482869645213696:ℚ),(7835901149567791276751/2361183241434822606848:ℚ)⟩ node3187 node358
def node3189 : BoxExpr 3 := .add ⟨(2729229416088824865653/1180591620717411303424:ℚ),(5458458832177649731345/2361183241434822606848:ℚ)⟩ node3188 node361
def node3190 : BoxExpr 3 := .add ⟨(2729225874313962713419/1180591620717411303424:ℚ),(10916903497255850853755/4722366482869645213696:ℚ)⟩ node3189 node325
def node3191 : BoxExpr 3 := .mul ⟨(790321/16777216:ℚ),(790321/16777216:ℚ)⟩ node3179 node3179
def node3192 : BoxExpr 3 := .neg ⟨(-790321/16777216:ℚ),(-790321/16777216:ℚ)⟩ node3191
def node3193 : BoxExpr 3 := .add ⟨(15986895/16777216:ℚ),(15986895/16777216:ℚ)⟩ node12 node3192
def node3194 : BoxExpr 3 := .sqrt ⟨(36014039078146781599/36893488147419103232:ℚ),(4609797002002788044673/4722366482869645213696:ℚ)⟩ node3193
def node3195 : BoxExpr 3 := .mul ⟨(5710164205538496364975/2361183241434822606848:ℚ),(5710164205538496364981/2361183241434822606848:ℚ)⟩ node50 node3194
def node3196 : BoxExpr 3 := .neg ⟨(889/4096:ℚ),(889/4096:ℚ)⟩ node3179
def node3197 : BoxExpr 3 := .add ⟨(906888055523745831321/4722366482869645213696:ℚ),(453444027761872915661/2361183241434822606848:ℚ)⟩ node332 node3196
def node3198 : BoxExpr 3 := .mul ⟨(647518071643954523563/4722366482869645213696:ℚ),(161879517910988630891/1180591620717411303424:ℚ)⟩ node3197 node335
def node3199 : BoxExpr 3 := .neg ⟨(-161879517910988630891/1180591620717411303424:ℚ),(-647518071643954523563/4722366482869645213696:ℚ)⟩ node3198
def node3200 : BoxExpr 3 := .add ⟨(5386405169716519103193/2361183241434822606848:ℚ),(10772810339433038206399/4722366482869645213696:ℚ)⟩ node3195 node3199
def node3201 : BoxExpr 3 := .mul ⟨(174159703240961540751/4722366482869645213696:ℚ),(10884981452560096297/295147905179352825856:ℚ)⟩ node3197 node3197
def node3202 : BoxExpr 3 := .mul ⟨(35963978719258558165/1180591620717411303424:ℚ),(71927957438517116331/2361183241434822606848:ℚ)⟩ node3201 node340
def node3203 : BoxExpr 3 := .add ⟨(5458333127155036219523/2361183241434822606848:ℚ),(10916666254310072439061/4722366482869645213696:ℚ)⟩ node3200 node3202
def node3204 : BoxExpr 3 := .neg ⟨(-10916666254310072439061/4722366482869645213696:ℚ),(-5458333127155036219523/2361183241434822606848:ℚ)⟩ node3203
def node3205 : BoxExpr 3 := .add ⟨(237242945778414615/4722366482869645213696:ℚ),(237242945778414709/4722366482869645213696:ℚ)⟩ node3190 node3204
def node3206 : BoxExpr 3 := .mul ⟨(1106698216195670504401/4722366482869645213696:ℚ),(553349108097835252203/2361183241434822606848:ℚ)⟩ node78 node3181
def node3207 : BoxExpr 3 := .mul ⟨(1316901143476758566265/4722366482869645213696:ℚ),(1316901143476758566273/4722366482869645213696:ℚ)⟩ node3206 node349
def node3208 : BoxExpr 3 := .add ⟨(2598066240379064776929/2361183241434822606848:ℚ),(2598066240379064777143/2361183241434822606848:ℚ)⟩ node3207 node385
def node3209 : BoxExpr 3 := .add ⟨(355283302530671963137/590295810358705651712:ℚ),(1421133210122687852763/2361183241434822606848:ℚ)⟩ node3208 node387
def node3210 : BoxExpr 3 := .mul ⟨(2851422968622089934267/4722366482869645213696:ℚ),(2851422968622089934275/4722366482869645213696:ℚ)⟩ node77 node3194
def node3211 : BoxExpr 3 := .neg ⟨(-2851422968622089934275/4722366482869645213696:ℚ),(-2851422968622089934267/4722366482869645213696:ℚ)⟩ node3210
def node3212 : BoxExpr 3 := .add ⟨(-9156548376714229179/4722366482869645213696:ℚ),(-9156548376714228741/4722366482869645213696:ℚ)⟩ node3209 node3211
def node3213 : BoxExpr 3 := .mul ⟨(-1861413943912493083169/4722366482869645213696:ℚ),(-1861413943912493083159/4722366482869645213696:ℚ)⟩ node98 node3181
def node3214 : BoxExpr 3 := .mul ⟨(-1078827266329641814661/2361183241434822606848:ℚ),(-539413633164820907329/1180591620717411303424:ℚ)⟩ node68 node3179
def node3215 : BoxExpr 3 := .add ⟨(-4019068476571776712491/4722366482869645213696:ℚ),(-4019068476571776712475/4722366482869645213696:ℚ)⟩ node3213 node3214
def node3216 : BoxExpr 3 := .mul ⟨(-4782438242922933107519/4722366482869645213696:ℚ),(-4782438242922933107497/4722366482869645213696:ℚ)⟩ node3215 node349
def node3217 : BoxExpr 3 := .mul ⟨(4648496163260483819765/4722366482869645213696:ℚ),(4648496163260483819789/4722366482869645213696:ℚ)⟩ node3182 node399
def node3218 : BoxExpr 3 := .add ⟨(-66971039831224643877/2361183241434822606848:ℚ),(-33485519915612321927/1180591620717411303424:ℚ)⟩ node3216 node3217
def node3219 : BoxExpr 3 := .mul ⟨(914767150786825511/2361183241434822606848:ℚ),(114345893848353189/295147905179352825856:ℚ)⟩ node3185 node103
def node3220 : BoxExpr 3 := .add ⟨(-109529094164192552511/4722366482869645213696:ℚ),(-109529094164192552507/4722366482869645213696:ℚ)⟩ node403 node3219
def node3221 : BoxExpr 3 := .add ⟨(-243471173826641840265/4722366482869645213696:ℚ),(-243471173826641840215/4722366482869645213696:ℚ)⟩ node3218 node3220
def node3222 : BoxExpr 3 := .add ⟨(78446060798026990009/4722366482869645213696:ℚ),(78446060798026990175/4722366482869645213696:ℚ)⟩ node3221 node409
def node3223 : BoxExpr 3 := .add ⟨(-889/2048:ℚ),(-889/2048:ℚ)⟩ node3179 node3179
def node3224 : BoxExpr 3 := .neg ⟨(889/2048:ℚ),(889/2048:ℚ)⟩ node3223
def node3225 : BoxExpr 3 := .mul ⟨(36014039078146781599/18446744073709551616:ℚ),(4609797002002788044673/2361183241434822606848:ℚ)⟩ node86 node3194
def node3226 : BoxExpr 3 := .inv ⟨(2418842433716903990039/4722366482869645213696:ℚ),(302355304214612998755/590295810358705651712:ℚ)⟩ node3225
def node3227 : BoxExpr 3 := .mul ⟨(1049976036901527171457/4722366482869645213696:ℚ),(524988018450763585729/2361183241434822606848:ℚ)⟩ node3224 node3226
def node3228 : BoxExpr 3 := .mul ⟨(2601214578422185234545/4722366482869645213696:ℚ),(1300607289211092617275/2361183241434822606848:ℚ)⟩ node50 node3227
def node3229 : BoxExpr 3 := .add ⟨(5972984247191111917123/4722366482869645213696:ℚ),(5972984247191111917129/4722366482869645213696:ℚ)⟩ node3228 node335
def node3230 : BoxExpr 3 := .mul ⟨(-453444027761872915661/2361183241434822606848:ℚ),(-906888055523745831321/4722366482869645213696:ℚ)⟩ node422 node3197
def node3231 : BoxExpr 3 := .mul ⟨(-453444027761872915661/2361183241434822606848:ℚ),(-906888055523745831321/4722366482869645213696:ℚ)⟩ node3197 node422
def node3232 : BoxExpr 3 := .add ⟨(-453444027761872915661/1180591620717411303424:ℚ),(-906888055523745831321/2361183241434822606848:ℚ)⟩ node3230 node3231
def node3233 : BoxExpr 3 := .mul ⟨(-23409047933206689271/73786976294838206464:ℚ),(-1498179067725228113341/4722366482869645213696:ℚ)⟩ node3232 node340
def node3234 : BoxExpr 3 := .add ⟨(4474805179465883803779/4722366482869645213696:ℚ),(1118701294866470950947/1180591620717411303424:ℚ)⟩ node3229 node3233
def node3235 : BoxExpr 3 := .neg ⟨(-1118701294866470950947/1180591620717411303424:ℚ),(-4474805179465883803779/4722366482869645213696:ℚ)⟩ node3234
def node3236 : BoxExpr 3 := .add ⟨(28620522413750609811/4722366482869645213696:ℚ),(28620522413750609839/4722366482869645213696:ℚ)⟩ node414 node3235
def node3237 : BoxExpr 3 := .mul ⟨(8777113009114247364147/4722366482869645213696:ℚ),(2207033170750000341169/1180591620717411303424:ℚ)⟩ node112 node3154
def node3238 : BoxExpr 3 := .mul ⟨(10424437590265162602159/4722366482869645213696:ℚ),(5262493192964612267095/2361183241434822606848:ℚ)⟩ node3237 node304
def node3239 : BoxExpr 3 := .add ⟨(10875324254563973382441/2361183241434822606848:ℚ),(44851335998590042948471/4722366482869645213696:ℚ)⟩ node3238 node448
def node3240 : BoxExpr 3 := .mul ⟨(1417212370749133949839/295147905179352825856:ℚ),(22684983069334602419029/4722366482869645213696:ℚ)⟩ node111 node3167
def node3241 : BoxExpr 3 := .neg ⟨(-22684983069334602419029/4722366482869645213696:ℚ),(-1417212370749133949839/295147905179352825856:ℚ)⟩ node3240
def node3242 : BoxExpr 3 := .add ⟨(-934334560206655654147/4722366482869645213696:ℚ),(22175938066603899751047/4722366482869645213696:ℚ)⟩ node3239 node3241
def node3243 : BoxExpr 3 := .mul ⟨(-271477136112883155105/2361183241434822606848:ℚ),(-509527639465006625389/4722366482869645213696:ℚ)⟩ node131 node3154
def node3244 : BoxExpr 3 := .mul ⟨(-598170111812828531811/4722366482869645213696:ℚ),(-141089884663606415887/1180591620717411303424:ℚ)⟩ node118 node3152
def node3245 : BoxExpr 3 := .add ⟨(-1141124384038594842021/4722366482869645213696:ℚ),(-1073887178119432288937/4722366482869645213696:ℚ)⟩ node3243 node3244
def node3246 : BoxExpr 3 := .mul ⟨(-1360459684728787049703/4722366482869645213696:ℚ),(-1275438729758557979143/4722366482869645213696:ℚ)⟩ node3245 node304
def node3247 : BoxExpr 3 := .mul ⟨(538576825111272330045/2361183241434822606848:ℚ),(568191866909654211621/2361183241434822606848:ℚ)⟩ node118 node3154
def node3248 : BoxExpr 3 := .mul ⟨(1208016351437844890221/4722366482869645213696:ℚ),(324273772270659408099/1180591620717411303424:ℚ)⟩ node3247 node461
def node3249 : BoxExpr 3 := .add ⟨(-76221666645471079741/2361183241434822606848:ℚ),(21656359324079653253/4722366482869645213696:ℚ)⟩ node3246 node3248
def node3250 : BoxExpr 3 := .add ⟨(-2909744058185413001441/4722366482869645213696:ℚ),(1435230239895739426157/4722366482869645213696:ℚ)⟩ node3249 node476
def node3251 : BoxExpr 3 := .add ⟨(-1029328319312992980173/2361183241434822606848:ℚ),(-1020566115877980943155/2361183241434822606848:ℚ)⟩ node3152 node3152
def node3252 : BoxExpr 3 := .neg ⟨(1020566115877980943155/2361183241434822606848:ℚ),(1029328319312992980173/2361183241434822606848:ℚ)⟩ node3251
def node3253 : BoxExpr 3 := .mul ⟨(4608820717883362438501/2361183241434822606848:ℚ),(1152692229132855813975/590295810358705651712:ℚ)⟩ node86 node3167
def node3254 : BoxExpr 3 := .inv ⟨(2418332560386366890237/4722366482869645213696:ℚ),(2419354815864091334979/4722366482869645213696:ℚ)⟩ node3253
def node3255 : BoxExpr 3 := .mul ⟨(522633784778811516415/2361183241434822606848:ℚ),(1054687490040752316343/4722366482869645213696:ℚ)⟩ node3252 node3254
def node3256 : BoxExpr 3 := .mul ⟨(631129596035538758399/4722366482869645213696:ℚ),(667951692031622926279/4722366482869645213696:ℚ)⟩ node117 node3255
def node3257 : BoxExpr 3 := .neg ⟨(-667951692031622926279/4722366482869645213696:ℚ),(-631129596035538758399/4722366482869645213696:ℚ)⟩ node3256
def node3258 : BoxExpr 3 := .add ⟨(141244725018685262417/1180591620717411303424:ℚ),(682565550693721943327/4722366482869645213696:ℚ)⟩ node479 node3257
def node3259 : BoxExpr 3 := .add ⟨(-90929501818294156295/147573952589676412928:ℚ),(1435230239895739426157/4722366482869645213696:ℚ)⟩ node3249 node492
def node3260 : BoxExpr 3 := .mul ⟨(-2009094471283744379523/4722366482869645213696:ℚ),(-1956165719485730631545/4722366482869645213696:ℚ)⟩ node175 node3154
def node3261 : BoxExpr 3 := .mul ⟨(480751371046970868461/2361183241434822606848:ℚ),(496860651419695906367/2361183241434822606848:ℚ)⟩ node148 node3152
def node3262 : BoxExpr 3 := .add ⟨(-1047591729189802642601/4722366482869645213696:ℚ),(-962444416646338818811/4722366482869645213696:ℚ)⟩ node3260 node3261
def node3263 : BoxExpr 3 := .add ⟨(-86088987095860905679/4722366482869645213696:ℚ),(31276886193052993923/4722366482869645213696:ℚ)⟩ node3262 node3261
def node3264 : BoxExpr 3 := .mul ⟨(-102636134922075522797/4722366482869645213696:ℚ),(37288610535957034363/4722366482869645213696:ℚ)⟩ node3263 node304
def node3265 : BoxExpr 3 := .mul ⟨(-471959690979079440583/1180591620717411303424:ℚ),(-229394144470121448549/590295810358705651712:ℚ)⟩ node148 node3154
def node3266 : BoxExpr 3 := .mul ⟨(-2174424734731304238463/4722366482869645213696:ℚ),(-2140989160081724560481/4722366482869645213696:ℚ)⟩ node36 node3152
def node3267 : BoxExpr 3 := .add ⟨(-4062263498647622000795/4722366482869645213696:ℚ),(-3976142315842696148873/4722366482869645213696:ℚ)⟩ node3265 node3266
def node3268 : BoxExpr 3 := .mul ⟨(-2318381492907442694623/2361183241434822606848:ℚ),(-278700079846405005391/295147905179352825856:ℚ)⟩ node3267 node461
def node3269 : BoxExpr 3 := .add ⟨(-4739399120736960912043/4722366482869645213696:ℚ),(-4421912667006523051893/4722366482869645213696:ℚ)⟩ node3264 node3268
def node3270 : BoxExpr 3 := .mul ⟨(20150293836205458307589/4722366482869645213696:ℚ),(5201482544660952357117/1180591620717411303424:ℚ)⟩ node3155 node514
def node3271 : BoxExpr 3 := .add ⟨(15513530850390572918343/4722366482869645213696:ℚ),(4086682225275332335553/1180591620717411303424:ℚ)⟩ node3268 node3270
def node3272 : BoxExpr 3 := .add ⟨(2693532932413403001575/1180591620717411303424:ℚ),(11924816234094806290319/4722366482869645213696:ℚ)⟩ node3269 node3271
def node3273 : BoxExpr 3 := .mul ⟨(396136006223142705/295147905179352825856:ℚ),(4026028001979347619/2361183241434822606848:ℚ)⟩ node3158 node189
def node3274 : BoxExpr 3 := .add ⟨(-5877521197441289653/590295810358705651712:ℚ),(-5559277008459011337/590295810358705651712:ℚ)⟩ node518 node3273
def node3275 : BoxExpr 3 := .add ⟨(-3136828601832216179/147573952589676412928:ℚ),(-48500244069651438315/2361183241434822606848:ℚ)⟩ node518 node3274
def node3276 : BoxExpr 3 := .add ⟨(2668438303598745272143/1180591620717411303424:ℚ),(11827815745955503413689/4722366482869645213696:ℚ)⟩ node3272 node3275
def node3277 : BoxExpr 3 := .add ⟨(21777486492761552460095/4722366482869645213696:ℚ),(3552660848160368736029/590295810358705651712:ℚ)⟩ node3276 node527
def node3278 : BoxExpr 3 := .mul ⟨(-2419354815864091334979/2361183241434822606848:ℚ),(-2418332560386366890237/2361183241434822606848:ℚ)⟩ node6 node3254
def node3279 : BoxExpr 3 := .mul ⟨(522633784778811516415/1180591620717411303424:ℚ),(1054687490040752316343/2361183241434822606848:ℚ)⟩ node86 node3255
def node3280 : BoxExpr 3 := .mul ⟨(8996010151538782550093/2361183241434822606848:ℚ),(18007234363338748109787/4722366482869645213696:ℚ)⟩ node3253 node3253
def node3281 : BoxExpr 3 := .inv ⟨(9675254308803101303/36893488147419103232:ℚ),(77467485664728419413/295147905179352825856:ℚ)⟩ node3280
def node3282 : BoxExpr 3 := .mul ⟨(274119636392310390237/2361183241434822606848:ℚ),(553647758169594547563/4722366482869645213696:ℚ)⟩ node3279 node3281
def node3283 : BoxExpr 3 := .neg ⟨(-553647758169594547563/4722366482869645213696:ℚ),(-274119636392310390237/2361183241434822606848:ℚ)⟩ node3282
def node3284 : BoxExpr 3 := .mul ⟨(-241355819577057623079/4722366482869645213696:ℚ),(-118481788151598221405/2361183241434822606848:ℚ)⟩ node3252 node3283
def node3285 : BoxExpr 3 := .add ⟨(-5080065451305240293037/4722366482869645213696:ℚ),(-1268407174268982555821/1180591620717411303424:ℚ)⟩ node3278 node3284
def node3286 : BoxExpr 3 := .mul ⟨(-6297456319709676745029/2361183241434822606848:ℚ),(-6280062068487272043539/2361183241434822606848:ℚ)⟩ node11 node3285
def node3287 : BoxExpr 3 := .add ⟨(-4793563209718699597033/4722366482869645213696:ℚ),(-1189693676818472548513/1180591620717411303424:ℚ)⟩ node3286 node546
def node3288 : BoxExpr 3 := .neg ⟨(1189693676818472548513/1180591620717411303424:ℚ),(4793563209718699597033/4722366482869645213696:ℚ)⟩ node3287
def cert_iv20 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-889/4096:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/20480:ℚ)],
    whole := node3178, centerValue := node3205, gradient := ![node3212, node3222, node3236],
    hessian := ![![node3242, node3250, node3258], ![node3259, node3277, node536], ![node3258, node536, node3288]] }
def node3289 : BoxExpr 3 := .var 2
def node3290 : BoxExpr 3 := .mul ⟨(-409781713366649007401/4722366482869645213696:ℚ),(-25138516462197321551/295147905179352825856:ℚ)⟩ node13 node3289
def node3291 : BoxExpr 3 := .add ⟨(1951401528068173599447/4722366482869645213696:ℚ),(122435436127479091377/295147905179352825856:ℚ)⟩ node3290 node301
def node3292 : BoxExpr 3 := .mul ⟨(4093737244026223193859/4722366482869645213696:ℚ),(1034564524177838765301/1180591620717411303424:ℚ)⟩ node36 node3291
def node3293 : BoxExpr 3 := .mul ⟨(2431033323085927679967/2361183241434822606848:ℚ),(4933671897933841861979/4722366482869645213696:ℚ)⟩ node3292 node304
def node3294 : BoxExpr 3 := .add ⟨(-81939284253913221433/4722366482869645213696:ℚ),(-63732347853161893985/4722366482869645213696:ℚ)⟩ node3289 node306
def node3295 : BoxExpr 3 := .mul ⟨(2755447347227944283/4722366482869645213696:ℚ),(221413645343210383/295147905179352825856:ℚ)⟩ node3294 node308
def node3296 : BoxExpr 3 := .mul ⟨(750727970597580825/1180591620717411303424:ℚ),(3868126872957053543/4722366482869645213696:ℚ)⟩ node3295 node37
def node3297 : BoxExpr 3 := .add ⟨(2432534779027122841617/2361183241434822606848:ℚ),(2468770012403399457761/2361183241434822606848:ℚ)⟩ node3293 node3296
def node3298 : BoxExpr 3 := .add ⟨(15579513813193632043041/4722366482869645213696:ℚ),(3944826005416647353191/1180591620717411303424:ℚ)⟩ node3297 node316
def node3299 : BoxExpr 3 := .add ⟨(10817567580231810690677/4722366482869645213696:ℚ),(11031480985067844583499/4722366482869645213696:ℚ)⟩ node3298 node323
def node3300 : BoxExpr 3 := .add ⟨(10817553413132362081741/4722366482869645213696:ℚ),(2757866704492098993641/1180591620717411303424:ℚ)⟩ node3299 node325
def node3301 : BoxExpr 3 := .mul ⟨(108393446479486024417/2361183241434822606848:ℚ),(220557892034958186251/4722366482869645213696:ℚ)⟩ node3289 node3289
def node3302 : BoxExpr 3 := .neg ⟨(-220557892034958186251/4722366482869645213696:ℚ),(-108393446479486024417/2361183241434822606848:ℚ)⟩ node3301
def node3303 : BoxExpr 3 := .add ⟨(4501808590834687027445/4722366482869645213696:ℚ),(2252789794955336582431/2361183241434822606848:ℚ)⟩ node12 node3302
def node3304 : BoxExpr 3 := .sqrt ⟨(4610768916531423255899/4722366482869645213696:ℚ),(2306349823926095347899/2361183241434822606848:ℚ)⟩ node3303
def node3305 : BoxExpr 3 := .mul ⟨(356696320179544610011/147573952589676412928:ℚ),(5718090608621173667265/2361183241434822606848:ℚ)⟩ node11 node3304
def node3306 : BoxExpr 3 := .neg ⟨(1011803912442968906137/4722366482869645213696:ℚ),(255141528969495235789/1180591620717411303424:ℚ)⟩ node3289
def node3307 : BoxExpr 3 := .add ⟨(446872375185613887897/2361183241434822606848:ℚ),(451253476903119906407/2361183241434822606848:ℚ)⟩ node332 node3306
def node3308 : BoxExpr 3 := .mul ⟨(159533437941264157979/1180591620717411303424:ℚ),(322194982508827613175/2361183241434822606848:ℚ)⟩ node3307 node335
def node3309 : BoxExpr 3 := .neg ⟨(-322194982508827613175/2361183241434822606848:ℚ),(-159533437941264157979/1180591620717411303424:ℚ)⟩ node3308
def node3310 : BoxExpr 3 := .add ⟨(5384946140363886147001/2361183241434822606848:ℚ),(5399023732738645351307/2361183241434822606848:ℚ)⟩ node3305 node3309
def node3311 : BoxExpr 3 := .mul ⟨(169148176388617131785/4722366482869645213696:ℚ),(21560133161606583419/590295810358705651712:ℚ)⟩ node3307 node3307
def node3312 : BoxExpr 3 := .mul ⟨(69858196848498875427/2361183241434822606848:ℚ),(142469359931896303233/4722366482869645213696:ℚ)⟩ node3311 node340
def node3313 : BoxExpr 3 := .add ⟨(1363701084303096255607/590295810358705651712:ℚ),(10940516825409187005847/4722366482869645213696:ℚ)⟩ node3310 node3312
def node3314 : BoxExpr 3 := .neg ⟨(-10940516825409187005847/4722366482869645213696:ℚ),(-1363701084303096255607/590295810358705651712:ℚ)⟩ node3313
def node3315 : BoxExpr 3 := .add ⟨(-61481706138412462053/2361183241434822606848:ℚ),(30464535885906482427/1180591620717411303424:ℚ)⟩ node3300 node3314
def node3316 : BoxExpr 3 := .var 2
def node3317 : BoxExpr 3 := .mul ⟨(-405990226177468064073/4722366482869645213696:ℚ),(-405990226177468064071/4722366482869645213696:ℚ)⟩ node51 node3316
def node3318 : BoxExpr 3 := .add ⟨(1955193015257354542775/4722366482869645213696:ℚ),(1955193015257354542777/4722366482869645213696:ℚ)⟩ node3317 node301
def node3319 : BoxExpr 3 := .mul ⟨(2057974790882723384113/2361183241434822606848:ℚ),(4115949581765446768241/4722366482869645213696:ℚ)⟩ node68 node3318
def node3320 : BoxExpr 3 := .mul ⟨(4897720653560051964257/4722366482869645213696:ℚ),(4897720653560051964277/4722366482869645213696:ℚ)⟩ node3319 node349
def node3321 : BoxExpr 3 := .add ⟨(-36417908026768778855/2361183241434822606848:ℚ),(-18208954013384389427/1180591620717411303424:ℚ)⟩ node3316 node351
def node3322 : BoxExpr 3 := .mul ⟨(3149032836359655205/4722366482869645213696:ℚ),(1574516418179827603/2361183241434822606848:ℚ)⟩ node3321 node308
def node3323 : BoxExpr 3 := .mul ⟨(858774579263278797/1180591620717411303424:ℚ),(1717549158526557595/2361183241434822606848:ℚ)⟩ node3322 node69
def node3324 : BoxExpr 3 := .add ⟨(4901155751877105079445/4722366482869645213696:ℚ),(4901155751877105079467/4722366482869645213696:ℚ)⟩ node3320 node3323
def node3325 : BoxExpr 3 := .add ⟨(15680158264793367031341/4722366482869645213696:ℚ),(1960019783099170878927/590295810358705651712:ℚ)⟩ node3324 node358
def node3326 : BoxExpr 3 := .add ⟨(2731318407503270985131/1180591620717411303424:ℚ),(2731318407503270985151/1180591620717411303424:ℚ)⟩ node3325 node361
def node3327 : BoxExpr 3 := .add ⟨(2731314865728408832897/1180591620717411303424:ℚ),(10925259462913635331669/4722366482869645213696:ℚ)⟩ node3326 node325
def node3328 : BoxExpr 3 := .mul ⟨(218668327998301415669/4722366482869645213696:ℚ),(218668327998301415671/4722366482869645213696:ℚ)⟩ node3316 node3316
def node3329 : BoxExpr 3 := .neg ⟨(-218668327998301415671/4722366482869645213696:ℚ),(-218668327998301415669/4722366482869645213696:ℚ)⟩ node3328
def node3330 : BoxExpr 3 := .add ⟨(4503698154871343798025/4722366482869645213696:ℚ),(4503698154871343798027/4722366482869645213696:ℚ)⟩ node12 node3329
def node3331 : BoxExpr 3 := .sqrt ⟨(4611736464231916463467/4722366482869645213696:ℚ),(4611736464231916463469/4722366482869645213696:ℚ)⟩ node3330
def node3332 : BoxExpr 3 := .mul ⟨(11425133242089703905587/4722366482869645213696:ℚ),(11425133242089703905601/4722366482869645213696:ℚ)⟩ node50 node3331
def node3333 : BoxExpr 3 := .neg ⟨(508092507080237462323/2361183241434822606848:ℚ),(1016185014160474924647/4722366482869645213696:ℚ)⟩ node3316
def node3334 : BoxExpr 3 := .add ⟨(898125852088733794303/4722366482869645213696:ℚ),(898125852088733794305/4722366482869645213696:ℚ)⟩ node332 node3333
def node3335 : BoxExpr 3 := .mul ⟨(160315464597838982283/1180591620717411303424:ℚ),(320630929195677964567/2361183241434822606848:ℚ)⟩ node3334 node335
def node3336 : BoxExpr 3 := .neg ⟨(-320630929195677964567/2361183241434822606848:ℚ),(-160315464597838982283/1180591620717411303424:ℚ)⟩ node3335
def node3337 : BoxExpr 3 := .add ⟨(10783871383698347976453/4722366482869645213696:ℚ),(10783871383698347976469/4722366482869645213696:ℚ)⟩ node3332 node3336
def node3338 : BoxExpr 3 := .mul ⟨(170810556342071197695/4722366482869645213696:ℚ),(170810556342071197697/4722366482869645213696:ℚ)⟩ node3334 node3334
def node3339 : BoxExpr 3 := .mul ⟨(8818094971159425581/295147905179352825856:ℚ),(70544759769275404649/2361183241434822606848:ℚ)⟩ node3338 node340
def node3340 : BoxExpr 3 := .add ⟨(10924960903236898785749/4722366482869645213696:ℚ),(10924960903236898785767/4722366482869645213696:ℚ)⟩ node3337 node3339
def node3341 : BoxExpr 3 := .neg ⟨(-10924960903236898785767/4722366482869645213696:ℚ),(-10924960903236898785749/4722366482869645213696:ℚ)⟩ node3340
def node3342 : BoxExpr 3 := .add ⟨(298559676736545821/4722366482869645213696:ℚ),(2332497474504265/36893488147419103232:ℚ)⟩ node3327 node3341
def node3343 : BoxExpr 3 := .mul ⟨(1108683277779188434407/4722366482869645213696:ℚ),(1108683277779188434413/4722366482869645213696:ℚ)⟩ node78 node3318
def node3344 : BoxExpr 3 := .mul ⟨(1319263241681084535969/4722366482869645213696:ℚ),(659631620840542267989/2361183241434822606848:ℚ)⟩ node3343 node349
def node3345 : BoxExpr 3 := .add ⟨(2599247289481227761781/2361183241434822606848:ℚ),(5198494578962455523991/4722366482869645213696:ℚ)⟩ node3344 node385
def node3346 : BoxExpr 3 := .add ⟨(177789282403106354675/295147905179352825856:ℚ),(2844628518449701675231/4722366482869645213696:ℚ)⟩ node3345 node387
def node3347 : BoxExpr 3 := .mul ⟨(713155659220444707401/1180591620717411303424:ℚ),(2852622636881778829613/4722366482869645213696:ℚ)⟩ node77 node3331
def node3348 : BoxExpr 3 := .neg ⟨(-2852622636881778829613/4722366482869645213696:ℚ),(-713155659220444707401/1180591620717411303424:ℚ)⟩ node3347
def node3349 : BoxExpr 3 := .add ⟨(-7994118432077154813/4722366482869645213696:ℚ),(-7994118432077154373/4722366482869645213696:ℚ)⟩ node3346 node3348
def node3350 : BoxExpr 3 := .mul ⟨(-1864752723407220296321/4722366482869645213696:ℚ),(-932376361703610148155/2361183241434822606848:ℚ)⟩ node98 node3318
def node3351 : BoxExpr 3 := .mul ⟨(-1069604446055057700161/2361183241434822606848:ℚ),(-2139208892110115400313/4722366482869645213696:ℚ)⟩ node68 node3316
def node3352 : BoxExpr 3 := .add ⟨(-4003961615517335696643/4722366482869645213696:ℚ),(-4003961615517335696623/4722366482869645213696:ℚ)⟩ node3350 node3351
def node3353 : BoxExpr 3 := .mul ⟨(-4764462030161584922789/4722366482869645213696:ℚ),(-4764462030161584922763/4722366482869645213696:ℚ)⟩ node3352 node349
def node3354 : BoxExpr 3 := .mul ⟨(2328417037096050393151/2361183241434822606848:ℚ),(4656834074192100786327/4722366482869645213696:ℚ)⟩ node3319 node399
def node3355 : BoxExpr 3 := .add ⟨(-107627955969484136487/4722366482869645213696:ℚ),(-26906988992371034109/1180591620717411303424:ℚ)⟩ node3353 node3354
def node3356 : BoxExpr 3 := .mul ⟨(1633074242344265677/4722366482869645213696:ℚ),(1633074242344265679/4722366482869645213696:ℚ)⟩ node3322 node103
def node3357 : BoxExpr 3 := .add ⟨(-1714461784740967779/73786976294838206464:ℚ),(-27431388555855484463/1180591620717411303424:ℚ)⟩ node403 node3356
def node3358 : BoxExpr 3 := .add ⟨(-217353510192906074343/4722366482869645213696:ℚ),(-13584594387056629643/295147905179352825856:ℚ)⟩ node3355 node3357
def node3359 : BoxExpr 3 := .add ⟨(104563724431762755931/4722366482869645213696:ℚ),(52281862215881378051/2361183241434822606848:ℚ)⟩ node3358 node409
def node3360 : BoxExpr 3 := .add ⟨(-1016185014160474924647/2361183241434822606848:ℚ),(-508092507080237462323/1180591620717411303424:ℚ)⟩ node3316 node3316
def node3361 : BoxExpr 3 := .neg ⟨(508092507080237462323/1180591620717411303424:ℚ),(1016185014160474924647/2361183241434822606848:ℚ)⟩ node3360
def node3362 : BoxExpr 3 := .mul ⟨(4611736464231916463467/2361183241434822606848:ℚ),(4611736464231916463469/2361183241434822606848:ℚ)⟩ node86 node3331
def node3363 : BoxExpr 3 := .inv ⟨(151114074461787400921/295147905179352825856:ℚ),(1208912595694299207369/2361183241434822606848:ℚ)⟩ node3362
def node3364 : BoxExpr 3 := .mul ⟨(1040562072114214181029/4722366482869645213696:ℚ),(1040562072114214181031/4722366482869645213696:ℚ)⟩ node3361 node3363
def node3365 : BoxExpr 3 := .mul ⟨(1288946193345621804023/2361183241434822606848:ℚ),(1288946193345621804027/2361183241434822606848:ℚ)⟩ node50 node3364
def node3366 : BoxExpr 3 := .add ⟨(92963469616565160791/73786976294838206464:ℚ),(5949662055460170290633/4722366482869645213696:ℚ)⟩ node3365 node335
def node3367 : BoxExpr 3 := .mul ⟨(-898125852088733794305/4722366482869645213696:ℚ),(-898125852088733794303/4722366482869645213696:ℚ)⟩ node422 node3334
def node3368 : BoxExpr 3 := .mul ⟨(-898125852088733794305/4722366482869645213696:ℚ),(-898125852088733794303/4722366482869645213696:ℚ)⟩ node3334 node422
def node3369 : BoxExpr 3 := .add ⟨(-898125852088733794305/2361183241434822606848:ℚ),(-898125852088733794303/2361183241434822606848:ℚ)⟩ node3367 node3368
def node3370 : BoxExpr 3 := .mul ⟨(-46365747114080882131/147573952589676412928:ℚ),(-370925976912647057047/1180591620717411303424:ℚ)⟩ node3369 node340
def node3371 : BoxExpr 3 := .add ⟨(139561192119049439451/147573952589676412928:ℚ),(4465958147809582062445/4722366482869645213696:ℚ)⟩ node3366 node3370
def node3372 : BoxExpr 3 := .neg ⟨(-4465958147809582062445/4722366482869645213696:ℚ),(-139561192119049439451/147573952589676412928:ℚ)⟩ node3371
def node3373 : BoxExpr 3 := .add ⟨(18733777035026175577/2361183241434822606848:ℚ),(18733777035026175593/2361183241434822606848:ℚ)⟩ node414 node3372
def node3374 : BoxExpr 3 := .mul ⟨(8792966084261726003453/4722366482869645213696:ℚ),(2210964426015498968967/1180591620717411303424:ℚ)⟩ node112 node3291
def node3375 : BoxExpr 3 := .mul ⟨(652704127224992003195/295147905179352825856:ℚ),(10543733910296937134985/4722366482869645213696:ℚ)⟩ node3374 node304
def node3376 : BoxExpr 3 := .add ⟨(21769476954462656213843/4722366482869645213696:ℚ),(22435041761478877774633/2361183241434822606848:ℚ)⟩ node3375 node448
def node3377 : BoxExpr 3 := .mul ⟨(11342491534667301209511/2361183241434822606848:ℚ),(22694482267432778223327/4722366482869645213696:ℚ)⟩ node111 node3304
def node3378 : BoxExpr 3 := .neg ⟨(-22694482267432778223327/4722366482869645213696:ℚ),(-11342491534667301209511/2361183241434822606848:ℚ)⟩ node3377
def node3379 : BoxExpr 3 := .add ⟨(-231251328242530502371/1180591620717411303424:ℚ),(5546275113405788282561/1180591620717411303424:ℚ)⟩ node3376 node3378
def node3380 : BoxExpr 3 := .mul ⟨(-543921403970726523033/4722366482869645213696:ℚ),(-510447939790383353255/4722366482869645213696:ℚ)⟩ node131 node3291
def node3381 : BoxExpr 3 := .mul ⟨(-148269540484071409151/1180591620717411303424:ℚ),(-559514156262001764945/4722366482869645213696:ℚ)⟩ node118 node3289
def node3382 : BoxExpr 3 := .add ⟨(-1136999565907012159637/4722366482869645213696:ℚ),(-133745262006548139775/590295810358705651712:ℚ)⟩ node3380 node3381
def node3383 : BoxExpr 3 := .mul ⟨(-677771018044560760389/2361183241434822606848:ℚ),(-1270776972184955611231/4722366482869645213696:ℚ)⟩ node3382 node304
def node3384 : BoxExpr 3 := .mul ⟨(1079099187182662049115/4722366482869645213696:ℚ),(1138407905724113106217/4722366482869645213696:ℚ)⟩ node118 node3291
def node3385 : BoxExpr 3 := .mul ⟨(605099125213297232899/2361183241434822606848:ℚ),(649702763222757052595/2361183241434822606848:ℚ)⟩ node3384 node461
def node3386 : BoxExpr 3 := .add ⟨(-36335946415631763745/1180591620717411303424:ℚ),(28628554260558493959/4722366482869645213696:ℚ)⟩ node3383 node3385
def node3387 : BoxExpr 3 := .add ⟨(-2902644510556997896939/4722366482869645213696:ℚ),(1442202434832218266863/4722366482869645213696:ℚ)⟩ node3386 node476
def node3388 : BoxExpr 3 := .add ⟨(-255141528969495235789/590295810358705651712:ℚ),(-1011803912442968906137/2361183241434822606848:ℚ)⟩ node3289 node3289
def node3389 : BoxExpr 3 := .neg ⟨(1011803912442968906137/2361183241434822606848:ℚ),(255141528969495235789/590295810358705651712:ℚ)⟩ node3388
def node3390 : BoxExpr 3 := .mul ⟨(4610768916531423255899/2361183241434822606848:ℚ),(2306349823926095347899/1180591620717411303424:ℚ)⟩ node86 node3304
def node3391 : BoxExpr 3 := .inv ⟨(2417320322266648046371/4722366482869645213696:ℚ),(1209166280193183445119/2361183241434822606848:ℚ)⟩ node3390
def node3392 : BoxExpr 3 := .mul ⟨(1035859528721294104245/4722366482869645213696:ℚ),(1045267569557623032833/4722366482869645213696:ℚ)⟩ node3389 node3391
def node3393 : BoxExpr 3 := .mul ⟨(156362261910631686141/1180591620717411303424:ℚ),(661985894688879790333/4722366482869645213696:ℚ)⟩ node117 node3392
def node3394 : BoxExpr 3 := .neg ⟨(-661985894688879790333/4722366482869645213696:ℚ),(-156362261910631686141/1180591620717411303424:ℚ)⟩ node3393
def node3395 : BoxExpr 3 := .add ⟨(285472348708742092807/2361183241434822606848:ℚ),(344123049543366978581/2361183241434822606848:ℚ)⟩ node479 node3394
def node3396 : BoxExpr 3 := .add ⟨(-1451322255278498948469/2361183241434822606848:ℚ),(1442202434832218266863/4722366482869645213696:ℚ)⟩ node3386 node492
def node3397 : BoxExpr 3 := .mul ⟨(-1006336575132504854629/2361183241434822606848:ℚ),(-30620295521667200937/73786976294838206464:ℚ)⟩ node175 node3291
def node3398 : BoxExpr 3 := .mul ⟨(953247634954409476189/4722366482869645213696:ℚ),(246315551431851935661/1180591620717411303424:ℚ)⟩ node148 node3289
def node3399 : BoxExpr 3 := .add ⟨(-1059425515310600233069/4722366482869645213696:ℚ),(-243609176914823279331/1180591620717411303424:ℚ)⟩ node3397 node3398
def node3400 : BoxExpr 3 := .add ⟨(-6636117522261922305/295147905179352825856:ℚ),(1353187258514328165/590295810358705651712:ℚ)⟩ node3399 node3398
def node3401 : BoxExpr 3 := .mul ⟨(-126586310532882776485/4722366482869645213696:ℚ),(806641561975048527/295147905179352825856:ℚ)⟩ node3400 node304
def node3402 : BoxExpr 3 := .mul ⟨(-945600728704419252015/2361183241434822606848:ℚ),(-1838467778787381406839/4722366482869645213696:ℚ)⟩ node148 node3291
def node3403 : BoxExpr 3 := .mul ⟨(-1077957423378220492769/2361183241434822606848:ℚ),(-2122607418535609437729/4722366482869645213696:ℚ)⟩ node36 node3289
def node3404 : BoxExpr 3 := .add ⟨(-126472384505164984049/147573952589676412928:ℚ),(-495134399665373855571/590295810358705651712:ℚ)⟩ node3402 node3403
def node3405 : BoxExpr 3 := .mul ⟨(-18044818836731183415/18446744073709551616:ℚ),(-1110575916131475287753/1180591620717411303424:ℚ)⟩ node3404 node461
def node3406 : BoxExpr 3 := .add ⟨(-4746059932736065730725/4722366482869645213696:ℚ),(-1107349349883575093645/1180591620717411303424:ℚ)⟩ node3401 node3405
def node3407 : BoxExpr 3 := .mul ⟨(10093344480450247443307/2361183241434822606848:ℚ),(20842990529005736705761/4722366482869645213696:ℚ)⟩ node3292 node514
def node3408 : BoxExpr 3 := .add ⟨(7783607669348655966187/2361183241434822606848:ℚ),(16400686864479835554749/4722366482869645213696:ℚ)⟩ node3405 node3407
def node3409 : BoxExpr 3 := .add ⟨(10821155405961246201649/4722366482869645213696:ℚ),(11971289464945535180169/4722366482869645213696:ℚ)⟩ node3406 node3408
def node3410 : BoxExpr 3 := .mul ⟨(5572099375119605741/4722366482869645213696:ℚ),(1818547089325635969/1180591620717411303424:ℚ)⟩ node3295 node189
def node3411 : BoxExpr 3 := .add ⟨(-47786246303980994763/4722366482869645213696:ℚ),(-22626041857164121029/2361183241434822606848:ℚ)⟩ node518 node3410
def node3412 : BoxExpr 3 := .add ⟨(-101144591983081595267/4722366482869645213696:ℚ),(-12222294473244878499/590295810358705651712:ℚ)⟩ node518 node3411
def node3413 : BoxExpr 3 := .add ⟨(5360005406989082303191/2361183241434822606848:ℚ),(11873511109159576152177/4722366482869645213696:ℚ)⟩ node3409 node3412
def node3414 : BoxExpr 3 := .add ⟨(21823744092344735977905/4722366482869645213696:ℚ),(889593192140219457085/147573952589676412928:ℚ)⟩ node3413 node527
def node3415 : BoxExpr 3 := .mul ⟨(-1209166280193183445119/1180591620717411303424:ℚ),(-2417320322266648046371/2361183241434822606848:ℚ)⟩ node6 node3391
def node3416 : BoxExpr 3 := .mul ⟨(1035859528721294104245/2361183241434822606848:ℚ),(1045267569557623032833/2361183241434822606848:ℚ)⟩ node86 node3392
def node3417 : BoxExpr 3 := .mul ⟨(9003617181669374054889/2361183241434822606848:ℚ),(18022318359642692659449/4722366482869645213696:ℚ)⟩ node3390 node3390
def node3418 : BoxExpr 3 := .inv ⟨(1237396030494533658121/4722366482869645213696:ℚ),(619216275763398483393/2361183241434822606848:ℚ)⟩ node3417
def node3419 : BoxExpr 3 := .mul ⟨(271425030996487625843/2361183241434822606848:ℚ),(548239272784620780477/4722366482869645213696:ℚ)⟩ node3416 node3418
def node3420 : BoxExpr 3 := .neg ⟨(-548239272784620780477/4722366482869645213696:ℚ),(-271425030996487625843/2361183241434822606848:ℚ)⟩ node3419
def node3421 : BoxExpr 3 := .mul ⟨(-59240894075799110703/1180591620717411303424:ℚ),(-232619733596208535585/4722366482869645213696:ℚ)⟩ node3389 node3420
def node3422 : BoxExpr 3 := .add ⟨(-634203587134491277911/590295810358705651712:ℚ),(-5067260378129504628327/4722366482869645213696:ℚ)⟩ node3415 node3421
def node3423 : BoxExpr 3 := .mul ⟨(-12578954113298643044139/4722366482869645213696:ℚ),(-12544358916205225469163/4722366482869645213696:ℚ)⟩ node11 node3422
def node3424 : BoxExpr 3 := .add ⟨(-2388802341798994575557/2361183241434822606848:ℚ),(-4743009486504571576137/4722366482869645213696:ℚ)⟩ node3423 node546
def node3425 : BoxExpr 3 := .neg ⟨(4743009486504571576137/4722366482869645213696:ℚ),(2388802341798994575557/2361183241434822606848:ℚ)⟩ node3424
def cert_iv21 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-4407/20480:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/20480:ℚ)],
    whole := node3315, centerValue := node3342, gradient := ![node3349, node3359, node3373],
    hessian := ![![node3379, node3387, node3395], ![node3396, node3414, node536], ![node3395, node536, node3425]] }
def node3426 : BoxExpr 3 := .var 2
def node3427 : BoxExpr 3 := .mul ⟨(-203131739522464510221/2361183241434822606848:ℚ),(-398733077887177206005/4722366482869645213696:ℚ)⟩ node13 node3426
def node3428 : BoxExpr 3 := .add ⟨(977459881194946793203/2361183241434822606848:ℚ),(1962450163547645400843/4722366482869645213696:ℚ)⟩ node3427 node301
def node3429 : BoxExpr 3 := .mul ⟨(2050558976527257821015/2361183241434822606848:ℚ),(2072808110022446926413/2361183241434822606848:ℚ)⟩ node36 node3428
def node3430 : BoxExpr 3 := .mul ⟨(1217708149238218709507/1180591620717411303424:ℚ),(4942444324753005464761/4722366482869645213696:ℚ)⟩ node3429 node304
def node3431 : BoxExpr 3 := .add ⟨(-73177080818901184415/4722366482869645213696:ℚ),(-6871268052268732121/590295810358705651712:ℚ)⟩ node3426 node306
def node3432 : BoxExpr 3 := .mul ⟨(2376616329320015837/4722366482869645213696:ℚ),(1581893653791718841/2361183241434822606848:ℚ)⟩ node3431 node308
def node3433 : BoxExpr 3 := .mul ⟨(2590058352005069277/4722366482869645213696:ℚ),(863621873737027569/1180591620717411303424:ℚ)⟩ node3432 node37
def node3434 : BoxExpr 3 := .add ⟨(4873422655304879907305/4722366482869645213696:ℚ),(4945898812247953575037/4722366482869645213696:ℚ)⟩ node3430 node3433
def node3435 : BoxExpr 3 := .add ⟨(1948483363805533283389/590295810358705651712:ℚ),(15787662809107744072279/4722366482869645213696:ℚ)⟩ node3434 node316
def node3436 : BoxExpr 3 := .add ⟨(2706480169370611228687/1180591620717411303424:ℚ),(5519919886254499621507/2361183241434822606848:ℚ)⟩ node3435 node323
def node3437 : BoxExpr 3 := .add ⟨(2706476627595749076453/1180591620717411303424:ℚ),(11039825605409550634079/4722366482869645213696:ℚ)⟩ node3436 node325
def node3438 : BoxExpr 3 := .mul ⟨(189225/4194304:ℚ),(216786892958972048835/4722366482869645213696:ℚ)⟩ node3426 node3426
def node3439 : BoxExpr 3 := .neg ⟨(-216786892958972048835/4722366482869645213696:ℚ),(-189225/4194304:ℚ)⟩ node3438
def node3440 : BoxExpr 3 := .add ⟨(4505579589910673164861/4722366482869645213696:ℚ),(4005079/4194304:ℚ)⟩ node12 node3439
def node3441 : BoxExpr 3 := .sqrt ⟨(4612699647852190695797/4722366482869645213696:ℚ),(4614612933770395906545/4722366482869645213696:ℚ)⟩ node3440
def node3442 : BoxExpr 3 := .mul ⟨(11419061906716274662731/4722366482869645213696:ℚ),(2860231197938583022519/1180591620717411303424:ℚ)⟩ node11 node3441
def node3443 : BoxExpr 3 := .neg ⟨(435/2048:ℚ),(505901956221484453069/2361183241434822606848:ℚ)⟩ node3426
def node3444 : BoxExpr 3 := .add ⟨(884982546936215738777/4722366482869645213696:ℚ),(223436187592806943949/1180591620717411303424:ℚ)⟩ node332 node3443
def node3445 : BoxExpr 3 := .mul ⟨(315938769256229018743/2361183241434822606848:ℚ),(638133751765056631919/4722366482869645213696:ℚ)⟩ node3444 node335
def node3446 : BoxExpr 3 := .neg ⟨(-638133751765056631919/4722366482869645213696:ℚ),(-315938769256229018743/2361183241434822606848:ℚ)⟩ node3445
def node3447 : BoxExpr 3 := .add ⟨(2695232038737804507703/1180591620717411303424:ℚ),(5404523626620937026295/2361183241434822606848:ℚ)⟩ node3442 node3446
def node3448 : BoxExpr 3 := .mul ⟨(82923901736845605601/2361183241434822606848:ℚ),(169148176388617131787/4722366482869645213696:ℚ)⟩ node3444 node3444
def node3449 : BoxExpr 3 := .mul ⟨(34247571417317235113/1180591620717411303424:ℚ),(139716393696997750857/4722366482869645213696:ℚ)⟩ node3448 node340
def node3450 : BoxExpr 3 := .add ⟨(85296237817347554463/36893488147419103232:ℚ),(10948763646938871803447/4722366482869645213696:ℚ)⟩ node3447 node3449
def node3451 : BoxExpr 3 := .neg ⟨(-10948763646938871803447/4722366482869645213696:ℚ),(-85296237817347554463/36893488147419103232:ℚ)⟩ node3450
def node3452 : BoxExpr 3 := .add ⟨(-122857136555875497635/4722366482869645213696:ℚ),(121907164789063662815/4722366482869645213696:ℚ)⟩ node3437 node3451
def node3453 : BoxExpr 3 := .var 2
def node3454 : BoxExpr 3 := .mul ⟨(-402489516262618101187/4722366482869645213696:ℚ),(-201244758131309050593/2361183241434822606848:ℚ)⟩ node51 node3453
def node3455 : BoxExpr 3 := .add ⟨(1958693725172204505661/4722366482869645213696:ℚ),(979346862586102252831/2361183241434822606848:ℚ)⟩ node3454 node301
def node3456 : BoxExpr 3 := .mul ⟨(4123319056491200271243/4722366482869645213696:ℚ),(515414882061400033907/590295810358705651712:ℚ)⟩ node68 node3455
def node3457 : BoxExpr 3 := .mul ⟨(2453244932064079310723/2361183241434822606848:ℚ),(613311233016019827683/590295810358705651712:ℚ)⟩ node3456 node349
def node3458 : BoxExpr 3 := .add ⟨(-16018403154631380173/1180591620717411303424:ℚ),(-32036806309262760345/2361183241434822606848:ℚ)⟩ node3453 node351
def node3459 : BoxExpr 3 := .mul ⟨(2770201818451726759/4722366482869645213696:ℚ),(346275227306465845/590295810358705651712:ℚ)⟩ node3458 node308
def node3460 : BoxExpr 3 := .mul ⟨(3021853406730935917/4722366482869645213696:ℚ),(3021853406730935919/4722366482869645213696:ℚ)⟩ node3459 node69
def node3461 : BoxExpr 3 := .add ⟨(4909511717534889557363/4722366482869645213696:ℚ),(4909511717534889557383/4722366482869645213696:ℚ)⟩ node3457 node3460
def node3462 : BoxExpr 3 := .add ⟨(15688514230451151509259/4722366482869645213696:ℚ),(3922128557612787877333/1180591620717411303424:ℚ)⟩ node3461 node358
def node3463 : BoxExpr 3 := .add ⟨(5466814797835434209221/2361183241434822606848:ℚ),(1366703699458858552315/590295810358705651712:ℚ)⟩ node3462 node361
def node3464 : BoxExpr 3 := .add ⟨(5466807714285709904753/2361183241434822606848:ℚ),(10933615428571419809585/4722366482869645213696:ℚ)⟩ node3463 node325
def node3465 : BoxExpr 3 := .mul ⟨(13432099182310630359/295147905179352825856:ℚ),(214913586916970085745/4722366482869645213696:ℚ)⟩ node3453 node3453
def node3466 : BoxExpr 3 := .neg ⟨(-214913586916970085745/4722366482869645213696:ℚ),(-13432099182310630359/295147905179352825856:ℚ)⟩ node3465
def node3467 : BoxExpr 3 := .add ⟨(4507452895952675127951/4722366482869645213696:ℚ),(281715805997042195497/295147905179352825856:ℚ)⟩ node12 node3466
def node3468 : BoxExpr 3 := .sqrt ⟨(1153414617531371264987/1180591620717411303424:ℚ),(2306829235062742529975/2361183241434822606848:ℚ)⟩ node3467
def node3469 : BoxExpr 3 := .mul ⟨(357184213334722448293/147573952589676412928:ℚ),(5714947413355559172695/2361183241434822606848:ℚ)⟩ node50 node3468
def node3470 : BoxExpr 3 := .neg ⟨(251855702681365721907/1180591620717411303424:ℚ),(1007422810725462887629/4722366482869645213696:ℚ)⟩ node3453
def node3471 : BoxExpr 3 := .add ⟨(889363648653721757285/4722366482869645213696:ℚ),(889363648653721757287/4722366482869645213696:ℚ)⟩ node332 node3470
def node3472 : BoxExpr 3 := .mul ⟨(635005645138757334701/4722366482869645213696:ℚ),(635005645138757334703/4722366482869645213696:ℚ)⟩ node3471 node335
def node3473 : BoxExpr 3 := .neg ⟨(-635005645138757334703/4722366482869645213696:ℚ),(-635005645138757334701/4722366482869645213696:ℚ)⟩ node3472
def node3474 : BoxExpr 3 := .add ⟨(10794889181572361010673/4722366482869645213696:ℚ),(10794889181572361010689/4722366482869645213696:ℚ)⟩ node3469 node3473
def node3475 : BoxExpr 3 := .mul ⟨(167493925432490469621/4722366482869645213696:ℚ),(83746962716245234811/2361183241434822606848:ℚ)⟩ node3471 node3471
def node3476 : BoxExpr 3 := .mul ⟨(69174991203618563953/2361183241434822606848:ℚ),(34587495601809281977/1180591620717411303424:ℚ)⟩ node3475 node340
def node3477 : BoxExpr 3 := .add ⟨(10933239163979598138579/4722366482869645213696:ℚ),(10933239163979598138597/4722366482869645213696:ℚ)⟩ node3474 node3476
def node3478 : BoxExpr 3 := .neg ⟨(-10933239163979598138597/4722366482869645213696:ℚ),(-10933239163979598138579/4722366482869645213696:ℚ)⟩ node3477
def node3479 : BoxExpr 3 := .add ⟨(376264591821670909/4722366482869645213696:ℚ),(188132295910835503/2361183241434822606848:ℚ)⟩ node3464 node3478
def node3480 : BoxExpr 3 := .mul ⟨(555334169681353182207/2361183241434822606848:ℚ),(277667084840676591105/1180591620717411303424:ℚ)⟩ node78 node3455
def node3481 : BoxExpr 3 := .mul ⟨(660812669942705252837/2361183241434822606848:ℚ),(660812669942705252841/2361183241434822606848:ℚ)⟩ node3480 node349
def node3482 : BoxExpr 3 := .add ⟨(5200856677166781493267/4722366482869645213696:ℚ),(5200856677166781493695/4722366482869645213696:ℚ)⟩ node3481 node385
def node3483 : BoxExpr 3 := .add ⟨(2846990616654027644505/4722366482869645213696:ℚ),(2846990616654027644935/4722366482869645213696:ℚ)⟩ node3482 node387
def node3484 : BoxExpr 3 := .mul ⟨(2853811507400018019821/4722366482869645213696:ℚ),(1426905753700009009915/2361183241434822606848:ℚ)⟩ node77 node3468
def node3485 : BoxExpr 3 := .neg ⟨(-1426905753700009009915/2361183241434822606848:ℚ),(-2853811507400018019821/4722366482869645213696:ℚ)⟩ node3484
def node3486 : BoxExpr 3 := .add ⟨(-6820890745990375325/4722366482869645213696:ℚ),(-3410445372995187443/2361183241434822606848:ℚ)⟩ node3483 node3485
def node3487 : BoxExpr 3 := .mul ⟨(-1868091502901947509473/4722366482869645213696:ℚ),(-1868091502901947509463/4722366482869645213696:ℚ)⟩ node98 node3455
def node3488 : BoxExpr 3 := .mul ⟨(-2120763251560947171319/4722366482869645213696:ℚ),(-2120763251560947171311/4722366482869645213696:ℚ)⟩ node68 node3453
def node3489 : BoxExpr 3 := .add ⟨(-498606844307861835099/590295810358705651712:ℚ),(-1994427377231447340387/2361183241434822606848:ℚ)⟩ node3487 node3488
def node3490 : BoxExpr 3 := .mul ⟨(-593310727175029592257/590295810358705651712:ℚ),(-296655363587514796127/295147905179352825856:ℚ)⟩ node3489 node349
def node3491 : BoxExpr 3 := .mul ⟨(4665171985123717752843/4722366482869645213696:ℚ),(2332585992561858876433/2361183241434822606848:ℚ)⟩ node3456 node399
def node3492 : BoxExpr 3 := .add ⟨(-81313832276518985213/4722366482869645213696:ℚ),(-40656916138259492583/2361183241434822606848:ℚ)⟩ node3490 node3491
def node3493 : BoxExpr 3 := .mul ⟨(359153545778720083/1180591620717411303424:ℚ),(718307091557440167/2361183241434822606848:ℚ)⟩ node3459 node103
def node3494 : BoxExpr 3 := .add ⟨(-109922014282651323201/4722366482869645213696:ℚ),(-109922014282651323197/4722366482869645213696:ℚ)⟩ node403 node3493
def node3495 : BoxExpr 3 := .add ⟨(-95617923279585154207/2361183241434822606848:ℚ),(-191235846559170308363/4722366482869645213696:ℚ)⟩ node3492 node3494
def node3496 : BoxExpr 3 := .add ⟨(32670347016374630465/1180591620717411303424:ℚ),(130681388065498522027/4722366482869645213696:ℚ)⟩ node3495 node409
def node3497 : BoxExpr 3 := .add ⟨(-1007422810725462887629/2361183241434822606848:ℚ),(-251855702681365721907/590295810358705651712:ℚ)⟩ node3453 node3453
def node3498 : BoxExpr 3 := .neg ⟨(251855702681365721907/590295810358705651712:ℚ),(1007422810725462887629/2361183241434822606848:ℚ)⟩ node3497
def node3499 : BoxExpr 3 := .mul ⟨(1153414617531371264987/590295810358705651712:ℚ),(2306829235062742529975/1180591620717411303424:ℚ)⟩ node86 node3468
def node3500 : BoxExpr 3 := .inv ⟨(1208408974295190626193/2361183241434822606848:ℚ),(604204487147595313097/1180591620717411303424:ℚ)⟩ node3499
def node3501 : BoxExpr 3 := .mul ⟨(1031159923573376532389/4722366482869645213696:ℚ),(128894990446672066549/590295810358705651712:ℚ)⟩ node3498 node3500
def node3502 : BoxExpr 3 := .mul ⟨(1277299734286855928687/2361183241434822606848:ℚ),(319324933571713982173/590295810358705651712:ℚ)⟩ node50 node3501
def node3503 : BoxExpr 3 := .add ⟨(370398071083914908747/295147905179352825856:ℚ),(5926369137342638539963/4722366482869645213696:ℚ)⟩ node3502 node335
def node3504 : BoxExpr 3 := .mul ⟨(-889363648653721757287/4722366482869645213696:ℚ),(-889363648653721757285/4722366482869645213696:ℚ)⟩ node422 node3471
def node3505 : BoxExpr 3 := .mul ⟨(-889363648653721757287/4722366482869645213696:ℚ),(-889363648653721757285/4722366482869645213696:ℚ)⟩ node3471 node422
def node3506 : BoxExpr 3 := .add ⟨(-889363648653721757287/2361183241434822606848:ℚ),(-889363648653721757285/2361183241434822606848:ℚ)⟩ node3504 node3505
def node3507 : BoxExpr 3 := .mul ⟨(-1469228747575948343039/4722366482869645213696:ℚ),(-734614373787974171517/2361183241434822606848:ℚ)⟩ node3506 node340
def node3508 : BoxExpr 3 := .add ⟨(4457140389766690196913/4722366482869645213696:ℚ),(4457140389766690196929/4722366482869645213696:ℚ)⟩ node3503 node3507
def node3509 : BoxExpr 3 := .neg ⟨(-4457140389766690196929/4722366482869645213696:ℚ),(-4457140389766690196913/4722366482869645213696:ℚ)⟩ node3508
def node3510 : BoxExpr 3 := .add ⟨(23142656056472108335/2361183241434822606848:ℚ),(46285312112944216705/4722366482869645213696:ℚ)⟩ node414 node3509
def node3511 : BoxExpr 3 := .mul ⟨(4404409579704602321379/2361183241434822606848:ℚ),(8859582725123990387059/4722366482869645213696:ℚ)⟩ node112 node3428
def node3512 : BoxExpr 3 := .mul ⟨(653880905058411343755/295147905179352825856:ℚ),(10562481434664649735779/4722366482869645213696:ℚ)⟩ node3511 node304
def node3513 : BoxExpr 3 := .add ⟨(21788305399797365662803/4722366482869645213696:ℚ),(11222207761831367037515/1180591620717411303424:ℚ)⟩ node3512 node448
def node3514 : BoxExpr 3 := .mul ⟨(2836810283429097277915/590295810358705651712:ℚ),(22703895634150347860203/4722366482869645213696:ℚ)⟩ node111 node3441
def node3515 : BoxExpr 3 := .neg ⟨(-22703895634150347860203/4722366482869645213696:ℚ),(-2836810283429097277915/590295810358705651712:ℚ)⟩ node3514
def node3516 : BoxExpr 3 := .add ⟨(-114448779294122774675/590295810358705651712:ℚ),(5548587194973172481685/1180591620717411303424:ℚ)⟩ node3513 node3515
def node3517 : BoxExpr 3 := .mul ⟨(-34055533482230420991/295147905179352825856:ℚ),(-511368240115760081121/4722366482869645213696:ℚ)⟩ node131 node3428
def node3518 : BoxExpr 3 := .mul ⟨(-587986212059742741395/4722366482869645213696:ℚ),(-554668773869577866343/4722366482869645213696:ℚ)⟩ node118 node3426
def node3519 : BoxExpr 3 := .add ⟨(-1132874747775429477251/4722366482869645213696:ℚ),(-133254626748167243433/590295810358705651712:ℚ)⟩ node3517 node3518
def node3520 : BoxExpr 3 := .mul ⟨(-1350624387449455991851/4722366482869645213696:ℚ),(-1266115214611353243321/4722366482869645213696:ℚ)⟩ node3519 node304
def node3521 : BoxExpr 3 := .mul ⟨(1081044724142779438139/4722366482869645213696:ℚ),(142554009703614723649/590295810358705651712:ℚ)⟩ node118 node3428
def node3522 : BoxExpr 3 := .mul ⟨(1212380149415344041375/4722366482869645213696:ℚ),(1301715963808390577985/4722366482869645213696:ℚ)⟩ node3521 node461
def node3523 : BoxExpr 3 := .add ⟨(-34561059508527987619/1180591620717411303424:ℚ),(4450093649629666833/590295810358705651712:ℚ)⟩ node3520 node3522
def node3524 : BoxExpr 3 := .add ⟨(-2895544962928582792435/4722366482869645213696:ℚ),(90573414360543569223/295147905179352825856:ℚ)⟩ node3523 node476
def node3525 : BoxExpr 3 := .add ⟨(-505901956221484453069/1180591620717411303424:ℚ),(-435/1024:ℚ)⟩ node3426 node3426
def node3526 : BoxExpr 3 := .neg ⟨(435/1024:ℚ),(505901956221484453069/1180591620717411303424:ℚ)⟩ node3525
def node3527 : BoxExpr 3 := .mul ⟨(4612699647852190695797/2361183241434822606848:ℚ),(4614612933770395906545/2361183241434822606848:ℚ)⟩ node86 node3441
def node3528 : BoxExpr 3 := .inv ⟨(2416318065956365234293/4722366482869645213696:ℚ),(604330080566662011593/1180591620717411303424:ℚ)⟩ node3527
def node3529 : BoxExpr 3 := .mul ⟨(1026463240909198121989/4722366482869645213696:ℚ),(1035859528721294104247/4722366482869645213696:ℚ)⟩ node3526 node3528
def node3530 : BoxExpr 3 := .mul ⟨(309887797846118272323/2361183241434822606848:ℚ),(656027620930379346527/4722366482869645213696:ℚ)⟩ node117 node3529
def node3531 : BoxExpr 3 := .neg ⟨(-656027620930379346527/4722366482869645213696:ℚ),(-309887797846118272323/2361183241434822606848:ℚ)⟩ node3530
def node3532 : BoxExpr 3 := .add ⟨(144225742793996157355/1180591620717411303424:ℚ),(86739943879628019635/590295810358705651712:ℚ)⟩ node479 node3531
def node3533 : BoxExpr 3 := .add ⟨(-1447772481464291396217/2361183241434822606848:ℚ),(90573414360543569223/295147905179352825856:ℚ)⟩ node3523 node492
def node3534 : BoxExpr 3 := .mul ⟨(-2016251829246275038993/4722366482869645213696:ℚ),(-981616053643835544195/2361183241434822606848:ℚ)⟩ node175 node3428
def node3535 : BoxExpr 3 := .mul ⟨(944992527814877215457/4722366482869645213696:ℚ),(976803108615423672553/4722366482869645213696:ℚ)⟩ node148 node3426
def node3536 : BoxExpr 3 := .add ⟨(-66953706339462363971/295147905179352825856:ℚ),(-986428998672247415837/4722366482869645213696:ℚ)⟩ node3534 node3535
def node3537 : BoxExpr 3 := .add ⟨(-126266773616520608079/4722366482869645213696:ℚ),(-2406472514205935821/1180591620717411303424:ℚ)⟩ node3536 node3535
def node3538 : BoxExpr 3 := .mul ⟨(-150536486143690030171/4722366482869645213696:ℚ),(-11432516596734519345/4722366482869645213696:ℚ)⟩ node3537 node304
def node3539 : BoxExpr 3 := .mul ⟨(-59205129715667476429/147573952589676412928:ℚ),(-1841782401813791225285/4722366482869645213696:ℚ)⟩ node148 node3428
def node3540 : BoxExpr 3 := .mul ⟨(-2137404958781577732611/4722366482869645213696:ℚ),(-1052112838494747157489/2361183241434822606848:ℚ)⟩ node36 node3426
def node3541 : BoxExpr 3 := .add ⟨(-4031969109682936978339/4722366482869645213696:ℚ),(-3946008078803285540263/4722366482869645213696:ℚ)⟩ node3539 node3540
def node3542 : BoxExpr 3 := .mul ⟨(-2301092129295740259615/2361183241434822606848:ℚ),(-553175756438665276971/590295810358705651712:ℚ)⟩ node3541 node461
def node3543 : BoxExpr 3 := .add ⟨(-4752720744735170549401/4722366482869645213696:ℚ),(-4436838568106056735113/4722366482869645213696:ℚ)⟩ node3538 node3542
def node3544 : BoxExpr 3 := .mul ⟨(20223084085595531465633/4722366482869645213696:ℚ),(20880050879367663983053/4722366482869645213696:ℚ)⟩ node3429 node514
def node3545 : BoxExpr 3 := .add ⟨(15620899827004050946403/4722366482869645213696:ℚ),(16454644827858341767285/4722366482869645213696:ℚ)⟩ node3542 node3544
def node3546 : BoxExpr 3 := .add ⟨(5434089541134440198501/2361183241434822606848:ℚ),(3004451564938071258043/1180591620717411303424:ℚ)⟩ node3543 node3545
def node3547 : BoxExpr 3 := .mul ⟨(2403011325334464101/2361183241434822606848:ℚ),(6496320710646392513/4722366482869645213696:ℚ)⟩ node3432 node189
def node3548 : BoxExpr 3 := .add ⟨(-24276161514215836151/2361183241434822606848:ℚ),(-46029951360984393421/4722366482869645213696:ℚ)⟩ node518 node3547
def node3549 : BoxExpr 3 := .add ⟨(-50955334353766136403/2361183241434822606848:ℚ),(-98556223432615179355/4722366482869645213696:ℚ)⟩ node518 node3548
def node3550 : BoxExpr 3 := .add ⟨(2691567103390337031049/1180591620717411303424:ℚ),(11919250036319669852817/4722366482869645213696:ℚ)⟩ node3546 node3549
def node3551 : BoxExpr 3 := .add ⟨(21870001691927919495719/4722366482869645213696:ℚ),(445511266806986192615/73786976294838206464:ℚ)⟩ node3550 node527
def node3552 : BoxExpr 3 := .mul ⟨(-604330080566662011593/590295810358705651712:ℚ),(-2416318065956365234293/2361183241434822606848:ℚ)⟩ node6 node3528
def node3553 : BoxExpr 3 := .mul ⟨(1026463240909198121989/2361183241434822606848:ℚ),(1035859528721294104247/2361183241434822606848:ℚ)⟩ node86 node3529
def node3554 : BoxExpr 3 := .mul ⟨(18022318359642692659441/4722366482869645213696:ℚ),(4509318072997349687297/1180591620717411303424:ℚ)⟩ node3527 node3527
def node3555 : BoxExpr 3 := .inv ⟨(1236370158276908170749/4722366482869645213696:ℚ),(618698015247266829061/2361183241434822606848:ℚ)⟩ node3554
def node3556 : BoxExpr 3 := .mul ⟨(268739947276846057209/2361183241434822606848:ℚ),(67856257749121906461/590295810358705651712:ℚ)⟩ node3553 node3555
def node3557 : BoxExpr 3 := .neg ⟨(-67856257749121906461/590295810358705651712:ℚ),(-268739947276846057209/2361183241434822606848:ℚ)⟩ node3556
def node3558 : BoxExpr 3 := .mul ⟨(-232619733596208535587/4722366482869645213696:ℚ),(-57080994660853532659/1180591620717411303424:ℚ)⟩ node3526 node3557
def node3559 : BoxExpr 3 := .add ⟨(-5067260378129504628331/4722366482869645213696:ℚ),(-2530480055278072299611/2361183241434822606848:ℚ)⟩ node3552 node3558
def node3560 : BoxExpr 3 := .mul ⟨(-12563165257513412714907/4722366482869645213696:ℚ),(-6264381080694431156369/2361183241434822606848:ℚ)⟩ node11 node3559
def node3561 : BoxExpr 3 := .add ⟨(-2380907913906379410941/2361183241434822606848:ℚ),(-36932911966314128279/36893488147419103232:ℚ)⟩ node3560 node546
def node3562 : BoxExpr 3 := .neg ⟨(36932911966314128279/36893488147419103232:ℚ),(2380907913906379410941/2361183241434822606848:ℚ)⟩ node3561
def cert_iv22 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-4369/20480:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/20480:ℚ)],
    whole := node3452, centerValue := node3479, gradient := ![node3486, node3496, node3510],
    hessian := ![![node3516, node3524, node3532], ![node3533, node3551, node536], ![node3532, node536, node3562]] }
def node3563 : BoxExpr 3 := .var 2
def node3564 : BoxExpr 3 := .mul ⟨(-402745244723209033483/4722366482869645213696:ℚ),(-197624946189598633597/2361183241434822606848:ℚ)⟩ node13 node3563
def node3565 : BoxExpr 3 := .add ⟨(1958437996711613573365/4722366482869645213696:ℚ),(982966674527812669827/2361183241434822606848:ℚ)⟩ node3564 node301
def node3566 : BoxExpr 3 := .mul ⟨(2054249331041404045101/2361183241434822606848:ℚ),(4152974343378432644447/4722366482869645213696:ℚ)⟩ node36 node3565
def node3567 : BoxExpr 3 := .mul ⟨(1219899636933473579031/1180591620717411303424:ℚ),(2475608375786084533771/2361183241434822606848:ℚ)⟩ node3566 node304
def node3568 : BoxExpr 3 := .add ⟨(-64414877383889147397/4722366482869645213696:ℚ),(-23103970491568909975/2361183241434822606848:ℚ)⟩ node3563 node306
def node3569 : BoxExpr 3 := .mul ⟨(1997785311412087391/4722366482869645213696:ℚ),(2784956289675509237/4722366482869645213696:ℚ)⟩ node3568 node308
def node3570 : BoxExpr 3 := .mul ⟨(2177204821619815255/4722366482869645213696:ℚ),(1520424058469583505/2361183241434822606848:ℚ)⟩ node3569 node37
def node3571 : BoxExpr 3 := .add ⟨(4881775752555514131379/4722366482869645213696:ℚ),(619282199961138529319/590295810358705651712:ℚ)⟩ node3567 node3570
def node3572 : BoxExpr 3 := .add ⟨(7798110003847450245593/2361183241434822606848:ℚ),(7898010798274449365897/2361183241434822606848:ℚ)⟩ node3571 node316
def node3573 : BoxExpr 3 := .add ⟨(5417136887366539569411/2361183241434822606848:ℚ),(11048198559950153902529/4722366482869645213696:ℚ)⟩ node3572 node323
def node3574 : BoxExpr 3 := .add ⟨(5417129803816815264943/2361183241434822606848:ℚ),(5524092196425352646797/2361183241434822606848:ℚ)⟩ node3573 node325
def node3575 : BoxExpr 3 := .mul ⟨(104671221387464309473/2361183241434822606848:ℚ),(189225/4194304:ℚ)⟩ node3563 node3563
def node3576 : BoxExpr 3 := .neg ⟨(-189225/4194304:ℚ),(-104671221387464309473/2361183241434822606848:ℚ)⟩ node3575
def node3577 : BoxExpr 3 := .add ⟨(4005079/4194304:ℚ),(2256512020047358297375/2361183241434822606848:ℚ)⟩ node12 node3576
def node3578 : BoxExpr 3 := .sqrt ⟨(288413308360649744159/295147905179352825856:ℚ),(4616508795976483732893/4722366482869645213696:ℚ)⟩ node3577
def node3579 : BoxExpr 3 := .mul ⟨(11423798380367969464567/4722366482869645213696:ℚ),(715351572998625751483/295147905179352825856:ℚ)⟩ node11 node3578
def node3580 : BoxExpr 3 := .neg ⟨(497139752786472416051/2361183241434822606848:ℚ),(435/2048:ℚ)⟩ node3563
def node3581 : BoxExpr 3 := .add ⟨(876220343501203701759/4722366482869645213696:ℚ),(442491273468107869389/2361183241434822606848:ℚ)⟩ node332 node3580
def node3582 : BoxExpr 3 := .mul ⟨(625621325259859443055/4722366482869645213696:ℚ),(39492346157028627343/295147905179352825856:ℚ)⟩ node3581 node335
def node3583 : BoxExpr 3 := .neg ⟨(-39492346157028627343/295147905179352825856:ℚ),(-625621325259859443055/4722366482869645213696:ℚ)⟩ node3582
def node3584 : BoxExpr 3 := .add ⟨(10791920841855511427079/4722366482869645213696:ℚ),(10820003842718152580673/4722366482869645213696:ℚ)⟩ node3579 node3583
def node3585 : BoxExpr 3 := .mul ⟨(162579946548074905599/4722366482869645213696:ℚ),(165847803473691211203/4722366482869645213696:ℚ)⟩ node3581 node3581
def node3586 : BoxExpr 3 := .mul ⟨(16786379481088734003/590295810358705651712:ℚ),(68495142834634470227/2361183241434822606848:ℚ)⟩ node3585 node340
def node3587 : BoxExpr 3 := .add ⟨(10926211877704221299103/4722366482869645213696:ℚ),(10956994128387421521127/4722366482869645213696:ℚ)⟩ node3584 node3586
def node3588 : BoxExpr 3 := .neg ⟨(-10956994128387421521127/4722366482869645213696:ℚ),(-10926211877704221299103/4722366482869645213696:ℚ)⟩ node3587
def node3589 : BoxExpr 3 := .add ⟨(-122734520753790991241/4722366482869645213696:ℚ),(121972515146483994491/4722366482869645213696:ℚ)⟩ node3574 node3588
def node3590 : BoxExpr 3 := .var 2
def node3591 : BoxExpr 3 := .mul ⟨(-199494403173884069151/2361183241434822606848:ℚ),(-398988806347768138301/4722366482869645213696:ℚ)⟩ node51 node3590
def node3592 : BoxExpr 3 := .add ⟨(981097217543527234273/2361183241434822606848:ℚ),(1962194435087054468547/4722366482869645213696:ℚ)⟩ node3591 node301
def node3593 : BoxExpr 3 := .mul ⟨(2065344265608476887129/2361183241434822606848:ℚ),(4130688531216953774271/4722366482869645213696:ℚ)⟩ node68 node3592
def node3594 : BoxExpr 3 := .mul ⟨(614407384337033159829/590295810358705651712:ℚ),(2457629537348132639325/2361183241434822606848:ℚ)⟩ node3593 node349
def node3595 : BoxExpr 3 := .add ⟨(-55311409183513483675/4722366482869645213696:ℚ),(-55311409183513483673/4722366482869645213696:ℚ)⟩ node3590 node351
def node3596 : BoxExpr 3 := .mul ⟨(2391370800543798313/4722366482869645213696:ℚ),(2391370800543798315/4722366482869645213696:ℚ)⟩ node3595 node308
def node3597 : BoxExpr 3 := .mul ⟨(1304304248204378323/2361183241434822606848:ℚ),(2608608496408756649/4722366482869645213696:ℚ)⟩ node3596 node69
def node3598 : BoxExpr 3 := .add ⟨(2458933841596337017639/2361183241434822606848:ℚ),(4917867683192674035299/4722366482869645213696:ℚ)⟩ node3594 node3597
def node3599 : BoxExpr 3 := .add ⟨(7848435098054467993587/2361183241434822606848:ℚ),(981054387256808499203/295147905179352825856:ℚ)⟩ node3598 node358
def node3600 : BoxExpr 3 := .add ⟨(10941985561328652896357/4722366482869645213696:ℚ),(2735496390332163224109/1180591620717411303424:ℚ)⟩ node3599 node361
def node3601 : BoxExpr 3 := .add ⟨(10941971394229204287421/4722366482869645213696:ℚ),(10941971394229204287501/4722366482869645213696:ℚ)⟩ node3600 node325
def node3602 : BoxExpr 3 := .mul ⟨(13199460114059273175/295147905179352825856:ℚ),(211191361824948370801/4722366482869645213696:ℚ)⟩ node3590 node3590
def node3603 : BoxExpr 3 := .neg ⟨(-211191361824948370801/4722366482869645213696:ℚ),(-13199460114059273175/295147905179352825856:ℚ)⟩ node3602
def node3604 : BoxExpr 3 := .add ⟨(4511175121044696842895/4722366482869645213696:ℚ),(281948445065293552681/295147905179352825856:ℚ)⟩ node12 node3603
def node3605 : BoxExpr 3 := .sqrt ⟨(4615563041490917719615/4722366482869645213696:ℚ),(4615563041490917719617/4722366482869645213696:ℚ)⟩ node3604
def node3606 : BoxExpr 3 := .mul ⟨(11434613218967029910473/4722366482869645213696:ℚ),(11434613218967029910487/4722366482869645213696:ℚ)⟩ node50 node3605
def node3607 : BoxExpr 3 := .neg ⟨(998660607290450850611/4722366482869645213696:ℚ),(249665151822612712653/1180591620717411303424:ℚ)⟩ node3590
def node3608 : BoxExpr 3 := .add ⟨(220150361304677430067/1180591620717411303424:ℚ),(440300722609354860135/2361183241434822606848:ℚ)⟩ node332 node3607
def node3609 : BoxExpr 3 := .mul ⟨(628749431886158740271/4722366482869645213696:ℚ),(628749431886158740273/4722366482869645213696:ℚ)⟩ node3608 node335
def node3610 : BoxExpr 3 := .neg ⟨(-628749431886158740273/4722366482869645213696:ℚ),(-628749431886158740271/4722366482869645213696:ℚ)⟩ node3609
def node3611 : BoxExpr 3 := .add ⟨(1350732973385108896275/590295810358705651712:ℚ),(1350732973385108896277/590295810358705651712:ℚ)⟩ node3606 node3610
def node3612 : BoxExpr 3 := .mul ⟨(10263113157013709783/295147905179352825856:ℚ),(82104905256109678265/2361183241434822606848:ℚ)⟩ node3608 node3608
def node3613 : BoxExpr 3 := .mul ⟨(33909325870773297123/1180591620717411303424:ℚ),(67818651741546594247/2361183241434822606848:ℚ)⟩ node3612 node340
def node3614 : BoxExpr 3 := .add ⟨(2735375272640991089673/1180591620717411303424:ℚ),(5470750545281982179355/2361183241434822606848:ℚ)⟩ node3611 node3613
def node3615 : BoxExpr 3 := .neg ⟨(-5470750545281982179355/2361183241434822606848:ℚ),(-2735375272640991089673/1180591620717411303424:ℚ)⟩ node3614
def node3616 : BoxExpr 3 := .add ⟨(470303665239928711/4722366482869645213696:ℚ),(470303665239928809/4722366482869645213696:ℚ)⟩ node3601 node3615
def node3617 : BoxExpr 3 := .mul ⟨(1112653400946224294421/4722366482869645213696:ℚ),(556326700473112147213/2361183241434822606848:ℚ)⟩ node78 node3592
def node3618 : BoxExpr 3 := .mul ⟨(661993719044868237689/2361183241434822606848:ℚ),(661993719044868237693/2361183241434822606848:ℚ)⟩ node3617 node349
def node3619 : BoxExpr 3 := .add ⟨(5203218775371107462971/4722366482869645213696:ℚ),(5203218775371107463399/4722366482869645213696:ℚ)⟩ node3618 node385
def node3620 : BoxExpr 3 := .add ⟨(2849352714858353614209/4722366482869645213696:ℚ),(2849352714858353614639/4722366482869645213696:ℚ)⟩ node3619 node387
def node3621 : BoxExpr 3 := .mul ⟨(713747398416486454411/1180591620717411303424:ℚ),(2854989593665945817653/4722366482869645213696:ℚ)⟩ node77 node3605
def node3622 : BoxExpr 3 := .neg ⟨(-2854989593665945817653/4722366482869645213696:ℚ),(-713747398416486454411/1180591620717411303424:ℚ)⟩ node3621
def node3623 : BoxExpr 3 := .add ⟨(-1409219701898050861/1180591620717411303424:ℚ),(-5636878807592203005/4722366482869645213696:ℚ)⟩ node3620 node3622
def node3624 : BoxExpr 3 := .mul ⟨(-1871430282396674722625/4722366482869645213696:ℚ),(-1871430282396674722615/4722366482869645213696:ℚ)⟩ node98 node3592
def node3625 : BoxExpr 3 := .mul ⟨(-1051158805505889471159/2361183241434822606848:ℚ),(-1051158805505889471155/2361183241434822606848:ℚ)⟩ node68 node3590
def node3626 : BoxExpr 3 := .add ⟨(-3973747893408453664943/4722366482869645213696:ℚ),(-3973747893408453664925/4722366482869645213696:ℚ)⟩ node3624 node3625
def node3627 : BoxExpr 3 := .mul ⟨(-4728509604638888553325/4722366482869645213696:ℚ),(-4728509604638888553301/4722366482869645213696:ℚ)⟩ node3626 node349
def node3628 : BoxExpr 3 := .mul ⟨(2336754948027667359691/2361183241434822606848:ℚ),(4673509896055334719405/4722366482869645213696:ℚ)⟩ node3593 node399
def node3629 : BoxExpr 3 := .add ⟨(-54999708583553833943/4722366482869645213696:ℚ),(-6874963572944229237/590295810358705651712:ℚ)⟩ node3627 node3628
def node3630 : BoxExpr 3 := .mul ⟨(310038530971373747/1180591620717411303424:ℚ),(620077061942747495/2361183241434822606848:ℚ)⟩ node3596 node103
def node3631 : BoxExpr 3 := .add ⟨(-110118474341880708545/4722366482869645213696:ℚ),(-110118474341880708541/4722366482869645213696:ℚ)⟩ node403 node3630
def node3632 : BoxExpr 3 := .add ⟨(-20639772865679317811/590295810358705651712:ℚ),(-165118182925434542437/4722366482869645213696:ℚ)⟩ node3629 node3631
def node3633 : BoxExpr 3 := .add ⟨(78399525849617143893/2361183241434822606848:ℚ),(156799051699234287953/4722366482869645213696:ℚ)⟩ node3632 node409
def node3634 : BoxExpr 3 := .add ⟨(-249665151822612712653/590295810358705651712:ℚ),(-998660607290450850611/2361183241434822606848:ℚ)⟩ node3590 node3590
def node3635 : BoxExpr 3 := .neg ⟨(998660607290450850611/2361183241434822606848:ℚ),(249665151822612712653/590295810358705651712:ℚ)⟩ node3634
def node3636 : BoxExpr 3 := .mul ⟨(4615563041490917719615/2361183241434822606848:ℚ),(4615563041490917719617/2361183241434822606848:ℚ)⟩ node86 node3605
def node3637 : BoxExpr 3 := .inv ⟨(2415820669987755540755/4722366482869645213696:ℚ),(2415820669987755540757/4722366482869645213696:ℚ)⟩ node3636
def node3638 : BoxExpr 3 := .mul ⟨(255442366252855694507/1180591620717411303424:ℚ),(510884732505711389015/2361183241434822606848:ℚ)⟩ node3635 node3637
def node3639 : BoxExpr 3 := .mul ⟨(632833877813446140521/1180591620717411303424:ℚ),(632833877813446140523/1180591620717411303424:ℚ)⟩ node50 node3638
def node3640 : BoxExpr 3 := .add ⟨(2951552590011355622331/2361183241434822606848:ℚ),(5903105180022711244671/4722366482869645213696:ℚ)⟩ node3639 node335
def node3641 : BoxExpr 3 := .mul ⟨(-440300722609354860135/2361183241434822606848:ℚ),(-220150361304677430067/1180591620717411303424:ℚ)⟩ node422 node3608
def node3642 : BoxExpr 3 := .mul ⟨(-440300722609354860135/2361183241434822606848:ℚ),(-220150361304677430067/1180591620717411303424:ℚ)⟩ node3608 node422
def node3643 : BoxExpr 3 := .add ⟨(-440300722609354860135/1180591620717411303424:ℚ),(-220150361304677430067/590295810358705651712:ℚ)⟩ node3641 node3642
def node3644 : BoxExpr 3 := .mul ⟨(-1454753587501308457887/4722366482869645213696:ℚ),(-727376793750654228941/2361183241434822606848:ℚ)⟩ node3643 node340
def node3645 : BoxExpr 3 := .add ⟨(4448351592521402786775/4722366482869645213696:ℚ),(4448351592521402786789/4722366482869645213696:ℚ)⟩ node3640 node3644
def node3646 : BoxExpr 3 := .neg ⟨(-4448351592521402786789/4722366482869645213696:ℚ),(-4448351592521402786775/4722366482869645213696:ℚ)⟩ node3645
def node3647 : BoxExpr 3 := .add ⟨(27537054679115813405/2361183241434822606848:ℚ),(55074109358231626843/4722366482869645213696:ℚ)⟩ node414 node3646
def node3648 : BoxExpr 3 := .mul ⟨(551542014659792705129/295147905179352825856:ℚ),(8875307746185984898251/4722366482869645213696:ℚ)⟩ node112 node3565
def node3649 : BoxExpr 3 := .mul ⟨(10480922926269290949041/4722366482869645213696:ℚ),(5290614479516181168287/2361183241434822606848:ℚ)⟩ node3648 node304
def node3650 : BoxExpr 3 := .add ⟨(5451783461283018777941/1180591620717411303424:ℚ),(44907578571693180750855/4722366482869645213696:ℚ)⟩ node3649 node448
def node3651 : BoxExpr 3 := .mul ⟨(5675973908537586965049/1180591620717411303424:ℚ),(22713223276204299965835/4722366482869645213696:ℚ)⟩ node111 node3578
def node3652 : BoxExpr 3 := .neg ⟨(-22713223276204299965835/4722366482869645213696:ℚ),(-5675973908537586965049/1180591620717411303424:ℚ)⟩ node3651
def node3653 : BoxExpr 3 := .add ⟨(-906089431072224854071/4722366482869645213696:ℚ),(22203682937542832890659/4722366482869645213696:ℚ)⟩ node3650 node3652
def node3654 : BoxExpr 3 := .mul ⟨(-545855667460646948679/4722366482869645213696:ℚ),(-512288540441136808987/4722366482869645213696:ℚ)⟩ node131 node3565
def node3655 : BoxExpr 3 := .mul ⟨(-582894262183199846187/4722366482869645213696:ℚ),(-549823391477153967741/4722366482869645213696:ℚ)⟩ node118 node3563
def node3656 : BoxExpr 3 := .add ⟨(-564374964821923397433/2361183241434822606848:ℚ),(-132763991489786347091/590295810358705651712:ℚ)⟩ node3654 node3655
def node3657 : BoxExpr 3 := .mul ⟨(-1345706738809790462925/4722366482869645213696:ℚ),(-630726728518875437705/2361183241434822606848:ℚ)⟩ node3656 node304
def node3658 : BoxExpr 3 := .mul ⟨(270747565275724206791/1180591620717411303424:ℚ),(1142456249533722472167/4722366482869645213696:ℚ)⟩ node118 node3565
def node3659 : BoxExpr 3 := .mul ⟨(1214562048404093616953/4722366482869645213696:ℚ),(1304026401171267050779/4722366482869645213696:ℚ)⟩ node3658 node461
def node3660 : BoxExpr 3 := .add ⟨(-32786172601424211493/1180591620717411303424:ℚ),(42572944133516175369/4722366482869645213696:ℚ)⟩ node3657 node3659
def node3661 : BoxExpr 3 := .add ⟨(-2888445415300167687931/4722366482869645213696:ℚ),(1456146824705175948273/4722366482869645213696:ℚ)⟩ node3660 node476
def node3662 : BoxExpr 3 := .add ⟨(-435/1024:ℚ),(-497139752786472416051/1180591620717411303424:ℚ)⟩ node3563 node3563
def node3663 : BoxExpr 3 := .neg ⟨(497139752786472416051/1180591620717411303424:ℚ),(435/1024:ℚ)⟩ node3662
def node3664 : BoxExpr 3 := .mul ⟨(288413308360649744159/147573952589676412928:ℚ),(4616508795976483732893/2361183241434822606848:ℚ)⟩ node86 node3578
def node3665 : BoxExpr 3 := .inv ⟨(301915719541772942189/590295810358705651712:ℚ),(2416318065956365234295/4722366482869645213696:ℚ)⟩ node3664
def node3666 : BoxExpr 3 := .mul ⟨(508539290103173799499/2361183241434822606848:ℚ),(1026463240909198121991/4722366482869645213696:ℚ)⟩ node3663 node3665
def node3667 : BoxExpr 3 := .mul ⟨(153527291039388894529/1180591620717411303424:ℚ),(162519197640969018303/1180591620717411303424:ℚ)⟩ node117 node3666
def node3668 : BoxExpr 3 := .neg ⟨(-162519197640969018303/1180591620717411303424:ℚ),(-153527291039388894529/1180591620717411303424:ℚ)⟩ node3667
def node3669 : BoxExpr 3 := .add ⟨(582853801542487902735/4722366482869645213696:ℚ),(349792991285852561805/2361183241434822606848:ℚ)⟩ node479 node3668
def node3670 : BoxExpr 3 := .add ⟨(-1444222707650083843965/2361183241434822606848:ℚ),(1456146824705175948273/4722366482869645213696:ℚ)⟩ node3660 node492
def node3671 : BoxExpr 3 := .mul ⟨(-2019830508227540368727/4722366482869645213696:ℚ),(-491691325297160329203/1180591620717411303424:ℚ)⟩ node175 node3565
def node3672 : BoxExpr 3 := .mul ⟨(234184355168836238681/1180591620717411303424:ℚ),(968344011503439602463/4722366482869645213696:ℚ)⟩ node148 node3563
def node3673 : BoxExpr 3 := .add ⟨(-1083093087552195414003/4722366482869645213696:ℚ),(-998421289685201714349/4722366482869645213696:ℚ)⟩ node3671 node3672
def node3674 : BoxExpr 3 := .add ⟨(-146355666876850459279/4722366482869645213696:ℚ),(-15038639090881055943/2361183241434822606848:ℚ)⟩ node3673 node3672
def node3675 : BoxExpr 3 := .mul ⟨(-87243330877248641929/2361183241434822606848:ℚ),(-8930576288730737981/1180591620717411303424:ℚ)⟩ node3674 node304
def node3676 : BoxExpr 3 := .mul ⟨(-1897926844393879987427/4722366482869645213696:ℚ),(-1845097024840201043731/4722366482869645213696:ℚ)⟩ node148 node3565
def node3677 : BoxExpr 3 := .mul ⟨(-529723767701678619921/1180591620717411303424:ℚ),(-1042921967721689596113/2361183241434822606848:ℚ)⟩ node36 node3563
def node3678 : BoxExpr 3 := .add ⟨(-4016821915200594467111/4722366482869645213696:ℚ),(-3930940960283580235957/4722366482869645213696:ℚ)⟩ node3676 node3677
def node3679 : BoxExpr 3 := .mul ⟨(-2292447447489889042111/2361183241434822606848:ℚ),(-1102127109623185820131/1180591620717411303424:ℚ)⟩ node3678 node461
def node3680 : BoxExpr 3 := .add ⟨(-297461347295892210505/295147905179352825856:ℚ),(-34720552684747392441/36893488147419103232:ℚ)⟩ node3675 node3679
def node3681 : BoxExpr 3 := .mul ⟨(20259479210290568044657/4722366482869645213696:ℚ),(20917111229729591260341/4722366482869645213696:ℚ)⟩ node3566 node514
def node3682 : BoxExpr 3 := .add ⟨(15674584315310789960435/4722366482869645213696:ℚ),(16508602791236847979817/4722366482869645213696:ℚ)⟩ node3679 node3681
def node3683 : BoxExpr 3 := .add ⟨(10915202758576514592355/4722366482869645213696:ℚ),(12064372047589181747369/4722366482869645213696:ℚ)⟩ node3680 node3682
def node3684 : BoxExpr 3 := .mul ⟨(504993240777281333/590295810358705651712:ℚ),(5718453063990241153/4722366482869645213696:ℚ)⟩ node3569 node189
def node3685 : BoxExpr 3 := .add ⟨(-3082399984555146865/295147905179352825856:ℚ),(-46807819007640544781/4722366482869645213696:ℚ)⟩ node518 node3684
def node3686 : BoxExpr 3 := .add ⟨(-12834593178997868793/590295810358705651712:ℚ),(-99334091079271330715/4722366482869645213696:ℚ)⟩ node518 node3685
def node3687 : BoxExpr 3 := .add ⟨(10812526013144531642011/4722366482869645213696:ℚ),(5982518978254955208327/2361183241434822606848:ℚ)⟩ node3683 node3686
def node3688 : BoxExpr 3 := .add ⟨(10958129645755551506767/2361183241434822606848:ℚ),(28558508995837356891197/4722366482869645213696:ℚ)⟩ node3687 node527
def node3689 : BoxExpr 3 := .mul ⟨(-2416318065956365234295/2361183241434822606848:ℚ),(-301915719541772942189/295147905179352825856:ℚ)⟩ node6 node3665
def node3690 : BoxExpr 3 := .mul ⟨(508539290103173799499/1180591620717411303424:ℚ),(1026463240909198121991/2361183241434822606848:ℚ)⟩ node86 node3666
def node3691 : BoxExpr 3 := .mul ⟨(18037272291989398749179/4722366482869645213696:ℚ),(18052096160378866379003/4722366482869645213696:ℚ)⟩ node3664 node3664
def node3692 : BoxExpr 3 := .inv ⟨(1235354886236246855279/4722366482869645213696:ℚ),(618185079138454085375/2361183241434822606848:ℚ)⟩ node3691
def node3693 : BoxExpr 3 := .mul ⟨(133032135297198063939/1180591620717411303424:ℚ),(537479894553692114421/4722366482869645213696:ℚ)⟩ node3690 node3692
def node3694 : BoxExpr 3 := .neg ⟨(-537479894553692114421/4722366482869645213696:ℚ),(-133032135297198063939/1180591620717411303424:ℚ)⟩ node3693
def node3695 : BoxExpr 3 := .mul ⟨(-114161989321707065319/2361183241434822606848:ℚ),(-224076002891217988947/4722366482869645213696:ℚ)⟩ node3663 node3694
def node3696 : BoxExpr 3 := .add ⟨(-1265240027639036149807/1180591620717411303424:ℚ),(-5054727515559585063971/4722366482869645213696:ℚ)⟩ node3689 node3695
def node3697 : BoxExpr 3 := .mul ⟨(-12547545120243124573857/4722366482869645213696:ℚ),(-12513332934788699330877/4722366482869645213696:ℚ)⟩ node11 node3696
def node3698 : BoxExpr 3 := .add ⟨(-18539826916181526097/18446744073709551616:ℚ),(-4711983505088045437851/4722366482869645213696:ℚ)⟩ node3697 node546
def node3699 : BoxExpr 3 := .neg ⟨(4711983505088045437851/4722366482869645213696:ℚ),(18539826916181526097/18446744073709551616:ℚ)⟩ node3698
def cert_iv23 : TaylorCertificate3Reduced :=
  { center := ![(264769627/131072000:ℚ), (32729/81920:ℚ), (-4331/20480:ℚ)], radius := ![(3/1000:ℚ), (1/500:ℚ), (19/20480:ℚ)],
    whole := node3589, centerValue := node3616, gradient := ![node3623, node3633, node3647],
    hessian := ![![node3653, node3661, node3669], ![node3670, node3688, node536], ![node3669, node536, node3699]] }

end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part6
end

section
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646CheckB4Part6
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part6

theorem cert_iv20_check : cert_iv20.check = true := by decide +kernel

theorem cert_iv20_lower_pos : 0 < cert_iv20.lower := by decide +kernel

theorem positive_iv20 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(279/1280:ℝ)) ≤ r) (hrhi : r ≤ (-(2213/10240:ℝ))) :
    0 < node3178.eval ![A,ρ,r] := by
  apply cert_iv20.positive_sound cert_iv20_check cert_iv20_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv20,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv20,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv20,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv21_check : cert_iv21.check = true := by decide +kernel

theorem cert_iv21_lower_pos : 0 < cert_iv21.lower := by decide +kernel

theorem positive_iv21 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(2213/10240:ℝ)) ≤ r) (hrhi : r ≤ (-(1097/5120:ℝ))) :
    0 < node3315.eval ![A,ρ,r] := by
  apply cert_iv21.positive_sound cert_iv21_check cert_iv21_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv21,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv21,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv21,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv22_check : cert_iv22.check = true := by decide +kernel

theorem cert_iv22_lower_pos : 0 < cert_iv22.lower := by decide +kernel

theorem positive_iv22 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(1097/5120:ℝ)) ≤ r) (hrhi : r ≤ (-(435/2048:ℝ))) :
    0 < node3452.eval ![A,ρ,r] := by
  apply cert_iv22.positive_sound cert_iv22_check cert_iv22_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv22,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv22,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv22,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

theorem cert_iv23_check : cert_iv23.check = true := by decide +kernel

theorem cert_iv23_lower_pos : 0 < cert_iv23.lower := by decide +kernel

theorem positive_iv23 (A ρ r : ℝ)
    (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(435/2048:ℝ)) ≤ r) (hrhi : r ≤ (-(539/2560:ℝ))) :
    0 < node3589.eval ![A,ρ,r] := by
  apply cert_iv23.positive_sound cert_iv23_check cert_iv23_lower_pos ![A,ρ,r]
  intro i
  fin_cases i
  · norm_num [cert_iv23,Matrix.cons_val_two]
    exact ⟨hAlo,hAhi⟩
  · norm_num [cert_iv23,Matrix.cons_val_two]
    exact ⟨hρlo,hρhi⟩
  · norm_num [cert_iv23,Matrix.cons_val_two]
    exact ⟨hrlo,hrhi⟩

end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SplitDataB4Part6
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
-- Source module: Solutions.GaussLocalMaxCase1FamilyAdaptive0Seed25646BoundB4Part6
set_option autoImplicit false
set_option maxHeartbeats 50000000
namespace GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part6
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate.CapacityCore
noncomputable section
namespace Parameters
def b : ℚ := (103531361122339324647880530522418473224550678173/6474633415922124204664207433178390079472570088576:ℚ)
def c : ℚ := (148022665013912365111/4722366482869645213696:ℚ)
def theta : ℚ := (105113898053531722649817636563532003778556764000751/182628568201966125342452015454275643968150995402752:ℚ)
end Parameters

theorem iv_shape20 : SplitDataB4Part6.node3178.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound20 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(279/1280:ℝ)) ≤ r) (hrhi : r ≤ (-(2213/10240:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part6.node3178 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape20 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part6.positive_iv20 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part6.node3178.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape21 : SplitDataB4Part6.node3315.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound21 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(2213/10240:ℝ)) ≤ r) (hrhi : r ≤ (-(1097/5120:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part6.node3315 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape21 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part6.positive_iv21 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part6.node3315.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape22 : SplitDataB4Part6.node3452.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound22 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(1097/5120:ℝ)) ≤ r) (hrhi : r ≤ (-(435/2048:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part6.node3452 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape22 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part6.positive_iv22 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part6.node3452.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem iv_shape23 : SplitDataB4Part6.node3589.formula.canonicalize = (ThinConstructiveSyntax.gap 3 4 0 Parameters.b Parameters.c Parameters.theta (-1)).canonicalize := by decide +kernel

theorem iv_bound23 (A ρ r : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ))
    (hrlo : (-(435/2048:ℝ)) ≤ r) (hrhi : r ≤ (-(539/2560:ℝ))) : fA A r+3/10^6 ≤ l40SignedLhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) (-1) r := by
  have hf : sourceFADomain 3 ρ := by
    norm_num [sourceFADomain] <;> linarith
  have hk : sourceFADomain 0 r := by
    norm_num [sourceFADomain] <;> linarith
  have hbase : 0 < 1-ρ^2 := by nlinarith
  have he := ThinConstructiveSyntax.reflect_gap SplitDataB4Part6.node3589 3 4 0
    Parameters.b Parameters.c Parameters.theta (-1) iv_shape23 A ρ r hf hk hbase
  norm_num only [Rat.cast_neg,Rat.cast_one] at he
  have hp := SplitDataB4Part6.positive_iv23 A ρ r hAlo hAhi hρlo hρhi hrlo hrhi
  change 0 < SplitDataB4Part6.node3589.eval (ThinConstructiveSyntax.point A ρ r) at hp
  rw [he] at hp
  linarith only [hp]

theorem actual_bound (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (r : ℝ)
    (hrlo : (-(279/1280:ℝ)) ≤ r) (hrhi : r ≤ (-(539/2560:ℝ))) : fA A r+3/10^6 ≤ l40Lhs A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ) (Parameters.theta:ℝ) r := by
  have hc : 0 ≤ (Parameters.c:ℝ) := by norm_num [Parameters.c]
  have hθ : 0 ≤ (Parameters.theta:ℝ) := by norm_num [Parameters.theta]
  by_cases h0 : r ≤ (-(2213/10240:ℝ))
  · have h := iv_bound20 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  by_cases h1 : r ≤ (-(1097/5120:ℝ))
  · have h := iv_bound21 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  by_cases h2 : r ≤ (-(435/2048:ℝ))
  · have h := iv_bound22 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
    exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
      (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
  have h := iv_bound23 A ρ r hAlo hAhi hρlo hρhi (by linarith) (by linarith)
  exact h.trans (l40SignedLhs_le A ρ (fA A ρ/Real.sqrt (1-ρ^2)) (constructedA (Parameters.b:ℝ) (constructedMu (fA A ρ/Real.sqrt (1-ρ^2)) (thresholdCapacity 4 ρ+1/4) (Parameters.c:ℝ) (Parameters.theta:ℝ))) (Parameters.b:ℝ) (Parameters.c:ℝ)
    (Parameters.theta:ℝ) (-1) r hθ hc (Or.inl rfl))
end
end GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part6
end

section
-- Source module: Solutions.Sol_GaussLocalMaxCase1FamilyAdaptive0Seed25646B4Part6
set_option autoImplicit false
open GaussLocalMaxColoring.Main
open GaussLocalMaxColoring.Certificate
open GaussLocalMaxColoring.Certificate.CapacityCore
theorem solution (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (r : ℝ)
    (hrlo : (-(279/1280:ℝ)) ≤ r) (hrhi : r ≤ (-(539/2560:ℝ))) :
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
  have h := GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part6.actual_bound A ρ hAlo hAhi hρlo hρhi r hrlo hrhi
  simpa only [Case2Static,constructedA,constructedMu,constructedMass,constructedKappa,thresholdCapacity,
    GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part6.Parameters.b,GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part6.Parameters.c,GaussLocalMaxColoring.Certificate.Case1Constructive.CellAdaptive0Seed25646.SubmissionB4Part6.Parameters.theta,
    show ¬ (4:ℕ)=1 by decide,show ¬ (4:ℕ)=2 by decide,show ¬ (4:ℕ)=3 by decide,ite_false,and_assoc] using h
end

#print axioms solution
