-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_61_branch_2
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T09:50:33.272123+00:00
-- url     : https://prove2.me/submissions/1d51f75e-745b-45fc-b70b-b0bb39a167a9

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Bands


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

#print axioms CertificateFormula.hasDerivAt_eval
#print axioms CertificateFormula.regular_pdiff
#print axioms BoxExpr.check_regular
#print axioms CertificateFormula.hasDerivAt_line_gradient
#print axioms BoxExpr.checked_line_derivatives

end GaussLocalMaxColoring.Certificate


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

#print axioms lower_sound
#print axioms positive_sound

end TaylorCertificate1
end GaussLocalMaxColoring.Certificate

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace GaussLocalMaxColoring.Certificate

def certFgtBox : Fin 3→RatInterval := ![⟨(43/20:ℚ),(43/20:ℚ)⟩,⟨(155606922197/8000003688788:ℚ),(1/50:ℚ)⟩,⟨0,0⟩]

def certFgtNode0 : BoxExpr 3 := .lit (3/1:ℚ)
def certFgtNode1 : BoxExpr 3 := .sqrt ⟨(8179378680290567732005/4722366482869645213696:ℚ),(4089689340145283866003/2361183241434822606848:ℚ)⟩ certFgtNode0
def certFgtNode2 : BoxExpr 3 := .lit (2/1:ℚ)
def certFgtNode3 : BoxExpr 3 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ certFgtNode2
def certFgtNode4 : BoxExpr 3 := .mul ⟨(2044844670072641933001/2361183241434822606848:ℚ),(4089689340145283866003/4722366482869645213696:ℚ)⟩ certFgtNode1 certFgtNode3
def certFgtNode5 : BoxExpr 3 := .lit (1462052672197/307399000000:ℚ)
def certFgtNode6 : BoxExpr 3 := .sqrt ⟨(5149439693892759156103/2361183241434822606848:ℚ),(10298879387785518312207/4722366482869645213696:ℚ)⟩ certFgtNode5
def certFgtNode7 : BoxExpr 3 := .var ⟨0,by decide⟩
def certFgtNode8 : BoxExpr 3 := .var ⟨1,by decide⟩
def certFgtNode9 : BoxExpr 3 := .lit (13/25:ℚ)
def certFgtNode10 : BoxExpr 3 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ certFgtNode7 certFgtNode9
def certFgtNode11 : BoxExpr 3 := .lit (713/500:ℚ)
def certFgtNode12 : BoxExpr 3 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ certFgtNode10 certFgtNode11
def certFgtNode13 : BoxExpr 3 := .lit (2/1:ℚ)
def certFgtNode14 : BoxExpr 3 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ certFgtNode13
def certFgtNode15 : BoxExpr 3 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ certFgtNode7 certFgtNode14
def certFgtNode16 : BoxExpr 3 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ certFgtNode15 certFgtNode15
def certFgtNode17 : BoxExpr 3 := .lit (123/50:ℚ)
def certFgtNode18 : BoxExpr 3 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ certFgtNode16 certFgtNode17
def certFgtNode19 : BoxExpr 3 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ certFgtNode12 certFgtNode18
def certFgtNode20 : BoxExpr 3 := .mul ⟨(223330044160487951/590295810358705651712:ℚ),(944473296573929043/2361183241434822606848:ℚ)⟩ certFgtNode8 certFgtNode8
def certFgtNode21 : BoxExpr 3 := .lit (1/1:ℚ)
def certFgtNode22 : BoxExpr 3 := .neg ⟨(-944473296573929043/2361183241434822606848:ℚ),(-223330044160487951/590295810358705651712:ℚ)⟩ certFgtNode20
def certFgtNode23 : BoxExpr 3 := .add ⟨(2360238768138248677805/2361183241434822606848:ℚ),(590072480314545163761/590295810358705651712:ℚ)⟩ certFgtNode21 certFgtNode22
def certFgtNode24 : BoxExpr 3 := .sqrt ⟨(4721421915106847437639/4722366482869645213696:ℚ),(590184134772907823743/590295810358705651712:ℚ)⟩ certFgtNode23
def certFgtNode25 : BoxExpr 3 := .mul ⟨(6136314027516491943511/2361183241434822606848:ℚ),(1534095130721957951647/590295810358705651712:ℚ)⟩ certFgtNode19 certFgtNode24
def certFgtNode26 : BoxExpr 3 := .mul ⟨(31894474925558266639649/4722366482869645213696:ℚ),(3986895771248485077271/590295810358705651712:ℚ)⟩ certFgtNode25 certFgtNode25
def certFgtNode27 : BoxExpr 3 := .mul ⟨(223330044160487951/590295810358705651712:ℚ),(944473296573929043/2361183241434822606848:ℚ)⟩ certFgtNode8 certFgtNode8
def certFgtNode28 : BoxExpr 3 := .lit (1/1:ℚ)
def certFgtNode29 : BoxExpr 3 := .neg ⟨(-944473296573929043/2361183241434822606848:ℚ),(-223330044160487951/590295810358705651712:ℚ)⟩ certFgtNode27
def certFgtNode30 : BoxExpr 3 := .add ⟨(2360238768138248677805/2361183241434822606848:ℚ),(590072480314545163761/590295810358705651712:ℚ)⟩ certFgtNode28 certFgtNode29
def certFgtNode31 : BoxExpr 3 := .lit (2/1:ℚ)
def certFgtNode32 : BoxExpr 3 := .mul ⟨(45927035940963706679/1180591620717411303424:ℚ),(47223664828696452137/1180591620717411303424:ℚ)⟩ certFgtNode8 certFgtNode31
def certFgtNode33 : BoxExpr 3 := .lit (1/1:ℚ)
def certFgtNode34 : BoxExpr 3 := .add ⟨(1226518656658375010103/1180591620717411303424:ℚ),(1227815285546107755561/1180591620717411303424:ℚ)⟩ certFgtNode32 certFgtNode33
def certFgtNode35 : BoxExpr 3 := .lit (7033791386230630914920427/47247072600500000000000:ℚ)
def certFgtNode36 : BoxExpr 3 := .inv ⟨(2270368501379637121969/2361183241434822606848:ℚ),(4545537297265527791021/4722366482869645213696:ℚ)⟩ certFgtNode34
def certFgtNode37 : BoxExpr 3 := .mul ⟨(84498877547412535956229/590295810358705651712:ℚ),(169176413095686585091777/1180591620717411303424:ℚ)⟩ certFgtNode35 certFgtNode36
def certFgtNode38 : BoxExpr 3 := .lit (1/1:ℚ)
def certFgtNode39 : BoxExpr 3 := .add ⟨(85089173357771241607941/590295810358705651712:ℚ),(170357004716403996395201/1180591620717411303424:ℚ)⟩ certFgtNode37 certFgtNode38
def certFgtNode40 : BoxExpr 3 := .sqrt ⟨(28348624669278885422223/2361183241434822606848:ℚ),(14181750678202711778193/1180591620717411303424:ℚ)⟩ certFgtNode39
def certFgtNode41 : BoxExpr 3 := .lit (1/1:ℚ)
def certFgtNode42 : BoxExpr 3 := .add ⟨(30709807910713708029071/2361183241434822606848:ℚ),(15362342298920123081617/1180591620717411303424:ℚ)⟩ certFgtNode40 certFgtNode41
def certFgtNode43 : BoxExpr 3 := .lit (2/1:ℚ)
def certFgtNode44 : BoxExpr 3 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ certFgtNode43
def certFgtNode45 : BoxExpr 3 := .mul ⟨(30709807910713708029071/4722366482869645213696:ℚ),(15362342298920123081617/2361183241434822606848:ℚ)⟩ certFgtNode42 certFgtNode44
def certFgtNode46 : BoxExpr 3 := .lit (1/4:ℚ)
def certFgtNode47 : BoxExpr 3 := .add ⟨(31890399531431119332495/4722366482869645213696:ℚ),(15952638109278828733329/2361183241434822606848:ℚ)⟩ certFgtNode45 certFgtNode46
def certFgtNode48 : BoxExpr 3 := .mul ⟨(15938821685809273442379/2361183241434822606848:ℚ),(31893205310003329180735/4722366482869645213696:ℚ)⟩ certFgtNode30 certFgtNode47
def certFgtNode49 : BoxExpr 3 := .neg ⟨(-31893205310003329180735/4722366482869645213696:ℚ),(-15938821685809273442379/2361183241434822606848:ℚ)⟩ certFgtNode48
def certFgtNode50 : BoxExpr 3 := .add ⟨(634807777468729457/2361183241434822606848:ℚ),(8761399184666866705/2361183241434822606848:ℚ)⟩ certFgtNode26 certFgtNode49
theorem certFgtCheck0 : (certFgtNode25).check certFgtBox=true := by decide +kernel
theorem certFgtPositive0 (x : Fin 3→ℝ) (hx : ∀i,(certFgtBox i).Contains (x i)) : 0<(certFgtNode25).eval x := by
  have h := BoxExpr.check_sound certFgtNode25 certFgtBox x hx certFgtCheck0
  have hlo : (0:ℝ)<(certFgtNode25.bounds certFgtBox).lo := by norm_num [certFgtNode25,BoxExpr.bounds]
  exact hlo.trans_le h.1
#print axioms certFgtPositive0
theorem certFgtCheck1 : (certFgtNode50).check certFgtBox=true := by decide +kernel
theorem certFgtPositive1 (x : Fin 3→ℝ) (hx : ∀i,(certFgtBox i).Contains (x i)) : 0<(certFgtNode50).eval x := by
  have h := BoxExpr.check_sound certFgtNode50 certFgtBox x hx certFgtCheck1
  have hlo : (0:ℝ)<(certFgtNode50.bounds certFgtBox).lo := by norm_num [certFgtNode50,BoxExpr.bounds]
  exact hlo.trans_le h.1
#print axioms certFgtPositive1
end GaussLocalMaxColoring.Certificate


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


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace GaussLocalMaxColoring.Certificate
open GaussLocalMaxColoring.Main
noncomputable section

def certFgtPoint (ρ : ℝ) : Fin 3 → ℝ := ![43/20, ρ, 0]

theorem certFgtPoint_contains (ρ : ℝ)
    (hlo : (155606922197/8000003688788 : ℝ) ≤ ρ) (hhi : ρ ≤ 1/50) :
    ∀ i, (certFgtBox i).Contains (certFgtPoint ρ i) := by
  intro i
  fin_cases i <;> norm_num [certFgtBox, certFgtPoint, RatInterval.Contains]
  exact ⟨hlo, hhi⟩

theorem certFgtNode25_eval (ρ : ℝ) :
    certFgtNode25.eval (certFgtPoint ρ) =
      (51987/20000 : ℝ) * Real.sqrt (1 - ρ^2) := by
  norm_num [certFgtNode25, certFgtNode24, certFgtNode23, certFgtNode22,
    certFgtNode21, certFgtNode20, certFgtNode19, certFgtNode18, certFgtNode17,
    certFgtNode16, certFgtNode15, certFgtNode14, certFgtNode13, certFgtNode12,
    certFgtNode11, certFgtNode10, certFgtNode9, certFgtNode8, certFgtNode7,
    BoxExpr.eval, certFgtPoint, pow_two, sub_eq_add_neg]

theorem certFgtNode50_eval (ρ : ℝ) :
    certFgtNode50.eval (certFgtPoint ρ) =
      (certFgtNode25.eval (certFgtPoint ρ))^2 -
        (1 - ρ^2) * (((1 + Real.sqrt (1 + 6*Da*(Da+1)/(1+2*ρ)))/2) + 1/4) := by
  norm_num [certFgtNode50, certFgtNode49, certFgtNode48, certFgtNode47,
    certFgtNode46, certFgtNode45, certFgtNode44, certFgtNode43, certFgtNode42,
    certFgtNode41, certFgtNode40, certFgtNode39, certFgtNode38, certFgtNode37,
    certFgtNode36, certFgtNode35, certFgtNode34, certFgtNode33, certFgtNode32,
    certFgtNode31, certFgtNode30, certFgtNode29, certFgtNode28, certFgtNode27,
    certFgtNode26, certFgtNode8, BoxExpr.eval, certFgtPoint, Da, D5, beta5, eta5,
    pow_two, div_eq_mul_inv, sub_eq_add_neg]
  left
  have h : ρ * 2 + 1 = 1 + 2 * ρ := by ring
  rw [h, add_comm (_ * _) 1]
  exact add_comm _ _

theorem certFgt_fA_eval (ρ : ℝ)
    (hlo : (155606922197/8000003688788 : ℝ) ≤ ρ) (hhi : ρ ≤ 1/50) :
    fA (43/20) ρ = certFgtNode25.eval (certFgtPoint ρ) := by
  have hρ : 0 < ρ := (by norm_num : (0:ℝ) < 155606922197/8000003688788).trans_le hlo
  have hz1 : max (-(1/40 : ℝ) - ρ) 0 = 0 := max_eq_right (by linarith)
  have hz2 : max (ρ - (1/50 : ℝ)) 0 = 0 := max_eq_right (by linarith)
  have hz3 : max (ρ - (1/4 : ℝ)) 0 = 0 := max_eq_right (by linarith)
  rw [certFgtNode25_eval]
  norm_num [fA, ftilde, hz1, hz2, hz3]

/-- One complete original interval certificate, interpreted using the public thresholds.
The rational endpoints and A=2.15 are the source certificate's unchanged data. -/
theorem certFgt_public_threshold (ρ : ℝ)
    (hlo : (155606922197/8000003688788 : ℝ) ≤ ρ) (hhi : ρ ≤ 1/50) :
    qc ρ < fA (43/20) ρ := by
  have hx := certFgtPoint_contains ρ hlo hhi
  have hf := certFgtPositive0 (certFgtPoint ρ) hx
  have hgap := certFgtPositive1 (certFgtPoint ρ) hx
  rw [certFgtNode50_eval] at hgap
  rw [← certFgt_fA_eval ρ hlo hhi] at hf hgap
  have hρ : 0 < ρ := (by norm_num : (0:ℝ) < 155606922197/8000003688788).trans_le hlo
  have hρ4 : ρ ≤ (1/4 : ℝ) := by linarith
  have hbase : 0 ≤ 1 - ρ^2 := by nlinarith
  have hDa : 0 ≤ Da := by norm_num [Da, D5, beta5, eta5]
  have hcap := capacity_ge_add_one Da ρ hDa (show ρ ∈ Set.Icc (-(1/2):ℝ) 1 by constructor <;> linarith)
  have hrad : 0 ≤ (1 - ρ^2) * (capacity Da ρ + 1/4) := by
    apply mul_nonneg hbase
    linarith
  have hupper : capacity Da ρ ≤ (1 + Real.sqrt (1 + 6*Da*(Da+1)/(1+2*ρ)))/2 := by
    simp only [capacity, if_neg (not_le.mpr hρ), if_pos hρ4]
    exact min_le_right _ _
  have hsq : (qc ρ)^2 ≤
      (1 - ρ^2) * (((1 + Real.sqrt (1 + 6*Da*(Da+1)/(1+2*ρ)))/2) + 1/4) := by
    rw [qc, Real.sq_sqrt hrad]
    exact mul_le_mul_of_nonneg_left (by linarith) hbase
  have hqc : 0 ≤ qc ρ := Real.sqrt_nonneg _
  nlinarith

theorem certFgt_qA_eq_qc (ρ : ℝ)
    (hlo : (155606922197/8000003688788 : ℝ) ≤ ρ) (hhi : ρ ≤ 1/50) :
    qA (43/20) ρ = qc ρ := by
  exact min_eq_left (le_of_lt (certFgt_public_threshold ρ hlo hhi))

theorem ftilde_monotoneOn : MonotoneOn ftilde (Set.Ici (1968/1000:ℝ)) := by
  intro a ha b hb hab
  change (1968/1000:ℝ) ≤ a at ha
  change (1968/1000:ℝ) ≤ b at hb
  have hfactor : 0 ≤ 52/100 + (246/100:ℝ)*(a+b-4) := by
    linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hab) hfactor
  have heq : ftilde b - ftilde a =
      (b-a) * (52/100 + (246/100:ℝ)*(a+b-4)) := by
    unfold ftilde
    ring
  exact sub_nonneg.mp (heq.symm ▸ hprod)

/-- Property (P1) of the original thresholds, on the paper's full A-range. -/
theorem fA_monotoneOn (ρ : ℝ) :
    MonotoneOn (fun A => fA A ρ) (Set.Ici (1968/1000:ℝ)) := by
  intro a ha b hb hab
  have h := mul_le_mul_of_nonneg_right (ftilde_monotoneOn ha hb hab)
    (Real.sqrt_nonneg (1-ρ^2))
  dsimp only [fA]
  linarith only [h]

theorem qA_monotoneOn (ρ : ℝ) :
    MonotoneOn (fun A => qA A ρ) (Set.Ici (1968/1000:ℝ)) := by
  intro a ha b hb hab
  exact min_le_min_left (qc ρ) (fA_monotoneOn ρ ha hb hab)

theorem certFgt_public_threshold_of_le (A ρ : ℝ) (hA : (43/20:ℝ) ≤ A)
    (hlo : (155606922197/8000003688788 : ℝ) ≤ ρ) (hhi : ρ ≤ 1/50) :
    qc ρ < fA A ρ := by
  apply (certFgt_public_threshold ρ hlo hhi).trans_le
  exact fA_monotoneOn ρ (by norm_num) (by change (1968/1000:ℝ) ≤ A; linarith) hA

theorem certFgt_qA_eq_qc_of_le (A ρ : ℝ) (hA : (43/20:ℝ) ≤ A)
    (hlo : (155606922197/8000003688788 : ℝ) ≤ ρ) (hhi : ρ ≤ 1/50) :
    qA A ρ = qc ρ := by
  exact min_eq_left (certFgt_public_threshold_of_le A ρ hA hlo hhi).le

#print axioms certFgt_public_threshold
#print axioms certFgt_qA_eq_qc
#print axioms fA_monotoneOn
#print axioms certFgt_qA_eq_qc_of_le

end
end GaussLocalMaxColoring.Certificate


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace GaussLocalMaxColoring.Certificate
open GaussLocalMaxColoring.Main
noncomputable section

def thresholdFA (j : ℕ) (ρ : ℝ) : ℝ :=
  let f := ftilde (43/20) * Real.sqrt (1-ρ^2)
  if j = 0 then f - 714/1000 * (-(1/40)-ρ) + 826/1000 * (-(1/40)-ρ)^2
  else if j = 1 then f
  else if j = 2 then f - 8/10 * (ρ-1/50) + 45/100 * (ρ-1/50)^2
  else f - 8/10 * (ρ-1/50) + 45/100 * (ρ-1/50)^2 +
    39/100 * (ρ-1/4) + 65/100 * (ρ-1/4)^2

def thresholdFADomain (j : ℕ) (ρ : ℝ) : Prop :=
  (j = 0 ∧ -(1/2) ≤ ρ ∧ ρ ≤ -(1/40)) ∨
  (j = 1 ∧ -(1/40) ≤ ρ ∧ ρ ≤ 1/50) ∨
  (j = 2 ∧ 1/50 ≤ ρ ∧ ρ ≤ 1/4) ∨
  (j = 3 ∧ 1/4 ≤ ρ ∧ ρ ≤ 1)

def thresholdCapacity (j : ℕ) (ρ : ℝ) : ℝ :=
  if j = 1 then (1 + Real.sqrt (1+6*Da*(Da+1)*((1-2*ρ)/(1-4*ρ))))/2
  else if j = 2 then Da+2
  else if j = 3 then (1 + Real.sqrt (1+6*Da*(Da+1)/(1+2*ρ)))/2
  else Da+1

def thresholdCapacityDomain (j : ℕ) (ρ : ℝ) : Prop :=
  (j = 1 ∧ ρ ≤ 0) ∨ (j = 2) ∨
  (j = 3 ∧ 0 ≤ ρ ∧ ρ ≤ 1/4) ∨ (j = 4 ∧ 1/4 ≤ ρ)

theorem thresholdFA_eq (j : ℕ) (ρ : ℝ) (hj : thresholdFADomain j ρ) :
    thresholdFA j ρ = fA (43/20) ρ := by
  rcases hj with ⟨rfl, hlo, hhi⟩ | ⟨rfl, hlo, hhi⟩ | ⟨rfl, hlo, hhi⟩ | ⟨rfl, hlo, hhi⟩
  · have hz1 : max (-(1/40:ℝ)-ρ) 0 = -(1/40)-ρ := max_eq_left (by linarith)
    have hz2 : max (ρ-(1/50:ℝ)) 0 = 0 := max_eq_right (by linarith)
    have hz3 : max (ρ-(1/4:ℝ)) 0 = 0 := max_eq_right (by linarith)
    norm_num [thresholdFA, fA, hz1, hz2, hz3]
  · have hz1 : max (-(1/40:ℝ)-ρ) 0 = 0 := max_eq_right (by linarith)
    have hz2 : max (ρ-(1/50:ℝ)) 0 = 0 := max_eq_right (by linarith)
    have hz3 : max (ρ-(1/4:ℝ)) 0 = 0 := max_eq_right (by linarith)
    norm_num [thresholdFA, fA, hz1, hz2, hz3]
  · have hz1 : max (-(1/40:ℝ)-ρ) 0 = 0 := max_eq_right (by linarith)
    have hz2 : max (ρ-(1/50:ℝ)) 0 = ρ-1/50 := max_eq_left (by linarith)
    have hz3 : max (ρ-(1/4:ℝ)) 0 = 0 := max_eq_right (by linarith)
    norm_num [thresholdFA, fA, hz1, hz2, hz3]
  · have hz1 : max (-(1/40:ℝ)-ρ) 0 = 0 := max_eq_right (by linarith)
    have hz2 : max (ρ-(1/50:ℝ)) 0 = ρ-1/50 := max_eq_left (by linarith)
    have hz3 : max (ρ-(1/4:ℝ)) 0 = ρ-1/4 := max_eq_left (by linarith)
    norm_num [thresholdFA, fA, hz1, hz2, hz3]

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

theorem threshold_positive_to_public (fj cj : ℕ) (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (-(1/2):ℝ) 1)
    (hfdom : thresholdFADomain fj ρ) (hcdom : thresholdCapacityDomain cj ρ)
    (hf : 0 < thresholdFA fj ρ)
    (hgap : 0 < (thresholdFA fj ρ)^2 - (1-ρ^2)*(thresholdCapacity cj ρ+1/4)) :
    qc ρ < fA (43/20) ρ := by
  rw [thresholdFA_eq fj ρ hfdom] at hf hgap
  have hbase : 0 ≤ 1-ρ^2 := by nlinarith [hρ.1, hρ.2]
  have hcap := capacity_ge_add_one Da ρ (by norm_num [Da, D5, beta5, eta5]) hρ
  have hrad : 0 ≤ (1-ρ^2)*(capacity Da ρ+1/4) := by
    apply mul_nonneg hbase
    have hDa : 0 ≤ Da := by norm_num [Da, D5, beta5, eta5]
    linarith
  have hupper := mul_le_mul_of_nonneg_left
    (add_le_add_right (thresholdCapacity_upper cj ρ hcdom) (1/4)) hbase
  have hqc : (qc ρ)^2 = (1-ρ^2)*(capacity Da ρ+1/4) := Real.sq_sqrt hrad
  have hqc0 : 0 ≤ qc ρ := Real.sqrt_nonneg _
  nlinarith

#print axioms thresholdFA_eq
#print axioms thresholdCapacity_upper
#print axioms threshold_positive_to_public

end
end GaussLocalMaxColoring.Certificate

set_option autoImplicit false
set_option maxHeartbeats 20000000
namespace GaussLocalMaxColoring.Certificate.ThresholdBranch2
open GaussLocalMaxColoring.Main

def thresholdNode0 : BoxExpr 1 := .lit (43/20:ℚ)
def thresholdNode1 : BoxExpr 1 := .lit (13/25:ℚ)
def thresholdNode2 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode3 : BoxExpr 1 := .lit (713/500:ℚ)
def thresholdNode4 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode2 thresholdNode3
def thresholdNode5 : BoxExpr 1 := .lit (2/1:ℚ)
def thresholdNode6 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode7 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode6
def thresholdNode8 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode7 thresholdNode7
def thresholdNode9 : BoxExpr 1 := .lit (123/50:ℚ)
def thresholdNode10 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode8 thresholdNode9
def thresholdNode11 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode4 thresholdNode10
def thresholdNode12 : BoxExpr 1 := .lit (1/1:ℚ)
def thresholdNode13 : BoxExpr 1 := .var 0
def thresholdNode14 : BoxExpr 1 := .mul ⟨(1888946593147858085/4722366482869645213696:ℚ),(2805749773611222801/1180591620717411303424:ℚ)⟩ thresholdNode13 thresholdNode13
def thresholdNode15 : BoxExpr 1 := .neg ⟨(-2805749773611222801/1180591620717411303424:ℚ),(-1888946593147858085/4722366482869645213696:ℚ)⟩ thresholdNode14
def thresholdNode16 : BoxExpr 1 := .add ⟨(1177785870943800080623/1180591620717411303424:ℚ),(4720477536276497355611/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode15
def thresholdNode17 : BoxExpr 1 := .sqrt ⟨(2358375822667463458973/2361183241434822606848:ℚ),(590177739388355929705/590295810358705651712:ℚ)⟩ thresholdNode16
def thresholdNode18 : BoxExpr 1 := .mul ⟨(6130244194650671142079/2361183241434822606848:ℚ),(6136314027516491943517/2361183241434822606848:ℚ)⟩ thresholdNode11 thresholdNode17
def thresholdNode19 : BoxExpr 1 := .lit (1/50:ℚ)
def thresholdNode20 : BoxExpr 1 := .neg ⟨(-47223664828696452137/2361183241434822606848:ℚ),(-94447329657392904273/4722366482869645213696:ℚ)⟩ thresholdNode19
def thresholdNode21 : BoxExpr 1 := .add ⟨(-1/4722366482869645213696:ℚ),(135768036382502299895/4722366482869645213696:ℚ)⟩ thresholdNode13 thresholdNode20
def thresholdNode22 : BoxExpr 1 := .lit (-4/5:ℚ)
def thresholdNode23 : BoxExpr 1 := .mul ⟨(-108614429106001839917/4722366482869645213696:ℚ),(1/4722366482869645213696:ℚ)⟩ thresholdNode21 thresholdNode22
def thresholdNode24 : BoxExpr 1 := .mul ⟨(-1/4722366482869645213696:ℚ),(3903331045996941123/4722366482869645213696:ℚ)⟩ thresholdNode21 thresholdNode21
def thresholdNode25 : BoxExpr 1 := .lit (9/20:ℚ)
def thresholdNode26 : BoxExpr 1 := .mul ⟨(-1/4722366482869645213696:ℚ),(878249485349311753/2361183241434822606848:ℚ)⟩ thresholdNode24 thresholdNode25
def thresholdNode27 : BoxExpr 1 := .add ⟨(-54307214553000919959/2361183241434822606848:ℚ),(1756498970698623507/4722366482869645213696:ℚ)⟩ thresholdNode23 thresholdNode26
def thresholdNode28 : BoxExpr 1 := .add ⟨(759492122512208777765/295147905179352825856:ℚ),(12274384554003682510541/4722366482869645213696:ℚ)⟩ thresholdNode18 thresholdNode27
def thresholdNode29 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode30 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode29 thresholdNode3
def thresholdNode31 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode32 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode31
def thresholdNode33 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode32 thresholdNode32
def thresholdNode34 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode33 thresholdNode9
def thresholdNode35 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode30 thresholdNode34
def thresholdNode36 : BoxExpr 1 := .var 0
def thresholdNode37 : BoxExpr 1 := .mul ⟨(5580140082297139363/4722366482869645213696:ℚ),(1395035020574284841/1180591620717411303424:ℚ)⟩ thresholdNode36 thresholdNode36
def thresholdNode38 : BoxExpr 1 := .neg ⟨(-1395035020574284841/1180591620717411303424:ℚ),(-5580140082297139363/4722366482869645213696:ℚ)⟩ thresholdNode37
def thresholdNode39 : BoxExpr 1 := .add ⟨(1179196585696837018583/1180591620717411303424:ℚ),(4716786342787348074333/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode38
def thresholdNode40 : BoxExpr 1 := .sqrt ⟨(4719575588126146927907/4722366482869645213696:ℚ),(4719575588126146927909/4722366482869645213696:ℚ)⟩ thresholdNode39
def thresholdNode41 : BoxExpr 1 := .mul ⟨(6133914402497850008525/2361183241434822606848:ℚ),(12267828804995700017065/4722366482869645213696:ℚ)⟩ thresholdNode35 thresholdNode40
def thresholdNode42 : BoxExpr 1 := .neg ⟨(-47223664828696452137/2361183241434822606848:ℚ),(-94447329657392904273/4722366482869645213696:ℚ)⟩ thresholdNode19
def thresholdNode43 : BoxExpr 1 := .add ⟨(33942009095625574973/2361183241434822606848:ℚ),(16971004547812787487/1180591620717411303424:ℚ)⟩ thresholdNode36 thresholdNode42
def thresholdNode44 : BoxExpr 1 := .mul ⟨(-54307214553000919959/4722366482869645213696:ℚ),(-13576803638250229989/1180591620717411303424:ℚ)⟩ thresholdNode43 thresholdNode22
def thresholdNode45 : BoxExpr 1 := .mul ⟨(60989547593702205/295147905179352825856:ℚ),(975832761499235281/4722366482869645213696:ℚ)⟩ thresholdNode43 thresholdNode43
def thresholdNode46 : BoxExpr 1 := .mul ⟨(439124742674655875/4722366482869645213696:ℚ),(439124742674655877/4722366482869645213696:ℚ)⟩ thresholdNode45 thresholdNode25
def thresholdNode47 : BoxExpr 1 := .add ⟨(-13467022452581566021/1180591620717411303424:ℚ),(-53868089810326264079/4722366482869645213696:ℚ)⟩ thresholdNode44 thresholdNode46
def thresholdNode48 : BoxExpr 1 := .add ⟨(6106980357592686876483/2361183241434822606848:ℚ),(6106980357592686876493/2361183241434822606848:ℚ)⟩ thresholdNode41 thresholdNode47
def thresholdNode49 : BoxExpr 1 := .lit (0/1:ℚ)
def thresholdNode50 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode1
def thresholdNode51 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode49
def thresholdNode52 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode50 thresholdNode51
def thresholdNode53 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode52 thresholdNode49
def thresholdNode54 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49
def thresholdNode55 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode54
def thresholdNode56 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode55 thresholdNode32
def thresholdNode57 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode55
def thresholdNode58 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode56 thresholdNode57
def thresholdNode59 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode58 thresholdNode9
def thresholdNode60 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode33 thresholdNode49
def thresholdNode61 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode59 thresholdNode60
def thresholdNode62 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode53 thresholdNode61
def thresholdNode63 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode62 thresholdNode40
def thresholdNode64 : BoxExpr 1 := .mul ⟨(40582836962161013555/1180591620717411303424:ℚ),(162331347848644054221/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode36
def thresholdNode65 : BoxExpr 1 := .mul ⟨(40582836962161013555/1180591620717411303424:ℚ),(162331347848644054221/4722366482869645213696:ℚ)⟩ thresholdNode36 thresholdNode12
def thresholdNode66 : BoxExpr 1 := .add ⟨(40582836962161013555/590295810358705651712:ℚ),(162331347848644054221/2361183241434822606848:ℚ)⟩ thresholdNode64 thresholdNode65
def thresholdNode67 : BoxExpr 1 := .neg ⟨(-162331347848644054221/2361183241434822606848:ℚ),(-40582836962161013555/590295810358705651712:ℚ)⟩ thresholdNode66
def thresholdNode68 : BoxExpr 1 := .add ⟨(-162331347848644054221/2361183241434822606848:ℚ),(-40582836962161013555/590295810358705651712:ℚ)⟩ thresholdNode49 thresholdNode67
def thresholdNode69 : BoxExpr 1 := .mul ⟨(4719575588126146927907/2361183241434822606848:ℚ),(4719575588126146927909/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode40
def thresholdNode70 : BoxExpr 1 := .inv ⟨(1181289756998302304035/2361183241434822606848:ℚ),(295322439249575576009/590295810358705651712:ℚ)⟩ thresholdNode69
def thresholdNode71 : BoxExpr 1 := .mul ⟨(-81213670793633283403/2361183241434822606848:ℚ),(-40606835396816641701/1180591620717411303424:ℚ)⟩ thresholdNode68 thresholdNode70
def thresholdNode72 : BoxExpr 1 := .mul ⟨(-105551377588715337607/1180591620717411303424:ℚ),(-422205510354861350421/4722366482869645213696:ℚ)⟩ thresholdNode35 thresholdNode71
def thresholdNode73 : BoxExpr 1 := .add ⟨(-105551377588715337607/1180591620717411303424:ℚ),(-422205510354861350421/4722366482869645213696:ℚ)⟩ thresholdNode63 thresholdNode72
def thresholdNode74 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode54
def thresholdNode75 : BoxExpr 1 := .mul ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode74 thresholdNode22
def thresholdNode76 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode43 thresholdNode49
def thresholdNode77 : BoxExpr 1 := .add ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode75 thresholdNode76
def thresholdNode78 : BoxExpr 1 := .mul ⟨(33942009095625574973/2361183241434822606848:ℚ),(16971004547812787487/1180591620717411303424:ℚ)⟩ thresholdNode74 thresholdNode43
def thresholdNode79 : BoxExpr 1 := .mul ⟨(33942009095625574973/2361183241434822606848:ℚ),(16971004547812787487/1180591620717411303424:ℚ)⟩ thresholdNode43 thresholdNode74
def thresholdNode80 : BoxExpr 1 := .add ⟨(33942009095625574973/1180591620717411303424:ℚ),(16971004547812787487/590295810358705651712:ℚ)⟩ thresholdNode78 thresholdNode79
def thresholdNode81 : BoxExpr 1 := .mul ⟨(61095616372126034951/4722366482869645213696:ℚ),(30547808186063017477/2361183241434822606848:ℚ)⟩ thresholdNode80 thresholdNode25
def thresholdNode82 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode45 thresholdNode49
def thresholdNode83 : BoxExpr 1 := .add ⟨(61095616372126034951/4722366482869645213696:ℚ),(30547808186063017477/2361183241434822606848:ℚ)⟩ thresholdNode81 thresholdNode82
def thresholdNode84 : BoxExpr 1 := .add ⟨(-1858398784961795068003/2361183241434822606848:ℚ),(-1858398784961795068001/2361183241434822606848:ℚ)⟩ thresholdNode77 thresholdNode83
def thresholdNode85 : BoxExpr 1 := .add ⟨(-2069501540139225743217/2361183241434822606848:ℚ),(-4139003080278451486423/4722366482869645213696:ℚ)⟩ thresholdNode73 thresholdNode84
def thresholdNode86 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode1
def thresholdNode87 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode49
def thresholdNode88 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode86 thresholdNode87
def thresholdNode89 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode49
def thresholdNode90 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode87 thresholdNode89
def thresholdNode91 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode88 thresholdNode90
def thresholdNode92 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode91 thresholdNode49
def thresholdNode93 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49
def thresholdNode94 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode93
def thresholdNode95 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode94 thresholdNode7
def thresholdNode96 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode94 thresholdNode94
def thresholdNode97 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode95 thresholdNode96
def thresholdNode98 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode7 thresholdNode94
def thresholdNode99 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode96 thresholdNode98
def thresholdNode100 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode97 thresholdNode99
def thresholdNode101 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode100 thresholdNode9
def thresholdNode102 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode95 thresholdNode98
def thresholdNode103 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode102 thresholdNode49
def thresholdNode104 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode101 thresholdNode103
def thresholdNode105 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode8 thresholdNode49
def thresholdNode106 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode103 thresholdNode105
def thresholdNode107 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode104 thresholdNode106
def thresholdNode108 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode92 thresholdNode107
def thresholdNode109 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode108 thresholdNode17
def thresholdNode110 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode86 thresholdNode89
def thresholdNode111 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode110 thresholdNode49
def thresholdNode112 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode102 thresholdNode9
def thresholdNode113 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode112 thresholdNode105
def thresholdNode114 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode111 thresholdNode113
def thresholdNode115 : BoxExpr 1 := .mul ⟨(94447329657392904273/4722366482869645213696:ℚ),(28776920754986900521/590295810358705651712:ℚ)⟩ thresholdNode12 thresholdNode13
def thresholdNode116 : BoxExpr 1 := .mul ⟨(94447329657392904273/4722366482869645213696:ℚ),(28776920754986900521/590295810358705651712:ℚ)⟩ thresholdNode13 thresholdNode12
def thresholdNode117 : BoxExpr 1 := .add ⟨(94447329657392904273/2361183241434822606848:ℚ),(28776920754986900521/295147905179352825856:ℚ)⟩ thresholdNode115 thresholdNode116
def thresholdNode118 : BoxExpr 1 := .neg ⟨(-28776920754986900521/295147905179352825856:ℚ),(-94447329657392904273/2361183241434822606848:ℚ)⟩ thresholdNode117
def thresholdNode119 : BoxExpr 1 := .add ⟨(-28776920754986900521/295147905179352825856:ℚ),(-94447329657392904273/2361183241434822606848:ℚ)⟩ thresholdNode49 thresholdNode118
def thresholdNode120 : BoxExpr 1 := .mul ⟨(2358375822667463458973/1180591620717411303424:ℚ),(590177739388355929705/295147905179352825856:ℚ)⟩ thresholdNode5 thresholdNode17
def thresholdNode121 : BoxExpr 1 := .inv ⟨(1180827809900672128261/2361183241434822606848:ℚ),(2363994002163229509105/4722366482869645213696:ℚ)⟩ thresholdNode120
def thresholdNode122 : BoxExpr 1 := .mul ⟨(-230489415210914877139/4722366482869645213696:ℚ),(-94466224792053770259/4722366482869645213696:ℚ)⟩ thresholdNode119 thresholdNode121
def thresholdNode123 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode114 thresholdNode122
def thresholdNode124 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode109 thresholdNode123
def thresholdNode125 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode13
def thresholdNode126 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode12
def thresholdNode127 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode125 thresholdNode126
def thresholdNode128 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode13 thresholdNode49
def thresholdNode129 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode126 thresholdNode128
def thresholdNode130 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode127 thresholdNode129
def thresholdNode131 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode130
def thresholdNode132 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode49 thresholdNode131
def thresholdNode133 : BoxExpr 1 := .mul ⟨(-2363994002163229509105/2361183241434822606848:ℚ),(-1180827809900672128261/1180591620717411303424:ℚ)⟩ thresholdNode132 thresholdNode121
def thresholdNode134 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode17
def thresholdNode135 : BoxExpr 1 := .mul ⟨(-230489415210914877139/2361183241434822606848:ℚ),(-94466224792053770259/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode122
def thresholdNode136 : BoxExpr 1 := .add ⟨(-230489415210914877139/2361183241434822606848:ℚ),(-94466224792053770259/2361183241434822606848:ℚ)⟩ thresholdNode134 thresholdNode135
def thresholdNode137 : BoxExpr 1 := .mul ⟨(9422286967550400644981/2361183241434822606848:ℚ),(18881910145105989422445/4722366482869645213696:ℚ)⟩ thresholdNode120 thresholdNode120
def thresholdNode138 : BoxExpr 1 := .inv ⟨(36908251447998302553/147573952589676412928:ℚ),(295851013603870774995/1180591620717411303424:ℚ)⟩ thresholdNode137
def thresholdNode139 : BoxExpr 1 := .mul ⟨(-115519246314276210627/4722366482869645213696:ℚ),(-11813003300326852023/1180591620717411303424:ℚ)⟩ thresholdNode136 thresholdNode138
def thresholdNode140 : BoxExpr 1 := .neg ⟨(11813003300326852023/1180591620717411303424:ℚ),(115519246314276210627/4722366482869645213696:ℚ)⟩ thresholdNode139
def thresholdNode141 : BoxExpr 1 := .mul ⟨(-11263126515641930537/4722366482869645213696:ℚ),(-1890080528052296323/4722366482869645213696:ℚ)⟩ thresholdNode119 thresholdNode140
def thresholdNode142 : BoxExpr 1 := .add ⟨(-4739251130842100948747/4722366482869645213696:ℚ),(-4725201320130740809367/4722366482869645213696:ℚ)⟩ thresholdNode133 thresholdNode141
def thresholdNode143 : BoxExpr 1 := .mul ⟨(-6159486213477207550565/2361183241434822606848:ℚ),(-12282452051481841122823/4722366482869645213696:ℚ)⟩ thresholdNode11 thresholdNode142
def thresholdNode144 : BoxExpr 1 := .add ⟨(-6159486213477207550565/2361183241434822606848:ℚ),(-12282452051481841122823/4722366482869645213696:ℚ)⟩ thresholdNode123 thresholdNode143
def thresholdNode145 : BoxExpr 1 := .add ⟨(-6159486213477207550565/2361183241434822606848:ℚ),(-12282452051481841122823/4722366482869645213696:ℚ)⟩ thresholdNode124 thresholdNode144
def thresholdNode146 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode94 thresholdNode22
def thresholdNode147 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode93
def thresholdNode148 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode147 thresholdNode49
def thresholdNode149 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode146 thresholdNode148
def thresholdNode150 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode21 thresholdNode49
def thresholdNode151 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode148 thresholdNode150
def thresholdNode152 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode149 thresholdNode151
def thresholdNode153 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode94 thresholdNode21
def thresholdNode154 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode147 thresholdNode147
def thresholdNode155 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode153 thresholdNode154
def thresholdNode156 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode21 thresholdNode94
def thresholdNode157 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode154 thresholdNode156
def thresholdNode158 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode155 thresholdNode157
def thresholdNode159 : BoxExpr 1 := .mul ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode158 thresholdNode25
def thresholdNode160 : BoxExpr 1 := .mul ⟨(-1/4722366482869645213696:ℚ),(135768036382502299895/4722366482869645213696:ℚ)⟩ thresholdNode147 thresholdNode21
def thresholdNode161 : BoxExpr 1 := .mul ⟨(-1/4722366482869645213696:ℚ),(135768036382502299895/4722366482869645213696:ℚ)⟩ thresholdNode21 thresholdNode147
def thresholdNode162 : BoxExpr 1 := .add ⟨(-1/2361183241434822606848:ℚ),(135768036382502299895/2361183241434822606848:ℚ)⟩ thresholdNode160 thresholdNode161
def thresholdNode163 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode162 thresholdNode49
def thresholdNode164 : BoxExpr 1 := .add ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode159 thresholdNode163
def thresholdNode165 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode24 thresholdNode49
def thresholdNode166 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode163 thresholdNode165
def thresholdNode167 : BoxExpr 1 := .add ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode164 thresholdNode166
def thresholdNode168 : BoxExpr 1 := .add ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode152 thresholdNode167
def thresholdNode169 : BoxExpr 1 := .add ⟨(-2017210648092933602201/1180591620717411303424:ℚ),(-8032322216899160430495/4722366482869645213696:ℚ)⟩ thresholdNode145 thresholdNode168
def thresholdCell0Out0 : TaylorCertificate1 :=
  { center := (11/320:ℚ), radius := (23/1600:ℚ)
    whole := thresholdNode28, centerValue := thresholdNode48, gradient := thresholdNode85, hessian := thresholdNode169 }
theorem thresholdCell0Out0_check : thresholdCell0Out0.check = true := by decide +kernel
theorem thresholdCell0Out0_lower_pos : 0 < thresholdCell0Out0.lower := by decide +kernel
theorem thresholdCell0Out0_positive (x : ℝ) (hx : (1/50:ℝ) ≤ x ∧ x ≤ (39/800:ℝ)) :
    0 < thresholdNode28.eval (fun _ => x) := by
  apply thresholdCell0Out0.positive_sound thresholdCell0Out0_check thresholdCell0Out0_lower_pos x
  norm_num [thresholdCell0Out0]
  exact hx
def thresholdNode170 : BoxExpr 1 := .mul ⟨(15634961970882446097587/2361183241434822606848:ℚ),(15951802631803806115515/2361183241434822606848:ℚ)⟩ thresholdNode28 thresholdNode28
def thresholdNode171 : BoxExpr 1 := .lit (7033791386230630914920427/47247072600500000000000:ℚ)
def thresholdNode172 : BoxExpr 1 := .mul ⟨(94447329657392904273/2361183241434822606848:ℚ),(28776920754986900521/295147905179352825856:ℚ)⟩ thresholdNode13 thresholdNode5
def thresholdNode173 : BoxExpr 1 := .add ⟨(2455630571092215511121/2361183241434822606848:ℚ),(323924825934339726377/295147905179352825856:ℚ)⟩ thresholdNode172 thresholdNode12
def thresholdNode174 : BoxExpr 1 := .inv ⟨(4302839619926783793799/4722366482869645213696:ℚ),(4540737002759274243941/4722366482869645213696:ℚ)⟩ thresholdNode173
def thresholdNode175 : BoxExpr 1 := .mul ⟨(80071829293220079630485/590295810358705651712:ℚ),(84498877547412535956285/590295810358705651712:ℚ)⟩ thresholdNode171 thresholdNode174
def thresholdNode176 : BoxExpr 1 := .add ⟨(80662125103578785282197/590295810358705651712:ℚ),(85089173357771241607997/590295810358705651712:ℚ)⟩ thresholdNode175 thresholdNode12
def thresholdNode177 : BoxExpr 1 := .sqrt ⟨(55202617041309095159201/4722366482869645213696:ℚ),(28348624669278885422233/2361183241434822606848:ℚ)⟩ thresholdNode176
def thresholdNode178 : BoxExpr 1 := .add ⟨(59924983524178740372897/4722366482869645213696:ℚ),(30709807910713708029081/2361183241434822606848:ℚ)⟩ thresholdNode177 thresholdNode12
def thresholdNode179 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode180 : BoxExpr 1 := .mul ⟨(1872655735130585636653/295147905179352825856:ℚ),(30709807910713708029081/4722366482869645213696:ℚ)⟩ thresholdNode178 thresholdNode179
def thresholdNode181 : BoxExpr 1 := .lit (1/4:ℚ)
def thresholdNode182 : BoxExpr 1 := .add ⟨(1946442711425423843117/295147905179352825856:ℚ),(31890399531431119332505/4722366482869645213696:ℚ)⟩ thresholdNode180 thresholdNode181
def thresholdNode183 : BoxExpr 1 := .mul ⟨(3883633737338103718529/590295810358705651712:ℚ),(3984705421452318360597/590295810358705651712:ℚ)⟩ thresholdNode16 thresholdNode182
def thresholdNode184 : BoxExpr 1 := .neg ⟨(-3984705421452318360597/590295810358705651712:ℚ),(-3883633737338103718529/590295810358705651712:ℚ)⟩ thresholdNode183
def thresholdNode185 : BoxExpr 1 := .add ⟨(-303859714926827344801/2361183241434822606848:ℚ),(417267682451391241399/2361183241434822606848:ℚ)⟩ thresholdNode170 thresholdNode184
def thresholdNode186 : BoxExpr 1 := .mul ⟨(31590270872293405125481/4722366482869645213696:ℚ),(15795135436146702562793/2361183241434822606848:ℚ)⟩ thresholdNode48 thresholdNode48
def thresholdNode187 : BoxExpr 1 := .mul ⟨(40582836962161013555/590295810358705651712:ℚ),(162331347848644054221/2361183241434822606848:ℚ)⟩ thresholdNode36 thresholdNode5
def thresholdNode188 : BoxExpr 1 := .add ⟨(630878647320866665267/590295810358705651712:ℚ),(2523514589283466661069/2361183241434822606848:ℚ)⟩ thresholdNode187 thresholdNode12
def thresholdNode189 : BoxExpr 1 := .inv ⟨(138080891311977930225/147573952589676412928:ℚ),(4418588521983293767203/4722366482869645213696:ℚ)⟩ thresholdNode188
def thresholdNode190 : BoxExpr 1 := .mul ⟨(82225808326838865398333/590295810358705651712:ℚ),(657806466614710923187113/4722366482869645213696:ℚ)⟩ thresholdNode171 thresholdNode189
def thresholdNode191 : BoxExpr 1 := .add ⟨(82816104137197571050045/590295810358705651712:ℚ),(662528833097580568400809/4722366482869645213696:ℚ)⟩ thresholdNode190 thresholdNode12
def thresholdNode192 : BoxExpr 1 := .sqrt ⟨(13983704702605528910819/1180591620717411303424:ℚ),(1747963087825691113853/147573952589676412928:ℚ)⟩ thresholdNode191
def thresholdNode193 : BoxExpr 1 := .add ⟨(15164296323322940214243/1180591620717411303424:ℚ),(1895537040415367526781/147573952589676412928:ℚ)⟩ thresholdNode192 thresholdNode12
def thresholdNode194 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode195 : BoxExpr 1 := .mul ⟨(15164296323322940214243/2361183241434822606848:ℚ),(1895537040415367526781/295147905179352825856:ℚ)⟩ thresholdNode193 thresholdNode194
def thresholdNode196 : BoxExpr 1 := .add ⟨(15754592133681645865955/2361183241434822606848:ℚ),(1969324016710205733245/295147905179352825856:ℚ)⟩ thresholdNode195 thresholdNode181
def thresholdNode197 : BoxExpr 1 := .mul ⟨(7867987933793091101191/1180591620717411303424:ℚ),(15735975867586182202391/2361183241434822606848:ℚ)⟩ thresholdNode39 thresholdNode196
def thresholdNode198 : BoxExpr 1 := .neg ⟨(-15735975867586182202391/2361183241434822606848:ℚ),(-7867987933793091101191/1180591620717411303424:ℚ)⟩ thresholdNode197
def thresholdNode199 : BoxExpr 1 := .add ⟨(118319137121040720699/4722366482869645213696:ℚ),(59159568560520360411/2361183241434822606848:ℚ)⟩ thresholdNode186 thresholdNode198
def thresholdNode200 : BoxExpr 1 := .mul ⟨(-2676286413069337339315/1180591620717411303424:ℚ),(-10705145652277349357213/4722366482869645213696:ℚ)⟩ thresholdNode85 thresholdNode48
def thresholdNode201 : BoxExpr 1 := .mul ⟨(-2676286413069337339315/1180591620717411303424:ℚ),(-10705145652277349357213/4722366482869645213696:ℚ)⟩ thresholdNode48 thresholdNode85
def thresholdNode202 : BoxExpr 1 := .add ⟨(-2676286413069337339315/590295810358705651712:ℚ),(-10705145652277349357213/2361183241434822606848:ℚ)⟩ thresholdNode200 thresholdNode201
def thresholdNode203 : BoxExpr 1 := .mul ⟨(-2166256418381226306573/4722366482869645213696:ℚ),(-1083128209190613153279/2361183241434822606848:ℚ)⟩ thresholdNode68 thresholdNode196
def thresholdNode204 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode189
def thresholdNode205 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode206 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode36 thresholdNode49
def thresholdNode207 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode205 thresholdNode206
def thresholdNode208 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode207 thresholdNode49
def thresholdNode209 : BoxExpr 1 := .mul ⟨(5394012434593409988031/4722366482869645213696:ℚ),(1348503108648352497009/1180591620717411303424:ℚ)⟩ thresholdNode188 thresholdNode188
def thresholdNode210 : BoxExpr 1 := .inv ⟨(2067175916717330417403/2361183241434822606848:ℚ),(4134351833434660834811/4722366482869645213696:ℚ)⟩ thresholdNode209
def thresholdNode211 : BoxExpr 1 := .mul ⟨(2067175916717330417403/1180591620717411303424:ℚ),(4134351833434660834811/2361183241434822606848:ℚ)⟩ thresholdNode208 thresholdNode210
def thresholdNode212 : BoxExpr 1 := .neg ⟨(-4134351833434660834811/2361183241434822606848:ℚ),(-2067175916717330417403/1180591620717411303424:ℚ)⟩ thresholdNode211
def thresholdNode213 : BoxExpr 1 := .mul ⟨(-1230982861501213423508397/4722366482869645213696:ℚ),(-615491430750606711753453/2361183241434822606848:ℚ)⟩ thresholdNode171 thresholdNode212
def thresholdNode214 : BoxExpr 1 := .add ⟨(-1230982861501213423508397/4722366482869645213696:ℚ),(-615491430750606711753453/2361183241434822606848:ℚ)⟩ thresholdNode204 thresholdNode213
def thresholdNode215 : BoxExpr 1 := .add ⟨(-1230982861501213423508397/4722366482869645213696:ℚ),(-615491430750606711753453/2361183241434822606848:ℚ)⟩ thresholdNode214 thresholdNode49
def thresholdNode216 : BoxExpr 1 := .mul ⟨(13983704702605528910819/590295810358705651712:ℚ),(1747963087825691113853/73786976294838206464:ℚ)⟩ thresholdNode5 thresholdNode192
def thresholdNode217 : BoxExpr 1 := .inv ⟨(99672912475651984503/2361183241434822606848:ℚ),(199345824951303969007/4722366482869645213696:ℚ)⟩ thresholdNode216
def thresholdNode218 : BoxExpr 1 := .mul ⟨(-51963627752532872706759/4722366482869645213696:ℚ),(-51963627752532872706435/4722366482869645213696:ℚ)⟩ thresholdNode215 thresholdNode217
def thresholdNode219 : BoxExpr 1 := .add ⟨(-51963627752532872706759/4722366482869645213696:ℚ),(-51963627752532872706435/4722366482869645213696:ℚ)⟩ thresholdNode218 thresholdNode49
def thresholdNode220 : BoxExpr 1 := .mul ⟨(-6495453469066609088345/1180591620717411303424:ℚ),(-25981813876266436353217/4722366482869645213696:ℚ)⟩ thresholdNode219 thresholdNode194
def thresholdNode221 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode222 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode221
def thresholdNode223 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode222
def thresholdNode224 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode223
def thresholdNode225 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode193 thresholdNode224
def thresholdNode226 : BoxExpr 1 := .add ⟨(-6495453469066609088345/1180591620717411303424:ℚ),(-25981813876266436353217/4722366482869645213696:ℚ)⟩ thresholdNode220 thresholdNode225
def thresholdNode227 : BoxExpr 1 := .add ⟨(-6495453469066609088345/1180591620717411303424:ℚ),(-25981813876266436353217/4722366482869645213696:ℚ)⟩ thresholdNode226 thresholdNode49
def thresholdNode228 : BoxExpr 1 := .mul ⟨(-12975556354739525604433/2361183241434822606848:ℚ),(-25951112709479051208697/4722366482869645213696:ℚ)⟩ thresholdNode39 thresholdNode227
def thresholdNode229 : BoxExpr 1 := .add ⟨(-28117369127860277515439/4722366482869645213696:ℚ),(-28117369127860277515255/4722366482869645213696:ℚ)⟩ thresholdNode203 thresholdNode228
def thresholdNode230 : BoxExpr 1 := .neg ⟨(28117369127860277515255/4722366482869645213696:ℚ),(28117369127860277515439/4722366482869645213696:ℚ)⟩ thresholdNode229
def thresholdNode231 : BoxExpr 1 := .add ⟨(6707077823305578800735/4722366482869645213696:ℚ),(6707077823305578801013/4722366482869645213696:ℚ)⟩ thresholdNode202 thresholdNode230
def thresholdNode232 : BoxExpr 1 := .mul ⟨(-10486276027470750748263/2361183241434822606848:ℚ),(-10334624339460626362607/2361183241434822606848:ℚ)⟩ thresholdNode169 thresholdNode28
def thresholdNode233 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode114 thresholdNode17
def thresholdNode234 : BoxExpr 1 := .mul ⟨(-149780665357122896473/1180591620717411303424:ℚ),(-122775390706612483861/2361183241434822606848:ℚ)⟩ thresholdNode11 thresholdNode122
def thresholdNode235 : BoxExpr 1 := .add ⟨(-149780665357122896473/1180591620717411303424:ℚ),(-122775390706612483861/2361183241434822606848:ℚ)⟩ thresholdNode233 thresholdNode234
def thresholdNode236 : BoxExpr 1 := .mul ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode147 thresholdNode22
def thresholdNode237 : BoxExpr 1 := .add ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode236 thresholdNode150
def thresholdNode238 : BoxExpr 1 := .mul ⟨(-1/4722366482869645213696:ℚ),(61095616372126034953/2361183241434822606848:ℚ)⟩ thresholdNode162 thresholdNode25
def thresholdNode239 : BoxExpr 1 := .add ⟨(-1/4722366482869645213696:ℚ),(61095616372126034953/2361183241434822606848:ℚ)⟩ thresholdNode238 thresholdNode165
def thresholdNode240 : BoxExpr 1 := .add ⟨(-1888946593147858085479/2361183241434822606848:ℚ),(-1827850976775732050525/2361183241434822606848:ℚ)⟩ thresholdNode237 thresholdNode239
def thresholdNode241 : BoxExpr 1 := .add ⟨(-2188507923862103878425/2361183241434822606848:ℚ),(-975313183741172267193/1180591620717411303424:ℚ)⟩ thresholdNode235 thresholdNode240
def thresholdNode242 : BoxExpr 1 := .mul ⟨(402864034305657375315/590295810358705651712:ℚ),(2028460497583717936045/2361183241434822606848:ℚ)⟩ thresholdNode241 thresholdNode241
def thresholdNode243 : BoxExpr 1 := .add ⟨(-8874819890248121247003/2361183241434822606848:ℚ),(-4153081920938454213281/1180591620717411303424:ℚ)⟩ thresholdNode232 thresholdNode242
def thresholdNode244 : BoxExpr 1 := .mul ⟨(-10486276027470750748263/2361183241434822606848:ℚ),(-10334624339460626362607/2361183241434822606848:ℚ)⟩ thresholdNode28 thresholdNode169
def thresholdNode245 : BoxExpr 1 := .add ⟨(-8874819890248121247003/2361183241434822606848:ℚ),(-4153081920938454213281/1180591620717411303424:ℚ)⟩ thresholdNode242 thresholdNode244
def thresholdNode246 : BoxExpr 1 := .add ⟨(-8874819890248121247003/1180591620717411303424:ℚ),(-4153081920938454213281/590295810358705651712:ℚ)⟩ thresholdNode243 thresholdNode245
def thresholdNode247 : BoxExpr 1 := .mul ⟨(-31890399531431119332505/2361183241434822606848:ℚ),(-1946442711425423843117/147573952589676412928:ℚ)⟩ thresholdNode132 thresholdNode182
def thresholdNode248 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode174
def thresholdNode249 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode250 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode249 thresholdNode128
def thresholdNode251 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode250 thresholdNode49
def thresholdNode252 : BoxExpr 1 := .mul ⟨(5107711587871808263129/4722366482869645213696:ℚ),(5688119943407005595181/4722366482869645213696:ℚ)⟩ thresholdNode173 thresholdNode173
def thresholdNode253 : BoxExpr 1 := .inv ⟨(3920582797199803001183/4722366482869645213696:ℚ),(4366093271883917542253/4722366482869645213696:ℚ)⟩ thresholdNode252
def thresholdNode254 : BoxExpr 1 := .mul ⟨(3920582797199803001183/2361183241434822606848:ℚ),(4366093271883917542253/2361183241434822606848:ℚ)⟩ thresholdNode251 thresholdNode253
def thresholdNode255 : BoxExpr 1 := .neg ⟨(-4366093271883917542253/2361183241434822606848:ℚ),(-3920582797199803001183/2361183241434822606848:ℚ)⟩ thresholdNode254
def thresholdNode256 : BoxExpr 1 := .mul ⟨(-1299982731498654399328069/4722366482869645213696:ℚ),(-1167334185595919156344023/4722366482869645213696:ℚ)⟩ thresholdNode171 thresholdNode255
def thresholdNode257 : BoxExpr 1 := .add ⟨(-1299982731498654399328069/4722366482869645213696:ℚ),(-1167334185595919156344023/4722366482869645213696:ℚ)⟩ thresholdNode248 thresholdNode256
def thresholdNode258 : BoxExpr 1 := .add ⟨(-1299982731498654399328069/4722366482869645213696:ℚ),(-1167334185595919156344023/4722366482869645213696:ℚ)⟩ thresholdNode257 thresholdNode49
def thresholdNode259 : BoxExpr 1 := .mul ⟨(55202617041309095159201/2361183241434822606848:ℚ),(28348624669278885422233/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode177
def thresholdNode260 : BoxExpr 1 := .inv ⟨(196665142125022669973/4722366482869645213696:ℚ),(201989927233364505989/4722366482869645213696:ℚ)⟩ thresholdNode259
def thresholdNode261 : BoxExpr 1 := .mul ⟨(-55604201472410777410107/4722366482869645213696:ℚ),(-3038385843601892607687/295147905179352825856:ℚ)⟩ thresholdNode258 thresholdNode260
def thresholdNode262 : BoxExpr 1 := .add ⟨(-55604201472410777410107/4722366482869645213696:ℚ),(-3038385843601892607687/295147905179352825856:ℚ)⟩ thresholdNode261 thresholdNode49
def thresholdNode263 : BoxExpr 1 := .mul ⟨(-13901050368102694352527/2361183241434822606848:ℚ),(-3038385843601892607687/590295810358705651712:ℚ)⟩ thresholdNode262 thresholdNode179
def thresholdNode264 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode265 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode264
def thresholdNode266 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode265
def thresholdNode267 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode266
def thresholdNode268 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode178 thresholdNode267
def thresholdNode269 : BoxExpr 1 := .add ⟨(-13901050368102694352527/2361183241434822606848:ℚ),(-3038385843601892607687/590295810358705651712:ℚ)⟩ thresholdNode263 thresholdNode268
def thresholdNode270 : BoxExpr 1 := .add ⟨(-13901050368102694352527/2361183241434822606848:ℚ),(-3038385843601892607687/590295810358705651712:ℚ)⟩ thresholdNode269 thresholdNode49
def thresholdNode271 : BoxExpr 1 := .mul ⟨(486141734976302817225/2361183241434822606848:ℚ),(2710704821780025398747/4722366482869645213696:ℚ)⟩ thresholdNode119 thresholdNode270
def thresholdNode272 : BoxExpr 1 := .add ⟨(-1962766112278426032205/147573952589676412928:ℚ),(-59575461943833537580997/4722366482869645213696:ℚ)⟩ thresholdNode247 thresholdNode271
def thresholdNode273 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode255
def thresholdNode274 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode248 thresholdNode273
def thresholdNode275 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode5
def thresholdNode276 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode12 thresholdNode49
def thresholdNode277 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode275 thresholdNode276
def thresholdNode278 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode276 thresholdNode128
def thresholdNode279 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode277 thresholdNode278
def thresholdNode280 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode279 thresholdNode49
def thresholdNode281 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode280 thresholdNode253
def thresholdNode282 : BoxExpr 1 := .mul ⟨(2455630571092215511121/1180591620717411303424:ℚ),(323924825934339726377/147573952589676412928:ℚ)⟩ thresholdNode251 thresholdNode173
def thresholdNode283 : BoxExpr 1 := .mul ⟨(2455630571092215511121/1180591620717411303424:ℚ),(323924825934339726377/147573952589676412928:ℚ)⟩ thresholdNode173 thresholdNode251
def thresholdNode284 : BoxExpr 1 := .add ⟨(2455630571092215511121/590295810358705651712:ℚ),(323924825934339726377/73786976294838206464:ℚ)⟩ thresholdNode282 thresholdNode283
def thresholdNode285 : BoxExpr 1 := .mul ⟨(5524500853442147817395/4722366482869645213696:ℚ),(6851376022583384533183/4722366482869645213696:ℚ)⟩ thresholdNode252 thresholdNode252
def thresholdNode286 : BoxExpr 1 := .inv ⟨(1627464696509380088805/2361183241434822606848:ℚ),(4036698661135278792767/4722366482869645213696:ℚ)⟩ thresholdNode285
def thresholdNode287 : BoxExpr 1 := .mul ⟨(3385126568739510584713/1180591620717411303424:ℚ),(8860553561191936950125/2361183241434822606848:ℚ)⟩ thresholdNode284 thresholdNode286
def thresholdNode288 : BoxExpr 1 := .neg ⟨(-8860553561191936950125/2361183241434822606848:ℚ),(-3385126568739510584713/1180591620717411303424:ℚ)⟩ thresholdNode287
def thresholdNode289 : BoxExpr 1 := .mul ⟨(-8860553561191936950125/1180591620717411303424:ℚ),(-3385126568739510584713/590295810358705651712:ℚ)⟩ thresholdNode251 thresholdNode288
def thresholdNode290 : BoxExpr 1 := .add ⟨(-8860553561191936950125/1180591620717411303424:ℚ),(-3385126568739510584713/590295810358705651712:ℚ)⟩ thresholdNode281 thresholdNode289
def thresholdNode291 : BoxExpr 1 := .neg ⟨(3385126568739510584713/590295810358705651712:ℚ),(8860553561191936950125/1180591620717411303424:ℚ)⟩ thresholdNode290
def thresholdNode292 : BoxExpr 1 := .mul ⟨(2015809470510851932228799/2361183241434822606848:ℚ),(5276372218268392023905413/4722366482869645213696:ℚ)⟩ thresholdNode171 thresholdNode291
def thresholdNode293 : BoxExpr 1 := .add ⟨(2015809470510851932228799/2361183241434822606848:ℚ),(5276372218268392023905413/4722366482869645213696:ℚ)⟩ thresholdNode273 thresholdNode292
def thresholdNode294 : BoxExpr 1 := .add ⟨(2015809470510851932228799/2361183241434822606848:ℚ),(5276372218268392023905413/4722366482869645213696:ℚ)⟩ thresholdNode274 thresholdNode293
def thresholdNode295 : BoxExpr 1 := .add ⟨(2015809470510851932228799/2361183241434822606848:ℚ),(5276372218268392023905413/4722366482869645213696:ℚ)⟩ thresholdNode294 thresholdNode49
def thresholdNode296 : BoxExpr 1 := .mul ⟨(167898640418131472516253/4722366482869645213696:ℚ),(7052700988809498452253/147573952589676412928:ℚ)⟩ thresholdNode295 thresholdNode260
def thresholdNode297 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode177
def thresholdNode298 : BoxExpr 1 := .mul ⟨(-55604201472410777410107/2361183241434822606848:ℚ),(-3038385843601892607687/147573952589676412928:ℚ)⟩ thresholdNode5 thresholdNode261
def thresholdNode299 : BoxExpr 1 := .add ⟨(-55604201472410777410107/2361183241434822606848:ℚ),(-3038385843601892607687/147573952589676412928:ℚ)⟩ thresholdNode297 thresholdNode298
def thresholdNode300 : BoxExpr 1 := .mul ⟨(2581188003314521129030233/4722366482869645213696:ℚ),(2722853547448679731455999/4722366482869645213696:ℚ)⟩ thresholdNode259 thresholdNode259
def thresholdNode301 : BoxExpr 1 := .inv ⟨(8190211045109816715/4722366482869645213696:ℚ),(8639721387940004391/4722366482869645213696:ℚ)⟩ thresholdNode300
def thresholdNode302 : BoxExpr 1 := .mul ⟨(-50864837625709261123/1180591620717411303424:ℚ),(-84313731721902694609/2361183241434822606848:ℚ)⟩ thresholdNode299 thresholdNode301
def thresholdNode303 : BoxExpr 1 := .neg ⟨(84313731721902694609/2361183241434822606848:ℚ),(50864837625709261123/1180591620717411303424:ℚ)⟩ thresholdNode302
def thresholdNode304 : BoxExpr 1 := .mul ⟨(-56008707323980307784539/4722366482869645213696:ℚ),(-41683465995774100613265/4722366482869645213696:ℚ)⟩ thresholdNode258 thresholdNode303
def thresholdNode305 : BoxExpr 1 := .add ⟨(55944966547075582365857/2361183241434822606848:ℚ),(184002965646129849858831/4722366482869645213696:ℚ)⟩ thresholdNode296 thresholdNode304
def thresholdNode306 : BoxExpr 1 := .add ⟨(55944966547075582365857/2361183241434822606848:ℚ),(184002965646129849858831/4722366482869645213696:ℚ)⟩ thresholdNode305 thresholdNode49
def thresholdNode307 : BoxExpr 1 := .mul ⟨(55944966547075582365857/4722366482869645213696:ℚ),(11500185352883115616177/590295810358705651712:ℚ)⟩ thresholdNode306 thresholdNode179
def thresholdNode308 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode262 thresholdNode267
def thresholdNode309 : BoxExpr 1 := .add ⟨(55944966547075582365857/4722366482869645213696:ℚ),(11500185352883115616177/590295810358705651712:ℚ)⟩ thresholdNode307 thresholdNode308
def thresholdNode310 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode5 thresholdNode49
def thresholdNode311 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode275 thresholdNode310
def thresholdNode312 : BoxExpr 1 := .mul ⟨(16/1:ℚ),(16/1:ℚ)⟩ thresholdNode264 thresholdNode264
def thresholdNode313 : BoxExpr 1 := .inv ⟨(1/16:ℚ),(1/16:ℚ)⟩ thresholdNode312
def thresholdNode314 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode311 thresholdNode313
def thresholdNode315 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode314
def thresholdNode316 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode315
def thresholdNode317 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode266 thresholdNode316
def thresholdNode318 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode317
def thresholdNode319 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode178 thresholdNode318
def thresholdNode320 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode308 thresholdNode319
def thresholdNode321 : BoxExpr 1 := .add ⟨(55944966547075582365857/4722366482869645213696:ℚ),(11500185352883115616177/590295810358705651712:ℚ)⟩ thresholdNode309 thresholdNode320
def thresholdNode322 : BoxExpr 1 := .add ⟨(55944966547075582365857/4722366482869645213696:ℚ),(11500185352883115616177/590295810358705651712:ℚ)⟩ thresholdNode321 thresholdNode49
def thresholdNode323 : BoxExpr 1 := .mul ⟨(27906004918758024026065/2361183241434822606848:ℚ),(45982341114967849479727/2361183241434822606848:ℚ)⟩ thresholdNode16 thresholdNode322
def thresholdNode324 : BoxExpr 1 := .add ⟨(14196073326867163421645/1180591620717411303424:ℚ),(94675387051715724358201/4722366482869645213696:ℚ)⟩ thresholdNode271 thresholdNode323
def thresholdNode325 : BoxExpr 1 := .add ⟨(-1506055571360244835995/1180591620717411303424:ℚ),(8774981276970546694301/1180591620717411303424:ℚ)⟩ thresholdNode272 thresholdNode324
def thresholdNode326 : BoxExpr 1 := .neg ⟨(-8774981276970546694301/1180591620717411303424:ℚ),(1506055571360244835995/1180591620717411303424:ℚ)⟩ thresholdNode325
def thresholdNode327 : BoxExpr 1 := .add ⟨(-2206225145902333492663/147573952589676412928:ℚ),(-6800108270516663590567/1180591620717411303424:ℚ)⟩ thresholdNode246 thresholdNode326
def thresholdCell0Out1 : TaylorCertificate1 :=
  { center := (11/320:ℚ), radius := (23/1600:ℚ)
    whole := thresholdNode185, centerValue := thresholdNode199, gradient := thresholdNode231, hessian := thresholdNode327 }
theorem thresholdCell0Out1_check : thresholdCell0Out1.check = true := by decide +kernel
theorem thresholdCell0Out1_lower_pos : 0 < thresholdCell0Out1.lower := by decide +kernel
theorem thresholdCell0Out1_positive (x : ℝ) (hx : (1/50:ℝ) ≤ x ∧ x ≤ (39/800:ℝ)) :
    0 < thresholdNode185.eval (fun _ => x) := by
  apply thresholdCell0Out1.positive_sound thresholdCell0Out1_check thresholdCell0Out1_lower_pos x
  norm_num [thresholdCell0Out1]
  exact hx
theorem thresholdCell0_public (x : ℝ)
    (hx : (1/50:ℝ) ≤ x ∧ x ≤ (39/800:ℝ)) : qc x < fA (43/20) x := by
  have hf := thresholdCell0Out0_positive x hx
  have hg := thresholdCell0Out1_positive x hx
  have hfa : thresholdNode28.eval (fun _ => x) = thresholdFA 2 x := by
    norm_num [thresholdNode0, thresholdNode1, thresholdNode2, thresholdNode3, thresholdNode4, thresholdNode5, thresholdNode6, thresholdNode7, thresholdNode8, thresholdNode9, thresholdNode10, thresholdNode11, thresholdNode12, thresholdNode13, thresholdNode14, thresholdNode15, thresholdNode16, thresholdNode17, thresholdNode18, thresholdNode19, thresholdNode20, thresholdNode21, thresholdNode22, thresholdNode23, thresholdNode24, thresholdNode25, thresholdNode26, thresholdNode27, thresholdNode28, BoxExpr.eval, thresholdFA, ftilde, pow_two, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  have hgap : thresholdNode185.eval (fun _ => x) =
      (thresholdNode28.eval (fun _ => x))^2 - (1-x^2)*(thresholdCapacity 3 x+1/4) := by
    norm_num [thresholdNode170, thresholdNode12, thresholdNode13, thresholdNode14, thresholdNode15, thresholdNode16, thresholdNode171, thresholdNode5, thresholdNode172, thresholdNode173, thresholdNode174, thresholdNode175, thresholdNode176, thresholdNode177, thresholdNode178, thresholdNode179, thresholdNode180, thresholdNode181, thresholdNode182, thresholdNode183, thresholdNode184, thresholdNode185, BoxExpr.eval, thresholdCapacity, Da, D5, beta5, eta5, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  rw [hfa] at hf
  rw [hgap, hfa] at hg
  refine threshold_positive_to_public 2 3 x ?_ ?_ ?_ hf hg
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdFADomain] <;> constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdCapacityDomain] <;> constructor <;> linarith [hx.1,hx.2]
def thresholdNode328 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode329 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode328 thresholdNode3
def thresholdNode330 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode331 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode330
def thresholdNode332 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode331 thresholdNode331
def thresholdNode333 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode332 thresholdNode9
def thresholdNode334 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode329 thresholdNode333
def thresholdNode335 : BoxExpr 1 := .var 0
def thresholdNode336 : BoxExpr 1 := .mul ⟨(11222999094444891203/4722366482869645213696:ℚ),(28363713687735806565/4722366482869645213696:ℚ)⟩ thresholdNode335 thresholdNode335
def thresholdNode337 : BoxExpr 1 := .neg ⟨(-28363713687735806565/4722366482869645213696:ℚ),(-11222999094444891203/4722366482869645213696:ℚ)⟩ thresholdNode336
def thresholdNode338 : BoxExpr 1 := .add ⟨(4694002769181909407131/4722366482869645213696:ℚ),(4711143483775200322493/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode337
def thresholdNode339 : BoxExpr 1 := .sqrt ⟨(2354081633444449425211/2361183241434822606848:ℚ),(1179187911333731729487/1180591620717411303424:ℚ)⟩ thresholdNode338
def thresholdNode340 : BoxExpr 1 := .mul ⟨(12238164187787659226839/4722366482869645213696:ℚ),(12260488389301342284173/4722366482869645213696:ℚ)⟩ thresholdNode334 thresholdNode339
def thresholdNode341 : BoxExpr 1 := .neg ⟨(-47223664828696452137/2361183241434822606848:ℚ),(-94447329657392904273/4722366482869645213696:ℚ)⟩ thresholdNode19
def thresholdNode342 : BoxExpr 1 := .add ⟨(135768036382502299893/4722366482869645213696:ℚ),(271536072765004599789/4722366482869645213696:ℚ)⟩ thresholdNode335 thresholdNode341
def thresholdNode343 : BoxExpr 1 := .mul ⟨(-27153607276500459979/590295810358705651712:ℚ),(-54307214553000919957/2361183241434822606848:ℚ)⟩ thresholdNode342 thresholdNode22
def thresholdNode344 : BoxExpr 1 := .mul ⟨(3903331045996941121/4722366482869645213696:ℚ),(1951665522998470561/590295810358705651712:ℚ)⟩ thresholdNode342 thresholdNode342
def thresholdNode345 : BoxExpr 1 := .mul ⟨(109781185668663969/295147905179352825856:ℚ),(1756498970698623505/1180591620717411303424:ℚ)⟩ thresholdNode344 thresholdNode25
def thresholdNode346 : BoxExpr 1 := .add ⟨(-26934044905163132041/590295810358705651712:ℚ),(-50794216611603672947/2361183241434822606848:ℚ)⟩ thresholdNode343 thresholdNode345
def thresholdNode347 : BoxExpr 1 := .add ⟨(12022691828546354170511/4722366482869645213696:ℚ),(12158899956078134938279/4722366482869645213696:ℚ)⟩ thresholdNode340 thresholdNode346
def thresholdNode348 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode349 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode348 thresholdNode3
def thresholdNode350 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode351 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode350
def thresholdNode352 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode351 thresholdNode351
def thresholdNode353 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode352 thresholdNode9
def thresholdNode354 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode349 thresholdNode353
def thresholdNode355 : BoxExpr 1 := .var 0
def thresholdNode356 : BoxExpr 1 := .mul ⟨(18817523629591113603/4722366482869645213696:ℚ),(4704380907397778401/1180591620717411303424:ℚ)⟩ thresholdNode355 thresholdNode355
def thresholdNode357 : BoxExpr 1 := .neg ⟨(-4704380907397778401/1180591620717411303424:ℚ),(-18817523629591113603/4722366482869645213696:ℚ)⟩ thresholdNode356
def thresholdNode358 : BoxExpr 1 := .add ⟨(1175887239810013525023/1180591620717411303424:ℚ),(4703548959240054100093/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode357
def thresholdNode359 : BoxExpr 1 := .sqrt ⟨(4712948329406087867461/4722366482869645213696:ℚ),(4712948329406087867463/4722366482869645213696:ℚ)⟩ thresholdNode358
def thresholdNode360 : BoxExpr 1 := .mul ⟨(1531325280005214312285/590295810358705651712:ℚ),(12250602240041714498295/4722366482869645213696:ℚ)⟩ thresholdNode354 thresholdNode359
def thresholdNode361 : BoxExpr 1 := .neg ⟨(-47223664828696452137/2361183241434822606848:ℚ),(-94447329657392904273/4722366482869645213696:ℚ)⟩ thresholdNode19
def thresholdNode362 : BoxExpr 1 := .add ⟨(12728253410859590615/295147905179352825856:ℚ),(101826027286876724921/2361183241434822606848:ℚ)⟩ thresholdNode355 thresholdNode361
def thresholdNode363 : BoxExpr 1 := .mul ⟨(-81460821829501379937/2361183241434822606848:ℚ),(-162921643659002759871/4722366482869645213696:ℚ)⟩ thresholdNode362 thresholdNode22
def thresholdNode364 : BoxExpr 1 := .mul ⟨(2195623713373279381/1180591620717411303424:ℚ),(8782494853493117525/4722366482869645213696:ℚ)⟩ thresholdNode362 thresholdNode362
def thresholdNode365 : BoxExpr 1 := .mul ⟨(3952122684071902885/4722366482869645213696:ℚ),(3952122684071902887/4722366482869645213696:ℚ)⟩ thresholdNode364 thresholdNode25
def thresholdNode366 : BoxExpr 1 := .add ⟨(-158969520974930856989/4722366482869645213696:ℚ),(-19871190121866357123/590295810358705651712:ℚ)⟩ thresholdNode363 thresholdNode365
def thresholdNode367 : BoxExpr 1 := .add ⟨(12091632719066783641291/4722366482869645213696:ℚ),(12091632719066783641311/4722366482869645213696:ℚ)⟩ thresholdNode360 thresholdNode366
def thresholdNode368 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode1
def thresholdNode369 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode49
def thresholdNode370 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode368 thresholdNode369
def thresholdNode371 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode370 thresholdNode49
def thresholdNode372 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49
def thresholdNode373 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode372
def thresholdNode374 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode373 thresholdNode351
def thresholdNode375 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode351 thresholdNode373
def thresholdNode376 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode374 thresholdNode375
def thresholdNode377 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode376 thresholdNode9
def thresholdNode378 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode352 thresholdNode49
def thresholdNode379 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode377 thresholdNode378
def thresholdNode380 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode371 thresholdNode379
def thresholdNode381 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode380 thresholdNode359
def thresholdNode382 : BoxExpr 1 := .mul ⟨(149049692115573177057/2361183241434822606848:ℚ),(298099384231146354115/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode355
def thresholdNode383 : BoxExpr 1 := .mul ⟨(149049692115573177057/2361183241434822606848:ℚ),(298099384231146354115/4722366482869645213696:ℚ)⟩ thresholdNode355 thresholdNode12
def thresholdNode384 : BoxExpr 1 := .add ⟨(149049692115573177057/1180591620717411303424:ℚ),(298099384231146354115/2361183241434822606848:ℚ)⟩ thresholdNode382 thresholdNode383
def thresholdNode385 : BoxExpr 1 := .neg ⟨(-298099384231146354115/2361183241434822606848:ℚ),(-149049692115573177057/1180591620717411303424:ℚ)⟩ thresholdNode384
def thresholdNode386 : BoxExpr 1 := .add ⟨(-298099384231146354115/2361183241434822606848:ℚ),(-149049692115573177057/1180591620717411303424:ℚ)⟩ thresholdNode49 thresholdNode385
def thresholdNode387 : BoxExpr 1 := .mul ⟨(4712948329406087867461/2361183241434822606848:ℚ),(4712948329406087867463/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode359
def thresholdNode388 : BoxExpr 1 := .inv ⟨(591475432145807617615/1180591620717411303424:ℚ),(1182950864291615235231/2361183241434822606848:ℚ)⟩ thresholdNode387
def thresholdNode389 : BoxExpr 1 := .mul ⟨(-298695093233632846897/4722366482869645213696:ℚ),(-298695093233632846895/4722366482869645213696:ℚ)⟩ thresholdNode386 thresholdNode388
def thresholdNode390 : BoxExpr 1 := .mul ⟨(-388206545298421770291/2361183241434822606848:ℚ),(-24262909081151360643/147573952589676412928:ℚ)⟩ thresholdNode354 thresholdNode389
def thresholdNode391 : BoxExpr 1 := .add ⟨(-388206545298421770291/2361183241434822606848:ℚ),(-24262909081151360643/147573952589676412928:ℚ)⟩ thresholdNode381 thresholdNode390
def thresholdNode392 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode372
def thresholdNode393 : BoxExpr 1 := .mul ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode392 thresholdNode22
def thresholdNode394 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode362 thresholdNode49
def thresholdNode395 : BoxExpr 1 := .add ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode393 thresholdNode394
def thresholdNode396 : BoxExpr 1 := .mul ⟨(12728253410859590615/295147905179352825856:ℚ),(101826027286876724921/2361183241434822606848:ℚ)⟩ thresholdNode392 thresholdNode362
def thresholdNode397 : BoxExpr 1 := .mul ⟨(12728253410859590615/295147905179352825856:ℚ),(101826027286876724921/2361183241434822606848:ℚ)⟩ thresholdNode362 thresholdNode392
def thresholdNode398 : BoxExpr 1 := .add ⟨(12728253410859590615/147573952589676412928:ℚ),(101826027286876724921/1180591620717411303424:ℚ)⟩ thresholdNode396 thresholdNode397
def thresholdNode399 : BoxExpr 1 := .mul ⟨(183286849116378104855/4722366482869645213696:ℚ),(91643424558189052429/2361183241434822606848:ℚ)⟩ thresholdNode398 thresholdNode25
def thresholdNode400 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode364 thresholdNode49
def thresholdNode401 : BoxExpr 1 := .add ⟨(183286849116378104855/4722366482869645213696:ℚ),(91643424558189052429/2361183241434822606848:ℚ)⟩ thresholdNode399 thresholdNode400
def thresholdNode402 : BoxExpr 1 := .add ⟨(-1797303168589669033051/2361183241434822606848:ℚ),(-1797303168589669033049/2361183241434822606848:ℚ)⟩ thresholdNode395 thresholdNode401
def thresholdNode403 : BoxExpr 1 := .add ⟨(-1092754856944045401671/1180591620717411303424:ℚ),(-2185509713888090803337/2361183241434822606848:ℚ)⟩ thresholdNode391 thresholdNode402
def thresholdNode404 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode1
def thresholdNode405 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode49
def thresholdNode406 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode404 thresholdNode405
def thresholdNode407 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode49
def thresholdNode408 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode405 thresholdNode407
def thresholdNode409 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode406 thresholdNode408
def thresholdNode410 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode409 thresholdNode49
def thresholdNode411 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49
def thresholdNode412 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode411
def thresholdNode413 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode412 thresholdNode331
def thresholdNode414 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode412 thresholdNode412
def thresholdNode415 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode413 thresholdNode414
def thresholdNode416 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode331 thresholdNode412
def thresholdNode417 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode414 thresholdNode416
def thresholdNode418 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode415 thresholdNode417
def thresholdNode419 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode418 thresholdNode9
def thresholdNode420 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode413 thresholdNode416
def thresholdNode421 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode420 thresholdNode49
def thresholdNode422 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode419 thresholdNode421
def thresholdNode423 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode332 thresholdNode49
def thresholdNode424 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode421 thresholdNode423
def thresholdNode425 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode422 thresholdNode424
def thresholdNode426 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode410 thresholdNode425
def thresholdNode427 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode426 thresholdNode339
def thresholdNode428 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode404 thresholdNode407
def thresholdNode429 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode428 thresholdNode49
def thresholdNode430 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode420 thresholdNode9
def thresholdNode431 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode430 thresholdNode423
def thresholdNode432 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode429 thresholdNode431
def thresholdNode433 : BoxExpr 1 := .mul ⟨(230215366039895204167/4722366482869645213696:ℚ),(182991701211198752031/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode335
def thresholdNode434 : BoxExpr 1 := .mul ⟨(230215366039895204167/4722366482869645213696:ℚ),(182991701211198752031/2361183241434822606848:ℚ)⟩ thresholdNode335 thresholdNode12
def thresholdNode435 : BoxExpr 1 := .add ⟨(230215366039895204167/2361183241434822606848:ℚ),(182991701211198752031/1180591620717411303424:ℚ)⟩ thresholdNode433 thresholdNode434
def thresholdNode436 : BoxExpr 1 := .neg ⟨(-182991701211198752031/1180591620717411303424:ℚ),(-230215366039895204167/2361183241434822606848:ℚ)⟩ thresholdNode435
def thresholdNode437 : BoxExpr 1 := .add ⟨(-182991701211198752031/1180591620717411303424:ℚ),(-230215366039895204167/2361183241434822606848:ℚ)⟩ thresholdNode49 thresholdNode436
def thresholdNode438 : BoxExpr 1 := .mul ⟨(2354081633444449425211/1180591620717411303424:ℚ),(1179187911333731729487/590295810358705651712:ℚ)⟩ thresholdNode5 thresholdNode339
def thresholdNode439 : BoxExpr 1 := .inv ⟨(2363994002163229509103/4722366482869645213696:ℚ),(1184153136498317733493/2361183241434822606848:ℚ)⟩ thresholdNode438
def thresholdNode440 : BoxExpr 1 := .mul ⟨(-45885934039309812173/590295810358705651712:ℚ),(-14405588450682179821/295147905179352825856:ℚ)⟩ thresholdNode437 thresholdNode439
def thresholdNode441 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode432 thresholdNode440
def thresholdNode442 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode427 thresholdNode441
def thresholdNode443 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode335
def thresholdNode444 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode12
def thresholdNode445 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode443 thresholdNode444
def thresholdNode446 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode335 thresholdNode49
def thresholdNode447 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode444 thresholdNode446
def thresholdNode448 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode445 thresholdNode447
def thresholdNode449 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode448
def thresholdNode450 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode49 thresholdNode449
def thresholdNode451 : BoxExpr 1 := .mul ⟨(-1184153136498317733493/1180591620717411303424:ℚ),(-2363994002163229509103/2361183241434822606848:ℚ)⟩ thresholdNode450 thresholdNode439
def thresholdNode452 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode339
def thresholdNode453 : BoxExpr 1 := .mul ⟨(-45885934039309812173/295147905179352825856:ℚ),(-14405588450682179821/147573952589676412928:ℚ)⟩ thresholdNode5 thresholdNode440
def thresholdNode454 : BoxExpr 1 := .add ⟨(-45885934039309812173/295147905179352825856:ℚ),(-14405588450682179821/147573952589676412928:ℚ)⟩ thresholdNode452 thresholdNode453
def thresholdNode455 : BoxExpr 1 := .mul ⟨(18776011076727637628517/4722366482869645213696:ℚ),(18844573935100801289979/4722366482869645213696:ℚ)⟩ thresholdNode438 thresholdNode438
def thresholdNode456 : BoxExpr 1 := .inv ⟨(591702027207741549989/2361183241434822606848:ℚ),(296931349094853791441/1180591620717411303424:ℚ)⟩ thresholdNode455
def thresholdNode457 : BoxExpr 1 := .mul ⟨(-184652807079762069623/4722366482869645213696:ℚ),(-1804988223660565791/73786976294838206464:ℚ)⟩ thresholdNode454 thresholdNode456
def thresholdNode458 : BoxExpr 1 := .neg ⟨(1804988223660565791/73786976294838206464:ℚ),(184652807079762069623/4722366482869645213696:ℚ)⟩ thresholdNode457
def thresholdNode459 : BoxExpr 1 := .mul ⟨(-3577648137170390099/590295810358705651712:ℚ),(-11263126515641930535/4722366482869645213696:ℚ)⟩ thresholdNode437 thresholdNode458
def thresholdNode460 : BoxExpr 1 := .add ⟨(-1191308432772658513691/1180591620717411303424:ℚ),(-4739251130842100948741/4722366482869645213696:ℚ)⟩ thresholdNode451 thresholdNode459
def thresholdNode461 : BoxExpr 1 := .mul ⟨(-774156893681902476891/295147905179352825856:ℚ),(-12318972426954415101105/4722366482869645213696:ℚ)⟩ thresholdNode334 thresholdNode460
def thresholdNode462 : BoxExpr 1 := .add ⟨(-774156893681902476891/295147905179352825856:ℚ),(-12318972426954415101105/4722366482869645213696:ℚ)⟩ thresholdNode441 thresholdNode461
def thresholdNode463 : BoxExpr 1 := .add ⟨(-774156893681902476891/295147905179352825856:ℚ),(-12318972426954415101105/4722366482869645213696:ℚ)⟩ thresholdNode442 thresholdNode462
def thresholdNode464 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode412 thresholdNode22
def thresholdNode465 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode411
def thresholdNode466 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode465 thresholdNode49
def thresholdNode467 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode464 thresholdNode466
def thresholdNode468 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode342 thresholdNode49
def thresholdNode469 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode466 thresholdNode468
def thresholdNode470 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode467 thresholdNode469
def thresholdNode471 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode412 thresholdNode342
def thresholdNode472 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode465 thresholdNode465
def thresholdNode473 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode471 thresholdNode472
def thresholdNode474 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode342 thresholdNode412
def thresholdNode475 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode472 thresholdNode474
def thresholdNode476 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode473 thresholdNode475
def thresholdNode477 : BoxExpr 1 := .mul ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode476 thresholdNode25
def thresholdNode478 : BoxExpr 1 := .mul ⟨(135768036382502299893/4722366482869645213696:ℚ),(271536072765004599789/4722366482869645213696:ℚ)⟩ thresholdNode465 thresholdNode342
def thresholdNode479 : BoxExpr 1 := .mul ⟨(135768036382502299893/4722366482869645213696:ℚ),(271536072765004599789/4722366482869645213696:ℚ)⟩ thresholdNode342 thresholdNode465
def thresholdNode480 : BoxExpr 1 := .add ⟨(135768036382502299893/2361183241434822606848:ℚ),(271536072765004599789/2361183241434822606848:ℚ)⟩ thresholdNode478 thresholdNode479
def thresholdNode481 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode480 thresholdNode49
def thresholdNode482 : BoxExpr 1 := .add ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode477 thresholdNode481
def thresholdNode483 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode344 thresholdNode49
def thresholdNode484 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode481 thresholdNode483
def thresholdNode485 : BoxExpr 1 := .add ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode482 thresholdNode484
def thresholdNode486 : BoxExpr 1 := .add ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode470 thresholdNode485
def thresholdNode487 : BoxExpr 1 := .add ⟨(-4068190232163879468965/2361183241434822606848:ℚ),(-8068842592371734408777/4722366482869645213696:ℚ)⟩ thresholdNode463 thresholdNode486
def thresholdCell1Out0 : TaylorCertificate1 :=
  { center := (101/1600:ℚ), radius := (23/1600:ℚ)
    whole := thresholdNode347, centerValue := thresholdNode367, gradient := thresholdNode403, hessian := thresholdNode487 }
theorem thresholdCell1Out0_check : thresholdCell1Out0.check = true := by decide +kernel
theorem thresholdCell1Out0_lower_pos : 0 < thresholdCell1Out0.lower := by decide +kernel
theorem thresholdCell1Out0_positive (x : ℝ) (hx : (39/800:ℝ) ≤ x ∧ x ≤ (31/400:ℝ)) :
    0 < thresholdNode347.eval (fun _ => x) := by
  apply thresholdCell1Out0.positive_sound thresholdCell1Out0_check thresholdCell1Out0_lower_pos x
  norm_num [thresholdCell1Out0]
  exact hx
def thresholdNode488 : BoxExpr 1 := .mul ⟨(30608619497985128588761/4722366482869645213696:ℚ),(3913261726885274728171/590295810358705651712:ℚ)⟩ thresholdNode347 thresholdNode347
def thresholdNode489 : BoxExpr 1 := .mul ⟨(230215366039895204167/2361183241434822606848:ℚ),(182991701211198752031/1180591620717411303424:ℚ)⟩ thresholdNode335 thresholdNode5
def thresholdNode490 : BoxExpr 1 := .add ⟨(2591398607474717811015/2361183241434822606848:ℚ),(1363583321928610055455/1180591620717411303424:ℚ)⟩ thresholdNode489 thresholdNode12
def thresholdNode491 : BoxExpr 1 := .inv ⟨(4088628989497528323545/4722366482869645213696:ℚ),(2151419809963391896901/2361183241434822606848:ℚ)⟩ thresholdNode490
def thresholdNode492 : BoxExpr 1 := .mul ⟨(304342277573364631669121/2361183241434822606848:ℚ),(640574634345760637044329/4722366482869645213696:ℚ)⟩ thresholdNode171 thresholdNode491
def thresholdNode493 : BoxExpr 1 := .add ⟨(306703460814799454275969/2361183241434822606848:ℚ),(645297000828630282258025/4722366482869645213696:ℚ)⟩ thresholdNode492 thresholdNode12
def thresholdNode494 : BoxExpr 1 := .sqrt ⟨(53821299566843098463505/4722366482869645213696:ℚ),(55202617041309095159221/4722366482869645213696:ℚ)⟩ thresholdNode493
def thresholdNode495 : BoxExpr 1 := .add ⟨(58543666049712743677201/4722366482869645213696:ℚ),(59924983524178740372917/4722366482869645213696:ℚ)⟩ thresholdNode494 thresholdNode12
def thresholdNode496 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode497 : BoxExpr 1 := .mul ⟨(3658979128107046479825/590295810358705651712:ℚ),(29962491762089370186459/4722366482869645213696:ℚ)⟩ thresholdNode495 thresholdNode496
def thresholdNode498 : BoxExpr 1 := .add ⟨(3806553080696722892753/590295810358705651712:ℚ),(31143083382806781489883/4722366482869645213696:ℚ)⟩ thresholdNode497 thresholdNode181
def thresholdNode499 : BoxExpr 1 := .mul ⟨(30269519770046305607025/4722366482869645213696:ℚ),(15534534949352414874125/2361183241434822606848:ℚ)⟩ thresholdNode338 thresholdNode498
def thresholdNode500 : BoxExpr 1 := .neg ⟨(-15534534949352414874125/2361183241434822606848:ℚ),(-30269519770046305607025/4722366482869645213696:ℚ)⟩ thresholdNode499
def thresholdNode501 : BoxExpr 1 := .add ⟨(-460450400719701159489/4722366482869645213696:ℚ),(1036574045035892218343/4722366482869645213696:ℚ)⟩ thresholdNode488 thresholdNode500
def thresholdNode502 : BoxExpr 1 := .mul ⟨(30960659733456406896289/4722366482869645213696:ℚ),(3870082466682050862049/590295810358705651712:ℚ)⟩ thresholdNode367 thresholdNode367
def thresholdNode503 : BoxExpr 1 := .mul ⟨(149049692115573177057/1180591620717411303424:ℚ),(298099384231146354115/2361183241434822606848:ℚ)⟩ thresholdNode355 thresholdNode5
def thresholdNode504 : BoxExpr 1 := .add ⟨(1329641312832984480481/1180591620717411303424:ℚ),(2659282625665968960963/2361183241434822606848:ℚ)⟩ thresholdNode503 thresholdNode12
def thresholdNode505 : BoxExpr 1 := .inv ⟨(4193000206765500744679/4722366482869645213696:ℚ),(2096500103382750372341/2361183241434822606848:ℚ)⟩ thresholdNode504
def thresholdNode506 : BoxExpr 1 := .mul ⟨(624222562658798933767553/4722366482869645213696:ℚ),(624222562658798933768001/4722366482869645213696:ℚ)⟩ thresholdNode171 thresholdNode505
def thresholdNode507 : BoxExpr 1 := .add ⟨(628944929141668578981249/4722366482869645213696:ℚ),(628944929141668578981697/4722366482869645213696:ℚ)⟩ thresholdNode506 thresholdNode12
def thresholdNode508 : BoxExpr 1 := .sqrt ⟨(1703084418366698927117/147573952589676412928:ℚ),(13624675346933591416941/1180591620717411303424:ℚ)⟩ thresholdNode507
def thresholdNode509 : BoxExpr 1 := .add ⟨(1850658370956375340045/147573952589676412928:ℚ),(14805266967651002720365/1180591620717411303424:ℚ)⟩ thresholdNode508 thresholdNode12
def thresholdNode510 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode511 : BoxExpr 1 := .mul ⟨(1850658370956375340045/295147905179352825856:ℚ),(14805266967651002720365/2361183241434822606848:ℚ)⟩ thresholdNode509 thresholdNode510
def thresholdNode512 : BoxExpr 1 := .add ⟨(1924445347251213546509/295147905179352825856:ℚ),(15395562778009708372077/2361183241434822606848:ℚ)⟩ thresholdNode511 thresholdNode181
def thresholdNode513 : BoxExpr 1 := .mul ⟨(15334215068674365780233/2361183241434822606848:ℚ),(30668430137348731560483/4722366482869645213696:ℚ)⟩ thresholdNode358 thresholdNode512
def thresholdNode514 : BoxExpr 1 := .neg ⟨(-30668430137348731560483/4722366482869645213696:ℚ),(-15334215068674365780233/2361183241434822606848:ℚ)⟩ thresholdNode513
def thresholdNode515 : BoxExpr 1 := .add ⟨(146114798053837667903/2361183241434822606848:ℚ),(146114798053837667963/2361183241434822606848:ℚ)⟩ thresholdNode502 thresholdNode514
def thresholdNode516 : BoxExpr 1 := .mul ⟨(-11192007592019405596791/4722366482869645213696:ℚ),(-5596003796009702798373/2361183241434822606848:ℚ)⟩ thresholdNode403 thresholdNode367
def thresholdNode517 : BoxExpr 1 := .mul ⟨(-11192007592019405596791/4722366482869645213696:ℚ),(-5596003796009702798373/2361183241434822606848:ℚ)⟩ thresholdNode367 thresholdNode403
def thresholdNode518 : BoxExpr 1 := .add ⟨(-11192007592019405596791/2361183241434822606848:ℚ),(-5596003796009702798373/1180591620717411303424:ℚ)⟩ thresholdNode516 thresholdNode517
def thresholdNode519 : BoxExpr 1 := .mul ⟨(-971844900361862840989/1180591620717411303424:ℚ),(-971844900361862840985/1180591620717411303424:ℚ)⟩ thresholdNode386 thresholdNode512
def thresholdNode520 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode505
def thresholdNode521 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode522 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode355 thresholdNode49
def thresholdNode523 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode521 thresholdNode522
def thresholdNode524 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode523 thresholdNode49
def thresholdNode525 : BoxExpr 1 := .mul ⟨(5990034114312595084565/4722366482869645213696:ℚ),(5990034114312595084571/4722366482869645213696:ℚ)⟩ thresholdNode504 thresholdNode504
def thresholdNode526 : BoxExpr 1 := .inv ⟨(3722974656395561149547/4722366482869645213696:ℚ),(232685916024722571847/295147905179352825856:ℚ)⟩ thresholdNode525
def thresholdNode527 : BoxExpr 1 := .mul ⟨(3722974656395561149547/2361183241434822606848:ℚ),(232685916024722571847/147573952589676412928:ℚ)⟩ thresholdNode524 thresholdNode526
def thresholdNode528 : BoxExpr 1 := .neg ⟨(-232685916024722571847/147573952589676412928:ℚ),(-3722974656395561149547/2361183241434822606848:ℚ)⟩ thresholdNode527
def thresholdNode529 : BoxExpr 1 := .mul ⟨(-554248668287501827985031/2361183241434822606848:ℚ),(-1108497336575003655968571/4722366482869645213696:ℚ)⟩ thresholdNode171 thresholdNode528
def thresholdNode530 : BoxExpr 1 := .add ⟨(-554248668287501827985031/2361183241434822606848:ℚ),(-1108497336575003655968571/4722366482869645213696:ℚ)⟩ thresholdNode520 thresholdNode529
def thresholdNode531 : BoxExpr 1 := .add ⟨(-554248668287501827985031/2361183241434822606848:ℚ),(-1108497336575003655968571/4722366482869645213696:ℚ)⟩ thresholdNode530 thresholdNode49
def thresholdNode532 : BoxExpr 1 := .mul ⟨(1703084418366698927117/73786976294838206464:ℚ),(13624675346933591416941/590295810358705651712:ℚ)⟩ thresholdNode5 thresholdNode508
def thresholdNode533 : BoxExpr 1 := .inv ⟨(102299433888665523943/2361183241434822606848:ℚ),(204598867777331047887/4722366482869645213696:ℚ)⟩ thresholdNode532
def thresholdNode534 : BoxExpr 1 := .mul ⟨(-3001637272595987989575/295147905179352825856:ℚ),(-12006549090383951958225/1180591620717411303424:ℚ)⟩ thresholdNode531 thresholdNode533
def thresholdNode535 : BoxExpr 1 := .add ⟨(-3001637272595987989575/295147905179352825856:ℚ),(-12006549090383951958225/1180591620717411303424:ℚ)⟩ thresholdNode534 thresholdNode49
def thresholdNode536 : BoxExpr 1 := .mul ⟨(-3001637272595987989575/590295810358705651712:ℚ),(-12006549090383951958225/2361183241434822606848:ℚ)⟩ thresholdNode535 thresholdNode510
def thresholdNode537 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode538 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode537
def thresholdNode539 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode538
def thresholdNode540 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode539
def thresholdNode541 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode509 thresholdNode540
def thresholdNode542 : BoxExpr 1 := .add ⟨(-3001637272595987989575/590295810358705651712:ℚ),(-12006549090383951958225/2361183241434822606848:ℚ)⟩ thresholdNode536 thresholdNode541
def thresholdNode543 : BoxExpr 1 := .add ⟨(-3001637272595987989575/590295810358705651712:ℚ),(-12006549090383951958225/2361183241434822606848:ℚ)⟩ thresholdNode542 thresholdNode49
def thresholdNode544 : BoxExpr 1 := .mul ⟨(-23917411612587429936973/4722366482869645213696:ℚ),(-23917411612587429936817/4722366482869645213696:ℚ)⟩ thresholdNode358 thresholdNode543
def thresholdNode545 : BoxExpr 1 := .add ⟨(-27804791214034881300929/4722366482869645213696:ℚ),(-27804791214034881300757/4722366482869645213696:ℚ)⟩ thresholdNode519 thresholdNode544
def thresholdNode546 : BoxExpr 1 := .neg ⟨(27804791214034881300757/4722366482869645213696:ℚ),(27804791214034881300929/4722366482869645213696:ℚ)⟩ thresholdNode545
def thresholdNode547 : BoxExpr 1 := .add ⟨(5420776029996070107175/4722366482869645213696:ℚ),(5420776029996070107437/4722366482869645213696:ℚ)⟩ thresholdNode518 thresholdNode546
def thresholdNode548 : BoxExpr 1 := .mul ⟨(-10474561475609283176311/2361183241434822606848:ℚ),(-20542498819825764306301/4722366482869645213696:ℚ)⟩ thresholdNode487 thresholdNode347
def thresholdNode549 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode432 thresholdNode339
def thresholdNode550 : BoxExpr 1 := .mul ⟨(-7454600165317497517/36893488147419103232:ℚ),(-599122661428491585883/4722366482869645213696:ℚ)⟩ thresholdNode334 thresholdNode440
def thresholdNode551 : BoxExpr 1 := .add ⟨(-7454600165317497517/36893488147419103232:ℚ),(-599122661428491585883/4722366482869645213696:ℚ)⟩ thresholdNode549 thresholdNode550
def thresholdNode552 : BoxExpr 1 := .mul ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode465 thresholdNode22
def thresholdNode553 : BoxExpr 1 := .add ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode552 thresholdNode468
def thresholdNode554 : BoxExpr 1 := .mul ⟨(122191232744252069903/4722366482869645213696:ℚ),(244382465488504139811/4722366482869645213696:ℚ)⟩ thresholdNode480 thresholdNode25
def thresholdNode555 : BoxExpr 1 := .add ⟨(122191232744252069903/4722366482869645213696:ℚ),(244382465488504139811/4722366482869645213696:ℚ)⟩ thresholdNode554 thresholdNode483
def thresholdNode556 : BoxExpr 1 := .add ⟨(-1827850976775732050527/2361183241434822606848:ℚ),(-3533510720807212031145/4722366482869645213696:ℚ)⟩ thresholdNode553 thresholdNode555
def thresholdNode557 : BoxExpr 1 := .add ⟨(-2304945387356051891615/2361183241434822606848:ℚ),(-1033158345558925904257/1180591620717411303424:ℚ)⟩ thresholdNode551 thresholdNode556
def thresholdNode558 : BoxExpr 1 := .mul ⟨(3616546647517010458467/4722366482869645213696:ℚ),(2250046987232351274693/2361183241434822606848:ℚ)⟩ thresholdNode557 thresholdNode557
def thresholdNode559 : BoxExpr 1 := .add ⟨(-17332576303701555894155/4722366482869645213696:ℚ),(-16042404845361061756915/4722366482869645213696:ℚ)⟩ thresholdNode548 thresholdNode558
def thresholdNode560 : BoxExpr 1 := .mul ⟨(-10474561475609283176311/2361183241434822606848:ℚ),(-20542498819825764306301/4722366482869645213696:ℚ)⟩ thresholdNode347 thresholdNode487
def thresholdNode561 : BoxExpr 1 := .add ⟨(-17332576303701555894155/4722366482869645213696:ℚ),(-16042404845361061756915/4722366482869645213696:ℚ)⟩ thresholdNode558 thresholdNode560
def thresholdNode562 : BoxExpr 1 := .add ⟨(-17332576303701555894155/2361183241434822606848:ℚ),(-16042404845361061756915/2361183241434822606848:ℚ)⟩ thresholdNode559 thresholdNode561
def thresholdNode563 : BoxExpr 1 := .mul ⟨(-31143083382806781489883/2361183241434822606848:ℚ),(-3806553080696722892753/295147905179352825856:ℚ)⟩ thresholdNode450 thresholdNode498
def thresholdNode564 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode491
def thresholdNode565 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode566 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode565 thresholdNode446
def thresholdNode567 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode566 thresholdNode49
def thresholdNode568 : BoxExpr 1 := .mul ⟨(711014992925875699397/590295810358705651712:ℚ),(1574938736827544614051/1180591620717411303424:ℚ)⟩ thresholdNode490 thresholdNode490
def thresholdNode569 : BoxExpr 1 := .inv ⟨(3539938519045479068003/4722366482869645213696:ℚ),(980145699299950750297/1180591620717411303424:ℚ)⟩ thresholdNode568
def thresholdNode570 : BoxExpr 1 := .mul ⟨(3539938519045479068003/2361183241434822606848:ℚ),(980145699299950750297/590295810358705651712:ℚ)⟩ thresholdNode567 thresholdNode569
def thresholdNode571 : BoxExpr 1 := .neg ⟨(-980145699299950750297/590295810358705651712:ℚ),(-3539938519045479068003/2361183241434822606848:ℚ)⟩ thresholdNode570
def thresholdNode572 : BoxExpr 1 := .mul ⟨(-583667092797959578172757/2361183241434822606848:ℚ),(-263499807422826520925547/1180591620717411303424:ℚ)⟩ thresholdNode171 thresholdNode571
def thresholdNode573 : BoxExpr 1 := .add ⟨(-583667092797959578172757/2361183241434822606848:ℚ),(-263499807422826520925547/1180591620717411303424:ℚ)⟩ thresholdNode564 thresholdNode572
def thresholdNode574 : BoxExpr 1 := .add ⟨(-583667092797959578172757/2361183241434822606848:ℚ),(-263499807422826520925547/1180591620717411303424:ℚ)⟩ thresholdNode573 thresholdNode49
def thresholdNode575 : BoxExpr 1 := .mul ⟨(53821299566843098463505/2361183241434822606848:ℚ),(55202617041309095159221/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode494
def thresholdNode576 : BoxExpr 1 := .inv ⟨(50497481808341126497/1180591620717411303424:ℚ),(207173975526495065873/4722366482869645213696:ℚ)⟩ thresholdNode575
def thresholdNode577 : BoxExpr 1 := .mul ⟨(-25605939826479760949153/2361183241434822606848:ℚ),(-45082741562234213636453/4722366482869645213696:ℚ)⟩ thresholdNode574 thresholdNode576
def thresholdNode578 : BoxExpr 1 := .add ⟨(-25605939826479760949153/2361183241434822606848:ℚ),(-45082741562234213636453/4722366482869645213696:ℚ)⟩ thresholdNode577 thresholdNode49
def thresholdNode579 : BoxExpr 1 := .mul ⟨(-25605939826479760949153/4722366482869645213696:ℚ),(-11270685390558553409113/2361183241434822606848:ℚ)⟩ thresholdNode578 thresholdNode496
def thresholdNode580 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode581 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode580
def thresholdNode582 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode581
def thresholdNode583 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode582
def thresholdNode584 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode495 thresholdNode583
def thresholdNode585 : BoxExpr 1 := .add ⟨(-25605939826479760949153/4722366482869645213696:ℚ),(-11270685390558553409113/2361183241434822606848:ℚ)⟩ thresholdNode579 thresholdNode584
def thresholdNode586 : BoxExpr 1 := .add ⟨(-25605939826479760949153/4722366482869645213696:ℚ),(-11270685390558553409113/2361183241434822606848:ℚ)⟩ thresholdNode585 thresholdNode49
def thresholdNode587 : BoxExpr 1 := .mul ⟨(1098891825579458957385/2361183241434822606848:ℚ),(3968920673104362947125/4722366482869645213696:ℚ)⟩ thresholdNode437 thresholdNode586
def thresholdNode588 : BoxExpr 1 := .add ⟨(-15022095778613661266249/1180591620717411303424:ℚ),(-56935928618043203336923/4722366482869645213696:ℚ)⟩ thresholdNode563 thresholdNode587
def thresholdNode589 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode571
def thresholdNode590 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode564 thresholdNode589
def thresholdNode591 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode5
def thresholdNode592 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode12 thresholdNode49
def thresholdNode593 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode591 thresholdNode592
def thresholdNode594 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode592 thresholdNode446
def thresholdNode595 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode593 thresholdNode594
def thresholdNode596 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode595 thresholdNode49
def thresholdNode597 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode596 thresholdNode569
def thresholdNode598 : BoxExpr 1 := .mul ⟨(2591398607474717811015/1180591620717411303424:ℚ),(1363583321928610055455/590295810358705651712:ℚ)⟩ thresholdNode567 thresholdNode490
def thresholdNode599 : BoxExpr 1 := .mul ⟨(2591398607474717811015/1180591620717411303424:ℚ),(1363583321928610055455/590295810358705651712:ℚ)⟩ thresholdNode490 thresholdNode567
def thresholdNode600 : BoxExpr 1 := .add ⟨(2591398607474717811015/590295810358705651712:ℚ),(1363583321928610055455/295147905179352825856:ℚ)⟩ thresholdNode598 thresholdNode599
def thresholdNode601 : BoxExpr 1 := .mul ⟨(3425688011291692266585/2361183241434822606848:ℚ),(4202015296792730407521/2361183241434822606848:ℚ)⟩ thresholdNode568 thresholdNode568
def thresholdNode602 : BoxExpr 1 := .inv ⟨(331697168254481650269/590295810358705651712:ℚ),(3254929393018760177617/4722366482869645213696:ℚ)⟩ thresholdNode601
def thresholdNode603 : BoxExpr 1 := .mul ⟨(2912301137274348889361/1180591620717411303424:ℚ),(7518886897873336010297/2361183241434822606848:ℚ)⟩ thresholdNode600 thresholdNode602
def thresholdNode604 : BoxExpr 1 := .neg ⟨(-7518886897873336010297/2361183241434822606848:ℚ),(-2912301137274348889361/1180591620717411303424:ℚ)⟩ thresholdNode603
def thresholdNode605 : BoxExpr 1 := .mul ⟨(-7518886897873336010297/1180591620717411303424:ℚ),(-2912301137274348889361/590295810358705651712:ℚ)⟩ thresholdNode567 thresholdNode604
def thresholdNode606 : BoxExpr 1 := .add ⟨(-7518886897873336010297/1180591620717411303424:ℚ),(-2912301137274348889361/590295810358705651712:ℚ)⟩ thresholdNode597 thresholdNode605
def thresholdNode607 : BoxExpr 1 := .neg ⟨(2912301137274348889361/590295810358705651712:ℚ),(7518886897873336010297/1180591620717411303424:ℚ)⟩ thresholdNode606
def thresholdNode608 : BoxExpr 1 := .mul ⟨(3468493182919985538088459/4722366482869645213696:ℚ),(2238711479269263443971897/2361183241434822606848:ℚ)⟩ thresholdNode171 thresholdNode607
def thresholdNode609 : BoxExpr 1 := .add ⟨(3468493182919985538088459/4722366482869645213696:ℚ),(2238711479269263443971897/2361183241434822606848:ℚ)⟩ thresholdNode589 thresholdNode608
def thresholdNode610 : BoxExpr 1 := .add ⟨(3468493182919985538088459/4722366482869645213696:ℚ),(2238711479269263443971897/2361183241434822606848:ℚ)⟩ thresholdNode590 thresholdNode609
def thresholdNode611 : BoxExpr 1 := .add ⟨(3468493182919985538088459/4722366482869645213696:ℚ),(2238711479269263443971897/2361183241434822606848:ℚ)⟩ thresholdNode610 thresholdNode49
def thresholdNode612 : BoxExpr 1 := .mul ⟨(37089491474711530493029/1180591620717411303424:ℚ),(98214054097549510918019/2361183241434822606848:ℚ)⟩ thresholdNode611 thresholdNode576
def thresholdNode613 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode494
def thresholdNode614 : BoxExpr 1 := .mul ⟨(-25605939826479760949153/1180591620717411303424:ℚ),(-45082741562234213636453/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode577
def thresholdNode615 : BoxExpr 1 := .add ⟨(-25605939826479760949153/1180591620717411303424:ℚ),(-45082741562234213636453/2361183241434822606848:ℚ)⟩ thresholdNode613 thresholdNode614
def thresholdNode616 : BoxExpr 1 := .mul ⟨(1226813843259197817103855/2361183241434822606848:ℚ),(322648500414315141129013/590295810358705651712:ℚ)⟩ thresholdNode575 thresholdNode575
def thresholdNode617 : BoxExpr 1 := .inv ⟨(4319860693970002195/2361183241434822606848:ℚ),(4544443584709979449/2361183241434822606848:ℚ)⟩ thresholdNode616
def thresholdNode618 : BoxExpr 1 := .mul ⟨(-197129552561459362853/4722366482869645213696:ℚ),(-2577510184215397801/73786976294838206464:ℚ)⟩ thresholdNode615 thresholdNode617
def thresholdNode619 : BoxExpr 1 := .neg ⟨(2577510184215397801/73786976294838206464:ℚ),(197129552561459362853/4722366482869645213696:ℚ)⟩ thresholdNode618
def thresholdNode620 : BoxExpr 1 := .mul ⟨(-48728972334308167072275/4722366482869645213696:ℚ),(-9204516450942349352675/1180591620717411303424:ℚ)⟩ thresholdNode574 thresholdNode619
def thresholdNode621 : BoxExpr 1 := .add ⟨(99628993564537954899841/4722366482869645213696:ℚ),(79805021195664812212669/2361183241434822606848:ℚ)⟩ thresholdNode612 thresholdNode620
def thresholdNode622 : BoxExpr 1 := .add ⟨(99628993564537954899841/4722366482869645213696:ℚ),(79805021195664812212669/2361183241434822606848:ℚ)⟩ thresholdNode621 thresholdNode49
def thresholdNode623 : BoxExpr 1 := .mul ⟨(778351512222952772655/73786976294838206464:ℚ),(79805021195664812212669/4722366482869645213696:ℚ)⟩ thresholdNode622 thresholdNode496
def thresholdNode624 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode578 thresholdNode583
def thresholdNode625 : BoxExpr 1 := .add ⟨(778351512222952772655/73786976294838206464:ℚ),(79805021195664812212669/4722366482869645213696:ℚ)⟩ thresholdNode623 thresholdNode624
def thresholdNode626 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode5 thresholdNode49
def thresholdNode627 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode591 thresholdNode626
def thresholdNode628 : BoxExpr 1 := .mul ⟨(16/1:ℚ),(16/1:ℚ)⟩ thresholdNode580 thresholdNode580
def thresholdNode629 : BoxExpr 1 := .inv ⟨(1/16:ℚ),(1/16:ℚ)⟩ thresholdNode628
def thresholdNode630 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode627 thresholdNode629
def thresholdNode631 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode630
def thresholdNode632 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode631
def thresholdNode633 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode582 thresholdNode632
def thresholdNode634 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode633
def thresholdNode635 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode495 thresholdNode634
def thresholdNode636 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode624 thresholdNode635
def thresholdNode637 : BoxExpr 1 := .add ⟨(778351512222952772655/73786976294838206464:ℚ),(79805021195664812212669/4722366482869645213696:ℚ)⟩ thresholdNode625 thresholdNode636
def thresholdNode638 : BoxExpr 1 := .add ⟨(778351512222952772655/73786976294838206464:ℚ),(79805021195664812212669/4722366482869645213696:ℚ)⟩ thresholdNode637 thresholdNode49
def thresholdNode639 : BoxExpr 1 := .mul ⟨(12378824615242618601027/1180591620717411303424:ℚ),(39807679787489745028699/2361183241434822606848:ℚ)⟩ thresholdNode338 thresholdNode638
def thresholdNode640 : BoxExpr 1 := .add ⟨(25856541056064696159439/2361183241434822606848:ℚ),(83584280248083853004523/4722366482869645213696:ℚ)⟩ thresholdNode587 thresholdNode639
def thresholdNode641 : BoxExpr 1 := .add ⟨(-4187650501162626373059/2361183241434822606848:ℚ),(1665521976877540604225/295147905179352825856:ℚ)⟩ thresholdNode588 thresholdNode640
def thresholdNode642 : BoxExpr 1 := .neg ⟨(-1665521976877540604225/295147905179352825856:ℚ),(4187650501162626373059/2361183241434822606848:ℚ)⟩ thresholdNode641
def thresholdNode643 : BoxExpr 1 := .add ⟨(-30656752118721880727955/2361183241434822606848:ℚ),(-740922146512402211491/147573952589676412928:ℚ)⟩ thresholdNode562 thresholdNode642
def thresholdCell1Out1 : TaylorCertificate1 :=
  { center := (101/1600:ℚ), radius := (23/1600:ℚ)
    whole := thresholdNode501, centerValue := thresholdNode515, gradient := thresholdNode547, hessian := thresholdNode643 }
theorem thresholdCell1Out1_check : thresholdCell1Out1.check = true := by decide +kernel
theorem thresholdCell1Out1_lower_pos : 0 < thresholdCell1Out1.lower := by decide +kernel
theorem thresholdCell1Out1_positive (x : ℝ) (hx : (39/800:ℝ) ≤ x ∧ x ≤ (31/400:ℝ)) :
    0 < thresholdNode501.eval (fun _ => x) := by
  apply thresholdCell1Out1.positive_sound thresholdCell1Out1_check thresholdCell1Out1_lower_pos x
  norm_num [thresholdCell1Out1]
  exact hx
theorem thresholdCell1_public (x : ℝ)
    (hx : (39/800:ℝ) ≤ x ∧ x ≤ (31/400:ℝ)) : qc x < fA (43/20) x := by
  have hf := thresholdCell1Out0_positive x hx
  have hg := thresholdCell1Out1_positive x hx
  have hfa : thresholdNode347.eval (fun _ => x) = thresholdFA 2 x := by
    norm_num [thresholdNode0, thresholdNode1, thresholdNode328, thresholdNode3, thresholdNode329, thresholdNode5, thresholdNode330, thresholdNode331, thresholdNode332, thresholdNode9, thresholdNode333, thresholdNode334, thresholdNode12, thresholdNode335, thresholdNode336, thresholdNode337, thresholdNode338, thresholdNode339, thresholdNode340, thresholdNode19, thresholdNode341, thresholdNode342, thresholdNode22, thresholdNode343, thresholdNode344, thresholdNode25, thresholdNode345, thresholdNode346, thresholdNode347, BoxExpr.eval, thresholdFA, ftilde, pow_two, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  have hgap : thresholdNode501.eval (fun _ => x) =
      (thresholdNode347.eval (fun _ => x))^2 - (1-x^2)*(thresholdCapacity 3 x+1/4) := by
    norm_num [thresholdNode488, thresholdNode12, thresholdNode335, thresholdNode336, thresholdNode337, thresholdNode338, thresholdNode171, thresholdNode5, thresholdNode489, thresholdNode490, thresholdNode491, thresholdNode492, thresholdNode493, thresholdNode494, thresholdNode495, thresholdNode496, thresholdNode497, thresholdNode181, thresholdNode498, thresholdNode499, thresholdNode500, thresholdNode501, BoxExpr.eval, thresholdCapacity, Da, D5, beta5, eta5, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  rw [hfa] at hf
  rw [hgap, hfa] at hg
  refine threshold_positive_to_public 2 3 x ?_ ?_ ?_ hf hg
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdFADomain] <;> constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdCapacityDomain] <;> constructor <;> linarith [hx.1,hx.2]
def thresholdNode644 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode645 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode644 thresholdNode3
def thresholdNode646 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode647 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode646
def thresholdNode648 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode647 thresholdNode647
def thresholdNode649 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode648 thresholdNode9
def thresholdNode650 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode645 thresholdNode649
def thresholdNode651 : BoxExpr 1 := .var 0
def thresholdNode652 : BoxExpr 1 := .mul ⟨(7090928421933951641/1180591620717411303424:ℚ),(21516282287574821005/1180591620717411303424:ℚ)⟩ thresholdNode651 thresholdNode651
def thresholdNode653 : BoxExpr 1 := .neg ⟨(-21516282287574821005/1180591620717411303424:ℚ),(-7090928421933951641/1180591620717411303424:ℚ)⟩ thresholdNode652
def thresholdNode654 : BoxExpr 1 := .add ⟨(1159075338429836482419/1180591620717411303424:ℚ),(1173500692295477351783/1180591620717411303424:ℚ)⟩ thresholdNode12 thresholdNode653
def thresholdNode655 : BoxExpr 1 := .sqrt ⟨(2339568021948037020505/2361183241434822606848:ℚ),(588520408361112356303/590295810358705651712:ℚ)⟩ thresholdNode654
def thresholdNode656 : BoxExpr 1 := .mul ⟨(6081356137850630029247/2361183241434822606848:ℚ),(6119082093893829613427/2361183241434822606848:ℚ)⟩ thresholdNode650 thresholdNode655
def thresholdNode657 : BoxExpr 1 := .neg ⟨(-47223664828696452137/2361183241434822606848:ℚ),(-94447329657392904273/4722366482869645213696:ℚ)⟩ thresholdNode19
def thresholdNode658 : BoxExpr 1 := .add ⟨(271536072765004599787/4722366482869645213696:ℚ),(67884018191251149947/590295810358705651712:ℚ)⟩ thresholdNode651 thresholdNode657
def thresholdNode659 : BoxExpr 1 := .mul ⟨(-434457716424007359661/4722366482869645213696:ℚ),(-217228858212003679829/4722366482869645213696:ℚ)⟩ thresholdNode658 thresholdNode22
def thresholdNode660 : BoxExpr 1 := .mul ⟨(15613324183987764487/4722366482869645213696:ℚ),(1951665522998470561/147573952589676412928:ℚ)⟩ thresholdNode658 thresholdNode658
def thresholdNode661 : BoxExpr 1 := .mul ⟨(7025995882794494019/4722366482869645213696:ℚ),(28103983531177976079/4722366482869645213696:ℚ)⟩ thresholdNode660 thresholdNode25
def thresholdNode662 : BoxExpr 1 := .add ⟨(-213715860270606432821/2361183241434822606848:ℚ),(-94562437340412851875/2361183241434822606848:ℚ)⟩ thresholdNode659 thresholdNode661
def thresholdNode663 : BoxExpr 1 := .add ⟨(2933820138790011798213/1180591620717411303424:ℚ),(376532478534588547597/147573952589676412928:ℚ)⟩ thresholdNode656 thresholdNode662
def thresholdNode664 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode665 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode664 thresholdNode3
def thresholdNode666 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode667 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode666
def thresholdNode668 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode667 thresholdNode667
def thresholdNode669 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode668 thresholdNode9
def thresholdNode670 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode665 thresholdNode669
def thresholdNode671 : BoxExpr 1 := .var 0
def thresholdNode672 : BoxExpr 1 := .mul ⟨(26655545186510302085/2361183241434822606848:ℚ),(53311090373020604171/4722366482869645213696:ℚ)⟩ thresholdNode671 thresholdNode671
def thresholdNode673 : BoxExpr 1 := .neg ⟨(-53311090373020604171/4722366482869645213696:ℚ),(-26655545186510302085/2361183241434822606848:ℚ)⟩ thresholdNode672
def thresholdNode674 : BoxExpr 1 := .add ⟨(4669055392496624609525/4722366482869645213696:ℚ),(2334527696248312304763/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode673
def thresholdNode675 : BoxExpr 1 := .sqrt ⟨(4695635281001691684593/4722366482869645213696:ℚ),(4695635281001691684595/4722366482869645213696:ℚ)⟩ thresholdNode674
def thresholdNode676 : BoxExpr 1 := .mul ⟨(6102799783835873640171/2361183241434822606848:ℚ),(12205599567671747280357/4722366482869645213696:ℚ)⟩ thresholdNode670 thresholdNode675
def thresholdNode677 : BoxExpr 1 := .neg ⟨(-47223664828696452137/2361183241434822606848:ℚ),(-94447329657392904273/4722366482869645213696:ℚ)⟩ thresholdNode19
def thresholdNode678 : BoxExpr 1 := .add ⟨(407304109147506899681/4722366482869645213696:ℚ),(407304109147506899683/4722366482869645213696:ℚ)⟩ thresholdNode671 thresholdNode677
def thresholdNode679 : BoxExpr 1 := .mul ⟨(-325843287318005519747/4722366482869645213696:ℚ),(-2545650682171918123/36893488147419103232:ℚ)⟩ thresholdNode678 thresholdNode22
def thresholdNode680 : BoxExpr 1 := .mul ⟨(35129979413972470097/4722366482869645213696:ℚ),(17564989706986235049/2361183241434822606848:ℚ)⟩ thresholdNode678 thresholdNode678
def thresholdNode681 : BoxExpr 1 := .mul ⟨(15808490736287611543/4722366482869645213696:ℚ),(15808490736287611545/4722366482869645213696:ℚ)⟩ thresholdNode680 thresholdNode25
def thresholdNode682 : BoxExpr 1 := .add ⟨(-77508699145429477051/1180591620717411303424:ℚ),(-310034796581717908199/4722366482869645213696:ℚ)⟩ thresholdNode679 thresholdNode681
def thresholdNode683 : BoxExpr 1 := .add ⟨(5947782385545014686069/2361183241434822606848:ℚ),(5947782385545014686079/2361183241434822606848:ℚ)⟩ thresholdNode676 thresholdNode682
def thresholdNode684 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode1
def thresholdNode685 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode49
def thresholdNode686 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode684 thresholdNode685
def thresholdNode687 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode686 thresholdNode49
def thresholdNode688 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49
def thresholdNode689 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode688
def thresholdNode690 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode689 thresholdNode667
def thresholdNode691 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode667 thresholdNode689
def thresholdNode692 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode690 thresholdNode691
def thresholdNode693 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode692 thresholdNode9
def thresholdNode694 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode668 thresholdNode49
def thresholdNode695 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode693 thresholdNode694
def thresholdNode696 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode687 thresholdNode695
def thresholdNode697 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode696 thresholdNode675
def thresholdNode698 : BoxExpr 1 := .mul ⟨(501751438804899803955/4722366482869645213696:ℚ),(125437859701224950989/1180591620717411303424:ℚ)⟩ thresholdNode12 thresholdNode671
def thresholdNode699 : BoxExpr 1 := .mul ⟨(501751438804899803955/4722366482869645213696:ℚ),(125437859701224950989/1180591620717411303424:ℚ)⟩ thresholdNode671 thresholdNode12
def thresholdNode700 : BoxExpr 1 := .add ⟨(501751438804899803955/2361183241434822606848:ℚ),(125437859701224950989/590295810358705651712:ℚ)⟩ thresholdNode698 thresholdNode699
def thresholdNode701 : BoxExpr 1 := .neg ⟨(-125437859701224950989/590295810358705651712:ℚ),(-501751438804899803955/2361183241434822606848:ℚ)⟩ thresholdNode700
def thresholdNode702 : BoxExpr 1 := .add ⟨(-125437859701224950989/590295810358705651712:ℚ),(-501751438804899803955/2361183241434822606848:ℚ)⟩ thresholdNode49 thresholdNode701
def thresholdNode703 : BoxExpr 1 := .mul ⟨(4695635281001691684593/2361183241434822606848:ℚ),(4695635281001691684595/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode675
def thresholdNode704 : BoxExpr 1 := .inv ⟨(2374624929746815754525/4722366482869645213696:ℚ),(2374624929746815754527/4722366482869645213696:ℚ)⟩ thresholdNode703
def thresholdNode705 : BoxExpr 1 := .mul ⟨(-252303898785599173919/2361183241434822606848:ℚ),(-126151949392799586959/1180591620717411303424:ℚ)⟩ thresholdNode702 thresholdNode704
def thresholdNode706 : BoxExpr 1 := .mul ⟨(-655826139308347212727/2361183241434822606848:ℚ),(-1311652278616694425447/4722366482869645213696:ℚ)⟩ thresholdNode670 thresholdNode705
def thresholdNode707 : BoxExpr 1 := .add ⟨(-655826139308347212727/2361183241434822606848:ℚ),(-1311652278616694425447/4722366482869645213696:ℚ)⟩ thresholdNode697 thresholdNode706
def thresholdNode708 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode688
def thresholdNode709 : BoxExpr 1 := .mul ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode708 thresholdNode22
def thresholdNode710 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode678 thresholdNode49
def thresholdNode711 : BoxExpr 1 := .add ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode709 thresholdNode710
def thresholdNode712 : BoxExpr 1 := .mul ⟨(407304109147506899681/4722366482869645213696:ℚ),(407304109147506899683/4722366482869645213696:ℚ)⟩ thresholdNode708 thresholdNode678
def thresholdNode713 : BoxExpr 1 := .mul ⟨(407304109147506899681/4722366482869645213696:ℚ),(407304109147506899683/4722366482869645213696:ℚ)⟩ thresholdNode678 thresholdNode708
def thresholdNode714 : BoxExpr 1 := .add ⟨(407304109147506899681/2361183241434822606848:ℚ),(407304109147506899683/2361183241434822606848:ℚ)⟩ thresholdNode712 thresholdNode713
def thresholdNode715 : BoxExpr 1 := .mul ⟨(22910856139547263107/295147905179352825856:ℚ),(366573698232756209715/4722366482869645213696:ℚ)⟩ thresholdNode714 thresholdNode25
def thresholdNode716 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode680 thresholdNode49
def thresholdNode717 : BoxExpr 1 := .add ⟨(22910856139547263107/295147905179352825856:ℚ),(366573698232756209715/4722366482869645213696:ℚ)⟩ thresholdNode715 thresholdNode716
def thresholdNode718 : BoxExpr 1 := .add ⟨(-3411319488062959961245/4722366482869645213696:ℚ),(-3411319488062959961241/4722366482869645213696:ℚ)⟩ thresholdNode711 thresholdNode717
def thresholdNode719 : BoxExpr 1 := .add ⟨(-4722971766679654386699/4722366482869645213696:ℚ),(-4612277115898099987/4611686018427387904:ℚ)⟩ thresholdNode707 thresholdNode718
def thresholdNode720 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode1
def thresholdNode721 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode49
def thresholdNode722 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode720 thresholdNode721
def thresholdNode723 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode49
def thresholdNode724 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode721 thresholdNode723
def thresholdNode725 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode722 thresholdNode724
def thresholdNode726 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode725 thresholdNode49
def thresholdNode727 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49
def thresholdNode728 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode727
def thresholdNode729 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode728 thresholdNode647
def thresholdNode730 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode728 thresholdNode728
def thresholdNode731 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode729 thresholdNode730
def thresholdNode732 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode647 thresholdNode728
def thresholdNode733 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode730 thresholdNode732
def thresholdNode734 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode731 thresholdNode733
def thresholdNode735 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode734 thresholdNode9
def thresholdNode736 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode729 thresholdNode732
def thresholdNode737 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode736 thresholdNode49
def thresholdNode738 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode735 thresholdNode737
def thresholdNode739 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode648 thresholdNode49
def thresholdNode740 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode737 thresholdNode739
def thresholdNode741 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode738 thresholdNode740
def thresholdNode742 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode726 thresholdNode741
def thresholdNode743 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode742 thresholdNode655
def thresholdNode744 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode720 thresholdNode723
def thresholdNode745 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode744 thresholdNode49
def thresholdNode746 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode736 thresholdNode9
def thresholdNode747 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode746 thresholdNode739
def thresholdNode748 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode745 thresholdNode747
def thresholdNode749 : BoxExpr 1 := .mul ⟨(365983402422397504061/4722366482869645213696:ℚ),(637519475187402103849/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode651
def thresholdNode750 : BoxExpr 1 := .mul ⟨(365983402422397504061/4722366482869645213696:ℚ),(637519475187402103849/4722366482869645213696:ℚ)⟩ thresholdNode651 thresholdNode12
def thresholdNode751 : BoxExpr 1 := .add ⟨(365983402422397504061/2361183241434822606848:ℚ),(637519475187402103849/2361183241434822606848:ℚ)⟩ thresholdNode749 thresholdNode750
def thresholdNode752 : BoxExpr 1 := .neg ⟨(-637519475187402103849/2361183241434822606848:ℚ),(-365983402422397504061/2361183241434822606848:ℚ)⟩ thresholdNode751
def thresholdNode753 : BoxExpr 1 := .add ⟨(-637519475187402103849/2361183241434822606848:ℚ),(-365983402422397504061/2361183241434822606848:ℚ)⟩ thresholdNode49 thresholdNode752
def thresholdNode754 : BoxExpr 1 := .mul ⟨(2339568021948037020505/1180591620717411303424:ℚ),(588520408361112356303/295147905179352825856:ℚ)⟩ thresholdNode5 thresholdNode655
def thresholdNode755 : BoxExpr 1 := .inv ⟨(296038284124579433373/590295810358705651712:ℚ),(2382998163477412870063/4722366482869645213696:ℚ)⟩ thresholdNode754
def thresholdNode756 : BoxExpr 1 := .mul ⟨(-321704752069450737459/2361183241434822606848:ℚ),(-183543736157239248691/2361183241434822606848:ℚ)⟩ thresholdNode753 thresholdNode755
def thresholdNode757 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode748 thresholdNode756
def thresholdNode758 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode743 thresholdNode757
def thresholdNode759 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode651
def thresholdNode760 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode12
def thresholdNode761 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode759 thresholdNode760
def thresholdNode762 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode651 thresholdNode49
def thresholdNode763 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode760 thresholdNode762
def thresholdNode764 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode761 thresholdNode763
def thresholdNode765 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode764
def thresholdNode766 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode49 thresholdNode765
def thresholdNode767 : BoxExpr 1 := .mul ⟨(-2382998163477412870063/2361183241434822606848:ℚ),(-296038284124579433373/295147905179352825856:ℚ)⟩ thresholdNode766 thresholdNode755
def thresholdNode768 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode655
def thresholdNode769 : BoxExpr 1 := .mul ⟨(-321704752069450737459/1180591620717411303424:ℚ),(-183543736157239248691/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode756
def thresholdNode770 : BoxExpr 1 := .add ⟨(-321704752069450737459/1180591620717411303424:ℚ),(-183543736157239248691/1180591620717411303424:ℚ)⟩ thresholdNode768 thresholdNode769
def thresholdNode771 : BoxExpr 1 := .mul ⟨(18545205414877383718701/4722366482869645213696:ℚ),(9388005538363818814267/2361183241434822606848:ℚ)⟩ thresholdNode754 thresholdNode754
def thresholdNode772 : BoxExpr 1 := .inv ⟨(593862698189707582881/2361183241434822606848:ℚ),(18789176821277330973/73786976294838206464:ℚ)⟩ thresholdNode771
def thresholdNode773 : BoxExpr 1 := .mul ⟨(-327676659183062043197/4722366482869645213696:ℚ),(-184652807079762069621/4722366482869645213696:ℚ)⟩ thresholdNode770 thresholdNode772
def thresholdNode774 : BoxExpr 1 := .neg ⟨(184652807079762069621/4722366482869645213696:ℚ),(327676659183062043197/4722366482869645213696:ℚ)⟩ thresholdNode773
def thresholdNode775 : BoxExpr 1 := .mul ⟨(-5529543623714171979/295147905179352825856:ℚ),(-28621185097363120791/4722366482869645213696:ℚ)⟩ thresholdNode753 thresholdNode774
def thresholdNode776 : BoxExpr 1 := .add ⟨(-2427234512467126245895/2361183241434822606848:ℚ),(-4765233731090634054759/4722366482869645213696:ℚ)⟩ thresholdNode767 thresholdNode775
def thresholdNode777 : BoxExpr 1 := .mul ⟨(-12618464059962849214539/4722366482869645213696:ℚ),(-12386510298910439630233/4722366482869645213696:ℚ)⟩ thresholdNode650 thresholdNode776
def thresholdNode778 : BoxExpr 1 := .add ⟨(-12618464059962849214539/4722366482869645213696:ℚ),(-12386510298910439630233/4722366482869645213696:ℚ)⟩ thresholdNode757 thresholdNode777
def thresholdNode779 : BoxExpr 1 := .add ⟨(-12618464059962849214539/4722366482869645213696:ℚ),(-12386510298910439630233/4722366482869645213696:ℚ)⟩ thresholdNode758 thresholdNode778
def thresholdNode780 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode728 thresholdNode22
def thresholdNode781 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode727
def thresholdNode782 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode781 thresholdNode49
def thresholdNode783 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode780 thresholdNode782
def thresholdNode784 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode658 thresholdNode49
def thresholdNode785 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode782 thresholdNode784
def thresholdNode786 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode783 thresholdNode785
def thresholdNode787 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode728 thresholdNode658
def thresholdNode788 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode781 thresholdNode781
def thresholdNode789 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode787 thresholdNode788
def thresholdNode790 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode658 thresholdNode728
def thresholdNode791 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode788 thresholdNode790
def thresholdNode792 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode789 thresholdNode791
def thresholdNode793 : BoxExpr 1 := .mul ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode792 thresholdNode25
def thresholdNode794 : BoxExpr 1 := .mul ⟨(271536072765004599787/4722366482869645213696:ℚ),(67884018191251149947/590295810358705651712:ℚ)⟩ thresholdNode781 thresholdNode658
def thresholdNode795 : BoxExpr 1 := .mul ⟨(271536072765004599787/4722366482869645213696:ℚ),(67884018191251149947/590295810358705651712:ℚ)⟩ thresholdNode658 thresholdNode781
def thresholdNode796 : BoxExpr 1 := .add ⟨(271536072765004599787/2361183241434822606848:ℚ),(67884018191251149947/295147905179352825856:ℚ)⟩ thresholdNode794 thresholdNode795
def thresholdNode797 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode796 thresholdNode49
def thresholdNode798 : BoxExpr 1 := .add ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode793 thresholdNode797
def thresholdNode799 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode660 thresholdNode49
def thresholdNode800 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode797 thresholdNode799
def thresholdNode801 : BoxExpr 1 := .add ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode798 thresholdNode800
def thresholdNode802 : BoxExpr 1 := .add ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode786 thresholdNode801
def thresholdNode803 : BoxExpr 1 := .add ⟨(-8368334225380168522213/4722366482869645213696:ℚ),(-8136380464327758937905/4722366482869645213696:ℚ)⟩ thresholdNode779 thresholdNode802
def thresholdCell2Out0 : TaylorCertificate1 :=
  { center := (17/160:ℚ), radius := (23/800:ℚ)
    whole := thresholdNode663, centerValue := thresholdNode683, gradient := thresholdNode719, hessian := thresholdNode803 }
theorem thresholdCell2Out0_check : thresholdCell2Out0.check = true := by decide +kernel
theorem thresholdCell2Out0_lower_pos : 0 < thresholdCell2Out0.lower := by decide +kernel
theorem thresholdCell2Out0_positive (x : ℝ) (hx : (31/400:ℝ) ≤ x ∧ x ≤ (27/200:ℝ)) :
    0 < thresholdNode663.eval (fun _ => x) := by
  apply thresholdCell2Out0.positive_sound thresholdCell2Out0_check thresholdCell2Out0_lower_pos x
  norm_num [thresholdCell2Out0]
  exact hx
def thresholdNode804 : BoxExpr 1 := .mul ⟨(14581334401711977306661/2361183241434822606848:ℚ),(1921432677019974650081/295147905179352825856:ℚ)⟩ thresholdNode663 thresholdNode663
def thresholdNode805 : BoxExpr 1 := .mul ⟨(365983402422397504061/2361183241434822606848:ℚ),(637519475187402103849/2361183241434822606848:ℚ)⟩ thresholdNode651 thresholdNode5
def thresholdNode806 : BoxExpr 1 := .add ⟨(2727166643857220110909/2361183241434822606848:ℚ),(2998702716622224710697/2361183241434822606848:ℚ)⟩ thresholdNode805 thresholdNode12
def thresholdNode807 : BoxExpr 1 := .inv ⟨(3718398805409169459603/4722366482869645213696:ℚ),(4088628989497528323547/4722366482869645213696:ℚ)⟩ thresholdNode806
def thresholdNode808 : BoxExpr 1 := .mul ⟨(553567449759427007209345/4722366482869645213696:ℚ),(304342277573364631669271/2361183241434822606848:ℚ)⟩ thresholdNode171 thresholdNode807
def thresholdNode809 : BoxExpr 1 := .add ⟨(558289816242296652423041/4722366482869645213696:ℚ),(306703460814799454276119/2361183241434822606848:ℚ)⟩ thresholdNode808 thresholdNode12
def thresholdNode810 : BoxExpr 1 := .sqrt ⟨(51346364194070011763545/4722366482869645213696:ℚ),(53821299566843098463519/4722366482869645213696:ℚ)⟩ thresholdNode809
def thresholdNode811 : BoxExpr 1 := .add ⟨(56068730676939656977241/4722366482869645213696:ℚ),(58543666049712743677215/4722366482869645213696:ℚ)⟩ thresholdNode810 thresholdNode12
def thresholdNode812 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode813 : BoxExpr 1 := .mul ⟨(7008591334617457122155/1180591620717411303424:ℚ),(1829489564053523239913/295147905179352825856:ℚ)⟩ thresholdNode811 thresholdNode812
def thresholdNode814 : BoxExpr 1 := .add ⟨(7303739239796809948011/1180591620717411303424:ℚ),(1903276540348361446377/295147905179352825856:ℚ)⟩ thresholdNode813 thresholdNode181
def thresholdNode815 : BoxExpr 1 := .mul ⟨(28682514368606052346831/4722366482869645213696:ℚ),(30269519770046305607041/4722366482869645213696:ℚ)⟩ thresholdNode654 thresholdNode814
def thresholdNode816 : BoxExpr 1 := .neg ⟨(-30269519770046305607041/4722366482869645213696:ℚ),(-28682514368606052346831/4722366482869645213696:ℚ)⟩ thresholdNode815
def thresholdNode817 : BoxExpr 1 := .add ⟨(-1106850966622350993719/4722366482869645213696:ℚ),(2060408463713542054465/4722366482869645213696:ℚ)⟩ thresholdNode804 thresholdNode816
def thresholdNode818 : BoxExpr 1 := .mul ⟨(29964735209879353523073/4722366482869645213696:ℚ),(14982367604939676761587/2361183241434822606848:ℚ)⟩ thresholdNode683 thresholdNode683
def thresholdNode819 : BoxExpr 1 := .mul ⟨(501751438804899803955/2361183241434822606848:ℚ),(125437859701224950989/590295810358705651712:ℚ)⟩ thresholdNode671 thresholdNode5
def thresholdNode820 : BoxExpr 1 := .add ⟨(2862934680239722410803/2361183241434822606848:ℚ),(715733670059930602701/590295810358705651712:ℚ)⟩ thresholdNode819 thresholdNode12
def thresholdNode821 : BoxExpr 1 := .inv ⟨(1947367621801915552039/2361183241434822606848:ℚ),(243420952725239444005/295147905179352825856:ℚ)⟩ thresholdNode820
def thresholdNode822 : BoxExpr 1 := .mul ⟨(144954775504014907042409/1180591620717411303424:ℚ),(36238693876003726760621/295147905179352825856:ℚ)⟩ thresholdNode171 thresholdNode821
def thresholdNode823 : BoxExpr 1 := .add ⟨(146135367124732318345833/1180591620717411303424:ℚ),(36533841781183079586477/295147905179352825856:ℚ)⟩ thresholdNode822 thresholdNode12
def thresholdNode824 : BoxExpr 1 := .sqrt ⟨(52539690127433623300419/4722366482869645213696:ℚ),(26269845063716811650217/2361183241434822606848:ℚ)⟩ thresholdNode823
def thresholdNode825 : BoxExpr 1 := .add ⟨(57262056610303268514115/4722366482869645213696:ℚ),(28631028305151634257065/2361183241434822606848:ℚ)⟩ thresholdNode824 thresholdNode12
def thresholdNode826 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode827 : BoxExpr 1 := .mul ⟨(28631028305151634257057/4722366482869645213696:ℚ),(28631028305151634257065/4722366482869645213696:ℚ)⟩ thresholdNode825 thresholdNode826
def thresholdNode828 : BoxExpr 1 := .add ⟨(29811619925869045560481/4722366482869645213696:ℚ),(29811619925869045560489/4722366482869645213696:ℚ)⟩ thresholdNode827 thresholdNode181
def thresholdNode829 : BoxExpr 1 := .mul ⟨(3684384335662458067291/590295810358705651712:ℚ),(29475074685299664538343/4722366482869645213696:ℚ)⟩ thresholdNode674 thresholdNode828
def thresholdNode830 : BoxExpr 1 := .neg ⟨(-29475074685299664538343/4722366482869645213696:ℚ),(-3684384335662458067291/590295810358705651712:ℚ)⟩ thresholdNode829
def thresholdNode831 : BoxExpr 1 := .add ⟨(244830262289844492365/2361183241434822606848:ℚ),(244830262289844492423/2361183241434822606848:ℚ)⟩ thresholdNode818 thresholdNode830
def thresholdNode832 : BoxExpr 1 := .mul ⟨(-11897089471215056712363/4722366482869645213696:ℚ),(-11897089471215056712315/4722366482869645213696:ℚ)⟩ thresholdNode719 thresholdNode683
def thresholdNode833 : BoxExpr 1 := .mul ⟨(-11897089471215056712363/4722366482869645213696:ℚ),(-11897089471215056712315/4722366482869645213696:ℚ)⟩ thresholdNode683 thresholdNode719
def thresholdNode834 : BoxExpr 1 := .add ⟨(-11897089471215056712363/2361183241434822606848:ℚ),(-11897089471215056712315/2361183241434822606848:ℚ)⟩ thresholdNode832 thresholdNode833
def thresholdNode835 : BoxExpr 1 := .mul ⟨(-6334969234247172181615/4722366482869645213696:ℚ),(-6334969234247172181599/4722366482869645213696:ℚ)⟩ thresholdNode702 thresholdNode828
def thresholdNode836 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode821
def thresholdNode837 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode838 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode671 thresholdNode49
def thresholdNode839 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode837 thresholdNode838
def thresholdNode840 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode839 thresholdNode49
def thresholdNode841 : BoxExpr 1 := .mul ⟨(1735654149895331711549/1180591620717411303424:ℚ),(3471308299790663423101/2361183241434822606848:ℚ)⟩ thresholdNode820 thresholdNode820
def thresholdNode842 : BoxExpr 1 := .inv ⟨(401519097278745474647/590295810358705651712:ℚ),(803038194557490949295/1180591620717411303424:ℚ)⟩ thresholdNode841
def thresholdNode843 : BoxExpr 1 := .mul ⟨(401519097278745474647/295147905179352825856:ℚ),(803038194557490949295/590295810358705651712:ℚ)⟩ thresholdNode840 thresholdNode842
def thresholdNode844 : BoxExpr 1 := .neg ⟨(-803038194557490949295/590295810358705651712:ℚ),(-401519097278745474647/295147905179352825856:ℚ)⟩ thresholdNode843
def thresholdNode845 : BoxExpr 1 := .mul ⟨(-956402642500716912445439/4722366482869645213696:ℚ),(-478201321250358456222123/2361183241434822606848:ℚ)⟩ thresholdNode171 thresholdNode844
def thresholdNode846 : BoxExpr 1 := .add ⟨(-956402642500716912445439/4722366482869645213696:ℚ),(-478201321250358456222123/2361183241434822606848:ℚ)⟩ thresholdNode836 thresholdNode845
def thresholdNode847 : BoxExpr 1 := .add ⟨(-956402642500716912445439/4722366482869645213696:ℚ),(-478201321250358456222123/2361183241434822606848:ℚ)⟩ thresholdNode846 thresholdNode49
def thresholdNode848 : BoxExpr 1 := .mul ⟨(52539690127433623300419/2361183241434822606848:ℚ),(26269845063716811650217/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode824
def thresholdNode849 : BoxExpr 1 := .inv ⟨(212227604925350319173/4722366482869645213696:ℚ),(106113802462675159587/2361183241434822606848:ℚ)⟩ thresholdNode848
def thresholdNode850 : BoxExpr 1 := .mul ⟨(-42981637045429214566853/4722366482869645213696:ℚ),(-10745409261357303641649/1180591620717411303424:ℚ)⟩ thresholdNode847 thresholdNode849
def thresholdNode851 : BoxExpr 1 := .add ⟨(-42981637045429214566853/4722366482869645213696:ℚ),(-10745409261357303641649/1180591620717411303424:ℚ)⟩ thresholdNode850 thresholdNode49
def thresholdNode852 : BoxExpr 1 := .mul ⟨(-21490818522714607283427/4722366482869645213696:ℚ),(-10745409261357303641649/2361183241434822606848:ℚ)⟩ thresholdNode851 thresholdNode826
def thresholdNode853 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode854 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode853
def thresholdNode855 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode854
def thresholdNode856 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode855
def thresholdNode857 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode825 thresholdNode856
def thresholdNode858 : BoxExpr 1 := .add ⟨(-21490818522714607283427/4722366482869645213696:ℚ),(-10745409261357303641649/2361183241434822606848:ℚ)⟩ thresholdNode852 thresholdNode857
def thresholdNode859 : BoxExpr 1 := .add ⟨(-21490818522714607283427/4722366482869645213696:ℚ),(-10745409261357303641649/2361183241434822606848:ℚ)⟩ thresholdNode858 thresholdNode49
def thresholdNode860 : BoxExpr 1 := .mul ⟨(-21248207329235524412143/4722366482869645213696:ℚ),(-10624103664617762206005/2361183241434822606848:ℚ)⟩ thresholdNode674 thresholdNode859
def thresholdNode861 : BoxExpr 1 := .add ⟨(-13791588281741348296879/2361183241434822606848:ℚ),(-27583176563482696593609/4722366482869645213696:ℚ)⟩ thresholdNode835 thresholdNode860
def thresholdNode862 : BoxExpr 1 := .neg ⟨(27583176563482696593609/4722366482869645213696:ℚ),(13791588281741348296879/2361183241434822606848:ℚ)⟩ thresholdNode861
def thresholdNode863 : BoxExpr 1 := .add ⟨(3788997621052583168883/4722366482869645213696:ℚ),(473624702631572896141/590295810358705651712:ℚ)⟩ thresholdNode834 thresholdNode862
def thresholdNode864 : BoxExpr 1 := .mul ⟨(-10675832597129497634137/2361183241434822606848:ℚ),(-20219249776308668047065/4722366482869645213696:ℚ)⟩ thresholdNode803 thresholdNode663
def thresholdNode865 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode748 thresholdNode655
def thresholdNode866 : BoxExpr 1 := .mul ⟨(-1672446494583453548829/4722366482869645213696:ℚ),(-954188821160639682169/4722366482869645213696:ℚ)⟩ thresholdNode650 thresholdNode756
def thresholdNode867 : BoxExpr 1 := .add ⟨(-1672446494583453548829/4722366482869645213696:ℚ),(-954188821160639682169/4722366482869645213696:ℚ)⟩ thresholdNode865 thresholdNode866
def thresholdNode868 : BoxExpr 1 := .mul ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode781 thresholdNode22
def thresholdNode869 : BoxExpr 1 := .add ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode868 thresholdNode784
def thresholdNode870 : BoxExpr 1 := .mul ⟨(7636952046515754369/147573952589676412928:ℚ),(488764930977008279619/4722366482869645213696:ℚ)⟩ thresholdNode796 thresholdNode25
def thresholdNode871 : BoxExpr 1 := .add ⟨(7636952046515754369/147573952589676412928:ℚ),(488764930977008279619/4722366482869645213696:ℚ)⟩ thresholdNode870 thresholdNode799
def thresholdNode872 : BoxExpr 1 := .add ⟨(-3533510720807212031149/4722366482869645213696:ℚ),(-3289128255318707891337/4722366482869645213696:ℚ)⟩ thresholdNode869 thresholdNode871
def thresholdNode873 : BoxExpr 1 := .add ⟨(-2602978607695332789989/2361183241434822606848:ℚ),(-2121658538239673786753/2361183241434822606848:ℚ)⟩ thresholdNode867 thresholdNode872
def thresholdNode874 : BoxExpr 1 := .mul ⟨(1906431857507983068899/2361183241434822606848:ℚ),(5739069728448741410963/4722366482869645213696:ℚ)⟩ thresholdNode873 thresholdNode873
def thresholdNode875 : BoxExpr 1 := .add ⟨(-4384700369810757282619/1180591620717411303424:ℚ),(-7240090023929963318051/2361183241434822606848:ℚ)⟩ thresholdNode864 thresholdNode874
def thresholdNode876 : BoxExpr 1 := .mul ⟨(-10675832597129497634137/2361183241434822606848:ℚ),(-20219249776308668047065/4722366482869645213696:ℚ)⟩ thresholdNode663 thresholdNode803
def thresholdNode877 : BoxExpr 1 := .add ⟨(-4384700369810757282619/1180591620717411303424:ℚ),(-7240090023929963318051/2361183241434822606848:ℚ)⟩ thresholdNode874 thresholdNode876
def thresholdNode878 : BoxExpr 1 := .add ⟨(-4384700369810757282619/590295810358705651712:ℚ),(-7240090023929963318051/1180591620717411303424:ℚ)⟩ thresholdNode875 thresholdNode877
def thresholdNode879 : BoxExpr 1 := .mul ⟨(-1903276540348361446377/147573952589676412928:ℚ),(-7303739239796809948011/590295810358705651712:ℚ)⟩ thresholdNode766 thresholdNode814
def thresholdNode880 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode807
def thresholdNode881 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode882 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode881 thresholdNode762
def thresholdNode883 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode882 thresholdNode49
def thresholdNode884 : BoxExpr 1 := .mul ⟨(3149877473655089228099/2361183241434822606848:ℚ),(7616704900220450765171/4722366482869645213696:ℚ)⟩ thresholdNode806 thresholdNode806
def thresholdNode885 : BoxExpr 1 := .inv ⟨(2927873075125330283151/4722366482869645213696:ℚ),(442492314880684883501/590295810358705651712:ℚ)⟩ thresholdNode884
def thresholdNode886 : BoxExpr 1 := .mul ⟨(2927873075125330283151/2361183241434822606848:ℚ),(442492314880684883501/295147905179352825856:ℚ)⟩ thresholdNode883 thresholdNode885
def thresholdNode887 : BoxExpr 1 := .neg ⟨(-442492314880684883501/295147905179352825856:ℚ),(-2927873075125330283151/2361183241434822606848:ℚ)⟩ thresholdNode886
def thresholdNode888 : BoxExpr 1 := .mul ⟨(-1053999229691306083703679/4722366482869645213696:ℚ),(-871759763400672452297893/4722366482869645213696:ℚ)⟩ thresholdNode171 thresholdNode887
def thresholdNode889 : BoxExpr 1 := .add ⟨(-1053999229691306083703679/4722366482869645213696:ℚ),(-871759763400672452297893/4722366482869645213696:ℚ)⟩ thresholdNode880 thresholdNode888
def thresholdNode890 : BoxExpr 1 := .add ⟨(-1053999229691306083703679/4722366482869645213696:ℚ),(-871759763400672452297893/4722366482869645213696:ℚ)⟩ thresholdNode889 thresholdNode49
def thresholdNode891 : BoxExpr 1 := .mul ⟨(51346364194070011763545/2361183241434822606848:ℚ),(53821299566843098463519/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode810
def thresholdNode892 : BoxExpr 1 := .inv ⟨(12948373470405941617/295147905179352825856:ℚ),(217159925036193066455/4722366482869645213696:ℚ)⟩ thresholdNode891
def thresholdNode893 : BoxExpr 1 := .mul ⟨(-48468579162217338169267/4722366482869645213696:ℚ),(-38244794541656379889113/4722366482869645213696:ℚ)⟩ thresholdNode890 thresholdNode892
def thresholdNode894 : BoxExpr 1 := .add ⟨(-48468579162217338169267/4722366482869645213696:ℚ),(-38244794541656379889113/4722366482869645213696:ℚ)⟩ thresholdNode893 thresholdNode49
def thresholdNode895 : BoxExpr 1 := .mul ⟨(-12117144790554334542317/2361183241434822606848:ℚ),(-4780599317707047486139/1180591620717411303424:ℚ)⟩ thresholdNode894 thresholdNode812
def thresholdNode896 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode897 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode896
def thresholdNode898 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode897
def thresholdNode899 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode898
def thresholdNode900 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode811 thresholdNode899
def thresholdNode901 : BoxExpr 1 := .add ⟨(-12117144790554334542317/2361183241434822606848:ℚ),(-4780599317707047486139/1180591620717411303424:ℚ)⟩ thresholdNode895 thresholdNode900
def thresholdNode902 : BoxExpr 1 := .add ⟨(-12117144790554334542317/2361183241434822606848:ℚ),(-4780599317707047486139/1180591620717411303424:ℚ)⟩ thresholdNode901 thresholdNode49
def thresholdNode903 : BoxExpr 1 := .mul ⟨(1481985788489184720701/2361183241434822606848:ℚ),(1635814546724835163213/1180591620717411303424:ℚ)⟩ thresholdNode753 thresholdNode902
def thresholdNode904 : BoxExpr 1 := .add ⟨(-28970438857084598421331/2361183241434822606848:ℚ),(-12971663932868784732809/1180591620717411303424:ℚ)⟩ thresholdNode879 thresholdNode903
def thresholdNode905 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode887
def thresholdNode906 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode880 thresholdNode905
def thresholdNode907 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode5
def thresholdNode908 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode12 thresholdNode49
def thresholdNode909 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode907 thresholdNode908
def thresholdNode910 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode908 thresholdNode762
def thresholdNode911 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode909 thresholdNode910
def thresholdNode912 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode911 thresholdNode49
def thresholdNode913 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode912 thresholdNode885
def thresholdNode914 : BoxExpr 1 := .mul ⟨(2727166643857220110909/1180591620717411303424:ℚ),(2998702716622224710697/1180591620717411303424:ℚ)⟩ thresholdNode883 thresholdNode806
def thresholdNode915 : BoxExpr 1 := .mul ⟨(2727166643857220110909/1180591620717411303424:ℚ),(2998702716622224710697/1180591620717411303424:ℚ)⟩ thresholdNode806 thresholdNode883
def thresholdNode916 : BoxExpr 1 := .add ⟨(2727166643857220110909/590295810358705651712:ℚ),(2998702716622224710697/590295810358705651712:ℚ)⟩ thresholdNode914 thresholdNode915
def thresholdNode917 : BoxExpr 1 := .mul ⟨(8404030593585460815025/4722366482869645213696:ℚ),(6142491666782782519573/2361183241434822606848:ℚ)⟩ thresholdNode884 thresholdNode884
def thresholdNode918 : BoxExpr 1 := .inv ⟨(226910617143447383839/590295810358705651712:ℚ),(2653577346035853202159/4722366482869645213696:ℚ)⟩ thresholdNode917
def thresholdNode919 : BoxExpr 1 := .mul ⟨(131040881400340864167/73786976294838206464:ℚ),(1685021614732766783371/590295810358705651712:ℚ)⟩ thresholdNode916 thresholdNode918
def thresholdNode920 : BoxExpr 1 := .neg ⟨(-1685021614732766783371/590295810358705651712:ℚ),(-131040881400340864167/73786976294838206464:ℚ)⟩ thresholdNode919
def thresholdNode921 : BoxExpr 1 := .mul ⟨(-1685021614732766783371/295147905179352825856:ℚ),(-131040881400340864167/36893488147419103232:ℚ)⟩ thresholdNode883 thresholdNode920
def thresholdNode922 : BoxExpr 1 := .add ⟨(-1685021614732766783371/295147905179352825856:ℚ),(-131040881400340864167/36893488147419103232:ℚ)⟩ thresholdNode913 thresholdNode921
def thresholdNode923 : BoxExpr 1 := .neg ⟨(131040881400340864167/36893488147419103232:ℚ),(1685021614732766783371/295147905179352825856:ℚ)⟩ thresholdNode922
def thresholdNode924 : BoxExpr 1 := .mul ⟨(1248536830216103518388029/2361183241434822606848:ℚ),(2006827490801085026599227/2361183241434822606848:ℚ)⟩ thresholdNode171 thresholdNode923
def thresholdNode925 : BoxExpr 1 := .add ⟨(1248536830216103518388029/2361183241434822606848:ℚ),(2006827490801085026599227/2361183241434822606848:ℚ)⟩ thresholdNode905 thresholdNode924
def thresholdNode926 : BoxExpr 1 := .add ⟨(1248536830216103518388029/2361183241434822606848:ℚ),(2006827490801085026599227/2361183241434822606848:ℚ)⟩ thresholdNode906 thresholdNode925
def thresholdNode927 : BoxExpr 1 := .add ⟨(1248536830216103518388029/2361183241434822606848:ℚ),(2006827490801085026599227/2361183241434822606848:ℚ)⟩ thresholdNode926 thresholdNode49
def thresholdNode928 : BoxExpr 1 := .mul ⟨(109548608582337699229771/4722366482869645213696:ℚ),(184569541158572049174513/4722366482869645213696:ℚ)⟩ thresholdNode927 thresholdNode892
def thresholdNode929 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode810
def thresholdNode930 : BoxExpr 1 := .mul ⟨(-48468579162217338169267/2361183241434822606848:ℚ),(-38244794541656379889113/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode893
def thresholdNode931 : BoxExpr 1 := .add ⟨(-48468579162217338169267/2361183241434822606848:ℚ),(-38244794541656379889113/2361183241434822606848:ℚ)⟩ thresholdNode929 thresholdNode930
def thresholdNode932 : BoxExpr 1 := .mul ⟨(558289816242296652423039/1180591620717411303424:ℚ),(613406921629598908552247/1180591620717411303424:ℚ)⟩ thresholdNode891 thresholdNode891
def thresholdNode933 : BoxExpr 1 := .inv ⟨(9088887169419958897/4722366482869645213696:ℚ),(1248273328975840613/590295810358705651712:ℚ)⟩ thresholdNode932
def thresholdNode934 : BoxExpr 1 := .mul ⟨(-102494433468509227641/2361183241434822606848:ℚ),(-73607718432631071873/2361183241434822606848:ℚ)⟩ thresholdNode931 thresholdNode933
def thresholdNode935 : BoxExpr 1 := .neg ⟨(73607718432631071873/2361183241434822606848:ℚ),(102494433468509227641/2361183241434822606848:ℚ)⟩ thresholdNode934
def thresholdNode936 : BoxExpr 1 := .mul ⟨(-22876041983469572384685/2361183241434822606848:ℚ),(-3397038721902656954459/590295810358705651712:ℚ)⟩ thresholdNode890 thresholdNode935
def thresholdNode937 : BoxExpr 1 := .add ⟨(63796524615398554460401/4722366482869645213696:ℚ),(157393231383350793538841/4722366482869645213696:ℚ)⟩ thresholdNode928 thresholdNode936
def thresholdNode938 : BoxExpr 1 := .add ⟨(63796524615398554460401/4722366482869645213696:ℚ),(157393231383350793538841/4722366482869645213696:ℚ)⟩ thresholdNode937 thresholdNode49
def thresholdNode939 : BoxExpr 1 := .mul ⟨(3987282788462409653775/590295810358705651712:ℚ),(78696615691675396769421/4722366482869645213696:ℚ)⟩ thresholdNode938 thresholdNode812
def thresholdNode940 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode894 thresholdNode899
def thresholdNode941 : BoxExpr 1 := .add ⟨(3987282788462409653775/590295810358705651712:ℚ),(78696615691675396769421/4722366482869645213696:ℚ)⟩ thresholdNode939 thresholdNode940
def thresholdNode942 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode5 thresholdNode49
def thresholdNode943 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode907 thresholdNode942
def thresholdNode944 : BoxExpr 1 := .mul ⟨(16/1:ℚ),(16/1:ℚ)⟩ thresholdNode896 thresholdNode896
def thresholdNode945 : BoxExpr 1 := .inv ⟨(1/16:ℚ),(1/16:ℚ)⟩ thresholdNode944
def thresholdNode946 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode943 thresholdNode945
def thresholdNode947 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode946
def thresholdNode948 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode947
def thresholdNode949 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode898 thresholdNode948
def thresholdNode950 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode949
def thresholdNode951 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode811 thresholdNode950
def thresholdNode952 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode940 thresholdNode951
def thresholdNode953 : BoxExpr 1 := .add ⟨(3987282788462409653775/590295810358705651712:ℚ),(78696615691675396769421/4722366482869645213696:ℚ)⟩ thresholdNode941 thresholdNode952
def thresholdNode954 : BoxExpr 1 := .add ⟨(3987282788462409653775/590295810358705651712:ℚ),(78696615691675396769421/4722366482869645213696:ℚ)⟩ thresholdNode953 thresholdNode49
def thresholdNode955 : BoxExpr 1 := .mul ⟨(7829229119285364475669/1180591620717411303424:ℚ),(19555986035919317854397/1180591620717411303424:ℚ)⟩ thresholdNode654 thresholdNode954
def thresholdNode956 : BoxExpr 1 := .add ⟨(17140444027059913672039/2361183241434822606848:ℚ),(10595900291322076508805/590295810358705651712:ℚ)⟩ thresholdNode903 thresholdNode955
def thresholdNode957 : BoxExpr 1 := .add ⟨(-2957498707506171187323/590295810358705651712:ℚ),(8220136649775368284801/1180591620717411303424:ℚ)⟩ thresholdNode904 thresholdNode956
def thresholdNode958 : BoxExpr 1 := .neg ⟨(-8220136649775368284801/1180591620717411303424:ℚ),(2957498707506171187323/590295810358705651712:ℚ)⟩ thresholdNode957
def thresholdNode959 : BoxExpr 1 := .add ⟨(-16989537389396882850039/1180591620717411303424:ℚ),(-1325092608917620943405/1180591620717411303424:ℚ)⟩ thresholdNode878 thresholdNode958
def thresholdCell2Out1 : TaylorCertificate1 :=
  { center := (17/160:ℚ), radius := (23/800:ℚ)
    whole := thresholdNode817, centerValue := thresholdNode831, gradient := thresholdNode863, hessian := thresholdNode959 }
theorem thresholdCell2Out1_check : thresholdCell2Out1.check = true := by decide +kernel
theorem thresholdCell2Out1_lower_pos : 0 < thresholdCell2Out1.lower := by decide +kernel
theorem thresholdCell2Out1_positive (x : ℝ) (hx : (31/400:ℝ) ≤ x ∧ x ≤ (27/200:ℝ)) :
    0 < thresholdNode817.eval (fun _ => x) := by
  apply thresholdCell2Out1.positive_sound thresholdCell2Out1_check thresholdCell2Out1_lower_pos x
  norm_num [thresholdCell2Out1]
  exact hx
theorem thresholdCell2_public (x : ℝ)
    (hx : (31/400:ℝ) ≤ x ∧ x ≤ (27/200:ℝ)) : qc x < fA (43/20) x := by
  have hf := thresholdCell2Out0_positive x hx
  have hg := thresholdCell2Out1_positive x hx
  have hfa : thresholdNode663.eval (fun _ => x) = thresholdFA 2 x := by
    norm_num [thresholdNode0, thresholdNode1, thresholdNode644, thresholdNode3, thresholdNode645, thresholdNode5, thresholdNode646, thresholdNode647, thresholdNode648, thresholdNode9, thresholdNode649, thresholdNode650, thresholdNode12, thresholdNode651, thresholdNode652, thresholdNode653, thresholdNode654, thresholdNode655, thresholdNode656, thresholdNode19, thresholdNode657, thresholdNode658, thresholdNode22, thresholdNode659, thresholdNode660, thresholdNode25, thresholdNode661, thresholdNode662, thresholdNode663, BoxExpr.eval, thresholdFA, ftilde, pow_two, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  have hgap : thresholdNode817.eval (fun _ => x) =
      (thresholdNode663.eval (fun _ => x))^2 - (1-x^2)*(thresholdCapacity 3 x+1/4) := by
    norm_num [thresholdNode804, thresholdNode12, thresholdNode651, thresholdNode652, thresholdNode653, thresholdNode654, thresholdNode171, thresholdNode5, thresholdNode805, thresholdNode806, thresholdNode807, thresholdNode808, thresholdNode809, thresholdNode810, thresholdNode811, thresholdNode812, thresholdNode813, thresholdNode181, thresholdNode814, thresholdNode815, thresholdNode816, thresholdNode817, BoxExpr.eval, thresholdCapacity, Da, D5, beta5, eta5, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  rw [hfa] at hf
  rw [hgap, hfa] at hg
  refine threshold_positive_to_public 2 3 x ?_ ?_ ?_ hf hg
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdFADomain] <;> constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdCapacityDomain] <;> constructor <;> linarith [hx.1,hx.2]
def thresholdNode960 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode961 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode960 thresholdNode3
def thresholdNode962 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode963 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode962
def thresholdNode964 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode963 thresholdNode963
def thresholdNode965 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode964 thresholdNode9
def thresholdNode966 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode961 thresholdNode965
def thresholdNode967 : BoxExpr 1 := .var 0
def thresholdNode968 : BoxExpr 1 := .mul ⟨(86065129150299284019/4722366482869645213696:ℚ),(1/16:ℚ)⟩ thresholdNode967 thresholdNode967
def thresholdNode969 : BoxExpr 1 := .neg ⟨(-1/16:ℚ),(-86065129150299284019/4722366482869645213696:ℚ)⟩ thresholdNode968
def thresholdNode970 : BoxExpr 1 := .add ⟨(15/16:ℚ),(4636301353719345929677/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode969
def thresholdNode971 : BoxExpr 1 := .sqrt ⟨(4572411685710557187031/4722366482869645213696:ℚ),(4679136043896074041011/4722366482869645213696:ℚ)⟩ thresholdNode970
def thresholdNode972 : BoxExpr 1 := .mul ⟨(1485662289406467103013/590295810358705651712:ℚ),(12162712275701260058507/4722366482869645213696:ℚ)⟩ thresholdNode966 thresholdNode971
def thresholdNode973 : BoxExpr 1 := .neg ⟨(-47223664828696452137/2361183241434822606848:ℚ),(-94447329657392904273/4722366482869645213696:ℚ)⟩ thresholdNode19
def thresholdNode974 : BoxExpr 1 := .add ⟨(271536072765004599787/2361183241434822606848:ℚ),(1086144291060018399151/4722366482869645213696:ℚ)⟩ thresholdNode967 thresholdNode973
def thresholdNode975 : BoxExpr 1 := .mul ⟨(-868915432848014719321/4722366482869645213696:ℚ),(-434457716424007359659/4722366482869645213696:ℚ)⟩ thresholdNode974 thresholdNode22
def thresholdNode976 : BoxExpr 1 := .mul ⟨(31226648367975528975/2361183241434822606848:ℚ),(249813186943804231805/4722366482869645213696:ℚ)⟩ thresholdNode974 thresholdNode974
def thresholdNode977 : BoxExpr 1 := .mul ⟨(28103983531177976077/4722366482869645213696:ℚ),(112415934124711904313/4722366482869645213696:ℚ)⟩ thresholdNode976 thresholdNode25
def thresholdNode978 : BoxExpr 1 := .add ⟨(-210202862329209185811/1180591620717411303424:ℚ),(-161020891149647727673/2361183241434822606848:ℚ)⟩ thresholdNode975 thresholdNode977
def thresholdNode979 : BoxExpr 1 := .add ⟨(2761121716483725020215/1180591620717411303424:ℚ),(11840670493401964603161/4722366482869645213696:ℚ)⟩ thresholdNode972 thresholdNode978
def thresholdNode980 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode981 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode980 thresholdNode3
def thresholdNode982 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode983 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode982
def thresholdNode984 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode983 thresholdNode983
def thresholdNode985 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode984 thresholdNode9
def thresholdNode986 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode981 thresholdNode985
def thresholdNode987 : BoxExpr 1 := .var 0
def thresholdNode988 : BoxExpr 1 := .mul ⟨(174993192980838290449/4722366482869645213696:ℚ),(174993192980838290451/4722366482869645213696:ℚ)⟩ thresholdNode987 thresholdNode987
def thresholdNode989 : BoxExpr 1 := .neg ⟨(-174993192980838290451/4722366482869645213696:ℚ),(-174993192980838290449/4722366482869645213696:ℚ)⟩ thresholdNode988
def thresholdNode990 : BoxExpr 1 := .add ⟨(4547373289888806923245/4722366482869645213696:ℚ),(4547373289888806923247/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode989
def thresholdNode991 : BoxExpr 1 := .sqrt ⟨(1158510984228990077515/1180591620717411303424:ℚ),(2317021968457980155031/2361183241434822606848:ℚ)⟩ thresholdNode990
def thresholdNode992 : BoxExpr 1 := .mul ⟨(12045502107422501431949/4722366482869645213696:ℚ),(3011375526855625357991/1180591620717411303424:ℚ)⟩ thresholdNode986 thresholdNode991
def thresholdNode993 : BoxExpr 1 := .neg ⟨(-47223664828696452137/2361183241434822606848:ℚ),(-94447329657392904273/4722366482869645213696:ℚ)⟩ thresholdNode19
def thresholdNode994 : BoxExpr 1 := .add ⟨(407304109147506899681/2361183241434822606848:ℚ),(203652054573753449841/1180591620717411303424:ℚ)⟩ thresholdNode987 thresholdNode993
def thresholdNode995 : BoxExpr 1 := .mul ⟨(-162921643659002759873/1180591620717411303424:ℚ),(-651686574636011039489/4722366482869645213696:ℚ)⟩ thresholdNode994 thresholdNode22
def thresholdNode996 : BoxExpr 1 := .mul ⟨(140519917655889880389/4722366482869645213696:ℚ),(140519917655889880391/4722366482869645213696:ℚ)⟩ thresholdNode994 thresholdNode994
def thresholdNode997 : BoxExpr 1 := .mul ⟨(63233962945150446175/4722366482869645213696:ℚ),(1976061342035951443/147573952589676412928:ℚ)⟩ thresholdNode996 thresholdNode25
def thresholdNode998 : BoxExpr 1 := .add ⟨(-588452611690860593317/4722366482869645213696:ℚ),(-588452611690860593313/4722366482869645213696:ℚ)⟩ thresholdNode995 thresholdNode997
def thresholdNode999 : BoxExpr 1 := .add ⟨(1432131186966455104829/590295810358705651712:ℚ),(11457049495731640838651/4722366482869645213696:ℚ)⟩ thresholdNode992 thresholdNode998
def thresholdNode1000 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode1
def thresholdNode1001 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode49
def thresholdNode1002 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1000 thresholdNode1001
def thresholdNode1003 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1002 thresholdNode49
def thresholdNode1004 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49
def thresholdNode1005 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode1004
def thresholdNode1006 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1005 thresholdNode983
def thresholdNode1007 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode983 thresholdNode1005
def thresholdNode1008 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1006 thresholdNode1007
def thresholdNode1009 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1008 thresholdNode9
def thresholdNode1010 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode984 thresholdNode49
def thresholdNode1011 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1009 thresholdNode1010
def thresholdNode1012 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1003 thresholdNode1011
def thresholdNode1013 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1012 thresholdNode991
def thresholdNode1014 : BoxExpr 1 := .mul ⟨(227263886988101675909/1180591620717411303424:ℚ),(909055547952406703637/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode987
def thresholdNode1015 : BoxExpr 1 := .mul ⟨(227263886988101675909/1180591620717411303424:ℚ),(909055547952406703637/4722366482869645213696:ℚ)⟩ thresholdNode987 thresholdNode12
def thresholdNode1016 : BoxExpr 1 := .add ⟨(227263886988101675909/590295810358705651712:ℚ),(909055547952406703637/2361183241434822606848:ℚ)⟩ thresholdNode1014 thresholdNode1015
def thresholdNode1017 : BoxExpr 1 := .neg ⟨(-909055547952406703637/2361183241434822606848:ℚ),(-227263886988101675909/590295810358705651712:ℚ)⟩ thresholdNode1016
def thresholdNode1018 : BoxExpr 1 := .add ⟨(-909055547952406703637/2361183241434822606848:ℚ),(-227263886988101675909/590295810358705651712:ℚ)⟩ thresholdNode49 thresholdNode1017
def thresholdNode1019 : BoxExpr 1 := .mul ⟨(1158510984228990077515/590295810358705651712:ℚ),(2317021968457980155031/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode991
def thresholdNode1020 : BoxExpr 1 := .inv ⟨(2406186206056148300489/4722366482869645213696:ℚ),(2406186206056148300491/4722366482869645213696:ℚ)⟩ thresholdNode1019
def thresholdNode1021 : BoxExpr 1 := .mul ⟨(-463190844665808547845/2361183241434822606848:ℚ),(-926381689331617095687/4722366482869645213696:ℚ)⟩ thresholdNode1018 thresholdNode1020
def thresholdNode1022 : BoxExpr 1 := .mul ⟨(-2407990244164138897683/4722366482869645213696:ℚ),(-2407990244164138897673/4722366482869645213696:ℚ)⟩ thresholdNode986 thresholdNode1021
def thresholdNode1023 : BoxExpr 1 := .add ⟨(-2407990244164138897683/4722366482869645213696:ℚ),(-2407990244164138897673/4722366482869645213696:ℚ)⟩ thresholdNode1013 thresholdNode1022
def thresholdNode1024 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode1004
def thresholdNode1025 : BoxExpr 1 := .mul ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode1024 thresholdNode22
def thresholdNode1026 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode994 thresholdNode49
def thresholdNode1027 : BoxExpr 1 := .add ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode1025 thresholdNode1026
def thresholdNode1028 : BoxExpr 1 := .mul ⟨(407304109147506899681/2361183241434822606848:ℚ),(203652054573753449841/1180591620717411303424:ℚ)⟩ thresholdNode1024 thresholdNode994
def thresholdNode1029 : BoxExpr 1 := .mul ⟨(407304109147506899681/2361183241434822606848:ℚ),(203652054573753449841/1180591620717411303424:ℚ)⟩ thresholdNode994 thresholdNode1024
def thresholdNode1030 : BoxExpr 1 := .add ⟨(407304109147506899681/1180591620717411303424:ℚ),(203652054573753449841/590295810358705651712:ℚ)⟩ thresholdNode1028 thresholdNode1029
def thresholdNode1031 : BoxExpr 1 := .mul ⟨(733147396465512419425/4722366482869645213696:ℚ),(183286849116378104857/1180591620717411303424:ℚ)⟩ thresholdNode1030 thresholdNode25
def thresholdNode1032 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode996 thresholdNode49
def thresholdNode1033 : BoxExpr 1 := .add ⟨(733147396465512419425/4722366482869645213696:ℚ),(183286849116378104857/1180591620717411303424:ℚ)⟩ thresholdNode1031 thresholdNode1032
def thresholdNode1034 : BoxExpr 1 := .add ⟨(-761186447457550937883/1180591620717411303424:ℚ),(-380593223728775468941/590295810358705651712:ℚ)⟩ thresholdNode1027 thresholdNode1033
def thresholdNode1035 : BoxExpr 1 := .add ⟨(-5452736033994342649215/4722366482869645213696:ℚ),(-5452736033994342649201/4722366482869645213696:ℚ)⟩ thresholdNode1023 thresholdNode1034
def thresholdNode1036 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode1
def thresholdNode1037 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode49
def thresholdNode1038 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1036 thresholdNode1037
def thresholdNode1039 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode49
def thresholdNode1040 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1037 thresholdNode1039
def thresholdNode1041 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1038 thresholdNode1040
def thresholdNode1042 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1041 thresholdNode49
def thresholdNode1043 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49
def thresholdNode1044 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode1043
def thresholdNode1045 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1044 thresholdNode963
def thresholdNode1046 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1044 thresholdNode1044
def thresholdNode1047 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1045 thresholdNode1046
def thresholdNode1048 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode963 thresholdNode1044
def thresholdNode1049 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1046 thresholdNode1048
def thresholdNode1050 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1047 thresholdNode1049
def thresholdNode1051 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1050 thresholdNode9
def thresholdNode1052 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1045 thresholdNode1048
def thresholdNode1053 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1052 thresholdNode49
def thresholdNode1054 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1051 thresholdNode1053
def thresholdNode1055 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode964 thresholdNode49
def thresholdNode1056 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1053 thresholdNode1055
def thresholdNode1057 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1054 thresholdNode1056
def thresholdNode1058 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1042 thresholdNode1057
def thresholdNode1059 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1058 thresholdNode971
def thresholdNode1060 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1036 thresholdNode1039
def thresholdNode1061 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1060 thresholdNode49
def thresholdNode1062 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1052 thresholdNode9
def thresholdNode1063 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1062 thresholdNode1055
def thresholdNode1064 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1061 thresholdNode1063
def thresholdNode1065 : BoxExpr 1 := .mul ⟨(79689934398425262981/590295810358705651712:ℚ),(1/4:ℚ)⟩ thresholdNode12 thresholdNode967
def thresholdNode1066 : BoxExpr 1 := .mul ⟨(79689934398425262981/590295810358705651712:ℚ),(1/4:ℚ)⟩ thresholdNode967 thresholdNode12
def thresholdNode1067 : BoxExpr 1 := .add ⟨(79689934398425262981/295147905179352825856:ℚ),(1/2:ℚ)⟩ thresholdNode1065 thresholdNode1066
def thresholdNode1068 : BoxExpr 1 := .neg ⟨(-1/2:ℚ),(-79689934398425262981/295147905179352825856:ℚ)⟩ thresholdNode1067
def thresholdNode1069 : BoxExpr 1 := .add ⟨(-1/2:ℚ),(-79689934398425262981/295147905179352825856:ℚ)⟩ thresholdNode49 thresholdNode1068
def thresholdNode1070 : BoxExpr 1 := .mul ⟨(4572411685710557187031/2361183241434822606848:ℚ),(4679136043896074041011/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode971
def thresholdNode1071 : BoxExpr 1 := .inv ⟨(2382998163477412870061/4722366482869645213696:ℚ),(2438619565712297166417/4722366482869645213696:ℚ)⟩ thresholdNode1070
def thresholdNode1072 : BoxExpr 1 := .mul ⟨(-1219309782856148583209/4722366482869645213696:ℚ),(-643409504138901474915/4722366482869645213696:ℚ)⟩ thresholdNode1069 thresholdNode1071
def thresholdNode1073 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1064 thresholdNode1072
def thresholdNode1074 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1059 thresholdNode1073
def thresholdNode1075 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode967
def thresholdNode1076 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode12
def thresholdNode1077 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1075 thresholdNode1076
def thresholdNode1078 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode967 thresholdNode49
def thresholdNode1079 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1076 thresholdNode1078
def thresholdNode1080 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode1077 thresholdNode1079
def thresholdNode1081 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode1080
def thresholdNode1082 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode49 thresholdNode1081
def thresholdNode1083 : BoxExpr 1 := .mul ⟨(-2438619565712297166417/2361183241434822606848:ℚ),(-2382998163477412870061/2361183241434822606848:ℚ)⟩ thresholdNode1082 thresholdNode1071
def thresholdNode1084 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode971
def thresholdNode1085 : BoxExpr 1 := .mul ⟨(-1219309782856148583209/2361183241434822606848:ℚ),(-643409504138901474915/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode1072
def thresholdNode1086 : BoxExpr 1 := .add ⟨(-1219309782856148583209/2361183241434822606848:ℚ),(-643409504138901474915/2361183241434822606848:ℚ)⟩ thresholdNode1084 thresholdNode1085
def thresholdNode1087 : BoxExpr 1 := .mul ⟨(8854437155380584775679/2361183241434822606848:ℚ),(9272602707438691859355/2361183241434822606848:ℚ)⟩ thresholdNode1070 thresholdNode1070
def thresholdNode1088 : BoxExpr 1 := .inv ⟨(601253658280874591135/2361183241434822606848:ℚ),(1259297728765238723653/4722366482869645213696:ℚ)⟩ thresholdNode1087
def thresholdNode1089 : BoxExpr 1 := .mul ⟨(-40643659428538286107/295147905179352825856:ℚ),(-163838329591531021597/2361183241434822606848:ℚ)⟩ thresholdNode1086 thresholdNode1088
def thresholdNode1090 : BoxExpr 1 := .neg ⟨(163838329591531021597/2361183241434822606848:ℚ),(40643659428538286107/295147905179352825856:ℚ)⟩ thresholdNode1089
def thresholdNode1091 : BoxExpr 1 := .mul ⟨(-40643659428538286107/590295810358705651712:ℚ),(-44236348989713375831/2361183241434822606848:ℚ)⟩ thresholdNode1069 thresholdNode1090
def thresholdNode1092 : BoxExpr 1 := .add ⟨(-2601194203426450310845/2361183241434822606848:ℚ),(-606808628116781561473/590295810358705651712:ℚ)⟩ thresholdNode1083 thresholdNode1091
def thresholdNode1093 : BoxExpr 1 := .mul ⟨(-13522828305353087230995/4722366482869645213696:ℚ),(-12618464059962849214513/4722366482869645213696:ℚ)⟩ thresholdNode966 thresholdNode1092
def thresholdNode1094 : BoxExpr 1 := .add ⟨(-13522828305353087230995/4722366482869645213696:ℚ),(-12618464059962849214513/4722366482869645213696:ℚ)⟩ thresholdNode1073 thresholdNode1093
def thresholdNode1095 : BoxExpr 1 := .add ⟨(-13522828305353087230995/4722366482869645213696:ℚ),(-12618464059962849214513/4722366482869645213696:ℚ)⟩ thresholdNode1074 thresholdNode1094
def thresholdNode1096 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1044 thresholdNode22
def thresholdNode1097 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode1043
def thresholdNode1098 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1097 thresholdNode49
def thresholdNode1099 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1096 thresholdNode1098
def thresholdNode1100 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode974 thresholdNode49
def thresholdNode1101 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1098 thresholdNode1100
def thresholdNode1102 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1099 thresholdNode1101
def thresholdNode1103 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1044 thresholdNode974
def thresholdNode1104 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1097 thresholdNode1097
def thresholdNode1105 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1103 thresholdNode1104
def thresholdNode1106 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode974 thresholdNode1044
def thresholdNode1107 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1104 thresholdNode1106
def thresholdNode1108 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode1105 thresholdNode1107
def thresholdNode1109 : BoxExpr 1 := .mul ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode1108 thresholdNode25
def thresholdNode1110 : BoxExpr 1 := .mul ⟨(271536072765004599787/2361183241434822606848:ℚ),(1086144291060018399151/4722366482869645213696:ℚ)⟩ thresholdNode1097 thresholdNode974
def thresholdNode1111 : BoxExpr 1 := .mul ⟨(271536072765004599787/2361183241434822606848:ℚ),(1086144291060018399151/4722366482869645213696:ℚ)⟩ thresholdNode974 thresholdNode1097
def thresholdNode1112 : BoxExpr 1 := .add ⟨(271536072765004599787/1180591620717411303424:ℚ),(1086144291060018399151/2361183241434822606848:ℚ)⟩ thresholdNode1110 thresholdNode1111
def thresholdNode1113 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1112 thresholdNode49
def thresholdNode1114 : BoxExpr 1 := .add ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode1109 thresholdNode1113
def thresholdNode1115 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode976 thresholdNode49
def thresholdNode1116 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1113 thresholdNode1115
def thresholdNode1117 : BoxExpr 1 := .add ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode1114 thresholdNode1116
def thresholdNode1118 : BoxExpr 1 := .add ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode1102 thresholdNode1117
def thresholdNode1119 : BoxExpr 1 := .add ⟨(-9272698470770406538669/4722366482869645213696:ℚ),(-8368334225380168522185/4722366482869645213696:ℚ)⟩ thresholdNode1095 thresholdNode1118
def thresholdCell3Out0 : TaylorCertificate1 :=
  { center := (77/400:ℚ), radius := (23/400:ℚ)
    whole := thresholdNode979, centerValue := thresholdNode999, gradient := thresholdNode1035, hessian := thresholdNode1119 }
theorem thresholdCell3Out0_check : thresholdCell3Out0.check = true := by decide +kernel
theorem thresholdCell3Out0_lower_pos : 0 < thresholdCell3Out0.lower := by decide +kernel
theorem thresholdCell3Out0_positive (x : ℝ) (hx : (27/200:ℝ) ≤ x ∧ x ≤ (1/4:ℝ)) :
    0 < thresholdNode979.eval (fun _ => x) := by
  apply thresholdCell3Out0.positive_sound thresholdCell3Out0_check thresholdCell3Out0_lower_pos x
  norm_num [thresholdCell3Out0]
  exact hx
def thresholdNode1120 : BoxExpr 1 := .mul ⟨(25830415867614828210005/4722366482869645213696:ℚ),(14844408861732767318017/2361183241434822606848:ℚ)⟩ thresholdNode979 thresholdNode979
def thresholdNode1121 : BoxExpr 1 := .mul ⟨(79689934398425262981/295147905179352825856:ℚ),(1/2:ℚ)⟩ thresholdNode967 thresholdNode5
def thresholdNode1122 : BoxExpr 1 := .add ⟨(374837839577778088837/295147905179352825856:ℚ),(3/2:ℚ)⟩ thresholdNode1121 thresholdNode12
def thresholdNode1123 : BoxExpr 1 := .inv ⟨(1574122160956548404565/2361183241434822606848:ℚ),(3718398805409169459605/4722366482869645213696:ℚ)⟩ thresholdNode1122
def thresholdNode1124 : BoxExpr 1 := .mul ⟨(234343553731490766385249/2361183241434822606848:ℚ),(138391862439856751802411/1180591620717411303424:ℚ)⟩ thresholdNode171 thresholdNode1123
def thresholdNode1125 : BoxExpr 1 := .add ⟨(236704736972925588992097/2361183241434822606848:ℚ),(139572454060574163105835/1180591620717411303424:ℚ)⟩ thresholdNode1124 thresholdNode12
def thresholdNode1126 : BoxExpr 1 := .sqrt ⟨(47282269747071556685363/4722366482869645213696:ℚ),(51346364194070011763559/4722366482869645213696:ℚ)⟩ thresholdNode1125
def thresholdNode1127 : BoxExpr 1 := .add ⟨(52004636229941201899059/4722366482869645213696:ℚ),(56068730676939656977255/4722366482869645213696:ℚ)⟩ thresholdNode1126 thresholdNode12
def thresholdNode1128 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode1129 : BoxExpr 1 := .mul ⟨(26002318114970600949529/4722366482869645213696:ℚ),(7008591334617457122157/1180591620717411303424:ℚ)⟩ thresholdNode1127 thresholdNode1128
def thresholdNode1130 : BoxExpr 1 := .add ⟨(27182909735688012252953/4722366482869645213696:ℚ),(7303739239796809948013/1180591620717411303424:ℚ)⟩ thresholdNode1129 thresholdNode181
def thresholdNode1131 : BoxExpr 1 := .mul ⟨(25483977877207511487143/4722366482869645213696:ℚ),(14341257184303026173423/2361183241434822606848:ℚ)⟩ thresholdNode970 thresholdNode1130
def thresholdNode1132 : BoxExpr 1 := .neg ⟨(-14341257184303026173423/2361183241434822606848:ℚ),(-25483977877207511487143/4722366482869645213696:ℚ)⟩ thresholdNode1131
def thresholdNode1133 : BoxExpr 1 := .add ⟨(-2852098500991224136841/4722366482869645213696:ℚ),(4204839846258023148891/4722366482869645213696:ℚ)⟩ thresholdNode1120 thresholdNode1132
def thresholdNode1134 : BoxExpr 1 := .mul ⟨(6949057407118015982261/1180591620717411303424:ℚ),(27796229628472063929137/4722366482869645213696:ℚ)⟩ thresholdNode999 thresholdNode999
def thresholdNode1135 : BoxExpr 1 := .mul ⟨(227263886988101675909/590295810358705651712:ℚ),(909055547952406703637/2361183241434822606848:ℚ)⟩ thresholdNode987 thresholdNode5
def thresholdNode1136 : BoxExpr 1 := .add ⟨(817559697346807327621/590295810358705651712:ℚ),(3270238789387229310485/2361183241434822606848:ℚ)⟩ thresholdNode1135 thresholdNode12
def thresholdNode1137 : BoxExpr 1 := .inv ⟨(1704825445079294300973/2361183241434822606848:ℚ),(852412722539647150487/1180591620717411303424:ℚ)⟩ thresholdNode1136
def thresholdNode1138 : BoxExpr 1 := .mul ⟨(126900841370843375298877/1180591620717411303424:ℚ),(15862605171355421912369/147573952589676412928:ℚ)⟩ thresholdNode171 thresholdNode1137
def thresholdNode1139 : BoxExpr 1 := .add ⟨(128081432991560786602301/1180591620717411303424:ℚ),(16010179123945098325297/147573952589676412928:ℚ)⟩ thresholdNode1138 thresholdNode12
def thresholdNode1140 : BoxExpr 1 := .sqrt ⟨(24593646867377376667477/2361183241434822606848:ℚ),(49187293734754753334969/4722366482869645213696:ℚ)⟩ thresholdNode1139
def thresholdNode1141 : BoxExpr 1 := .add ⟨(26954830108812199274325/2361183241434822606848:ℚ),(53909660217624398548665/4722366482869645213696:ℚ)⟩ thresholdNode1140 thresholdNode12
def thresholdNode1142 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode1143 : BoxExpr 1 := .mul ⟨(26954830108812199274325/4722366482869645213696:ℚ),(26954830108812199274333/4722366482869645213696:ℚ)⟩ thresholdNode1141 thresholdNode1142
def thresholdNode1144 : BoxExpr 1 := .add ⟨(28135421729529610577749/4722366482869645213696:ℚ),(28135421729529610577757/4722366482869645213696:ℚ)⟩ thresholdNode1143 thresholdNode181
def thresholdNode1145 : BoxExpr 1 := .mul ⟨(27092828508064728945771/4722366482869645213696:ℚ),(211662722719255694889/36893488147419103232:ℚ)⟩ thresholdNode990 thresholdNode1144
def thresholdNode1146 : BoxExpr 1 := .neg ⟨(-211662722719255694889/36893488147419103232:ℚ),(-27092828508064728945771/4722366482869645213696:ℚ)⟩ thresholdNode1145
def thresholdNode1147 : BoxExpr 1 := .add ⟨(175850280101833745813/1180591620717411303424:ℚ),(351700560203667491683/2361183241434822606848:ℚ)⟩ thresholdNode1134 thresholdNode1146
def thresholdNode1148 : BoxExpr 1 := .mul ⟨(-13229017031026792575809/4722366482869645213696:ℚ),(-1653627128878349071969/590295810358705651712:ℚ)⟩ thresholdNode1035 thresholdNode999
def thresholdNode1149 : BoxExpr 1 := .mul ⟨(-13229017031026792575809/4722366482869645213696:ℚ),(-1653627128878349071969/590295810358705651712:ℚ)⟩ thresholdNode999 thresholdNode1035
def thresholdNode1150 : BoxExpr 1 := .add ⟨(-13229017031026792575809/2361183241434822606848:ℚ),(-1653627128878349071969/295147905179352825856:ℚ)⟩ thresholdNode1148 thresholdNode1149
def thresholdNode1151 : BoxExpr 1 := .mul ⟨(-10832137365868900072443/4722366482869645213696:ℚ),(-10832137365868900072427/4722366482869645213696:ℚ)⟩ thresholdNode1018 thresholdNode1144
def thresholdNode1152 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode1137
def thresholdNode1153 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode1154 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode987 thresholdNode49
def thresholdNode1155 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode1153 thresholdNode1154
def thresholdNode1156 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode1155 thresholdNode49
def thresholdNode1157 : BoxExpr 1 := .mul ⟨(9058561446602625190039/4722366482869645213696:ℚ),(9058561446602625190045/4722366482869645213696:ℚ)⟩ thresholdNode1136 thresholdNode1136
def thresholdNode1158 : BoxExpr 1 := .inv ⟨(2461841797948439423787/4722366482869645213696:ℚ),(2461841797948439423789/4722366482869645213696:ℚ)⟩ thresholdNode1157
def thresholdNode1159 : BoxExpr 1 := .mul ⟨(2461841797948439423787/2361183241434822606848:ℚ),(2461841797948439423789/2361183241434822606848:ℚ)⟩ thresholdNode1156 thresholdNode1158
def thresholdNode1160 : BoxExpr 1 := .neg ⟨(-2461841797948439423789/2361183241434822606848:ℚ),(-2461841797948439423787/2361183241434822606848:ℚ)⟩ thresholdNode1159
def thresholdNode1161 : BoxExpr 1 := .mul ⟨(-45812578112217825017669/295147905179352825856:ℚ),(-366500624897742600141053/2361183241434822606848:ℚ)⟩ thresholdNode171 thresholdNode1160
def thresholdNode1162 : BoxExpr 1 := .add ⟨(-45812578112217825017669/295147905179352825856:ℚ),(-366500624897742600141053/2361183241434822606848:ℚ)⟩ thresholdNode1152 thresholdNode1161
def thresholdNode1163 : BoxExpr 1 := .add ⟨(-45812578112217825017669/295147905179352825856:ℚ),(-366500624897742600141053/2361183241434822606848:ℚ)⟩ thresholdNode1162 thresholdNode49
def thresholdNode1164 : BoxExpr 1 := .mul ⟨(24593646867377376667477/1180591620717411303424:ℚ),(49187293734754753334969/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode1140
def thresholdNode1165 : BoxExpr 1 := .inv ⟨(226692134342546322257/4722366482869645213696:ℚ),(113346067171273161129/2361183241434822606848:ℚ)⟩ thresholdNode1164
def thresholdNode1166 : BoxExpr 1 := .mul ⟨(-4398367280331196813235/590295810358705651712:ℚ),(-35186938242649574505695/4722366482869645213696:ℚ)⟩ thresholdNode1163 thresholdNode1165
def thresholdNode1167 : BoxExpr 1 := .add ⟨(-4398367280331196813235/590295810358705651712:ℚ),(-35186938242649574505695/4722366482869645213696:ℚ)⟩ thresholdNode1166 thresholdNode49
def thresholdNode1168 : BoxExpr 1 := .mul ⟨(-4398367280331196813235/1180591620717411303424:ℚ),(-17593469121324787252847/4722366482869645213696:ℚ)⟩ thresholdNode1167 thresholdNode1142
def thresholdNode1169 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode1170 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode1169
def thresholdNode1171 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode1170
def thresholdNode1172 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1171
def thresholdNode1173 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1141 thresholdNode1172
def thresholdNode1174 : BoxExpr 1 := .add ⟨(-4398367280331196813235/1180591620717411303424:ℚ),(-17593469121324787252847/4722366482869645213696:ℚ)⟩ thresholdNode1168 thresholdNode1173
def thresholdNode1175 : BoxExpr 1 := .add ⟨(-4398367280331196813235/1180591620717411303424:ℚ),(-17593469121324787252847/4722366482869645213696:ℚ)⟩ thresholdNode1174 thresholdNode49
def thresholdNode1176 : BoxExpr 1 := .mul ⟨(-16941521131197695605303/4722366482869645213696:ℚ),(-16941521131197695605205/4722366482869645213696:ℚ)⟩ thresholdNode990 thresholdNode1175
def thresholdNode1177 : BoxExpr 1 := .add ⟨(-13886829248533297838873/2361183241434822606848:ℚ),(-433963414016665557463/73786976294838206464:ℚ)⟩ thresholdNode1151 thresholdNode1176
def thresholdNode1178 : BoxExpr 1 := .neg ⟨(433963414016665557463/73786976294838206464:ℚ),(13886829248533297838873/2361183241434822606848:ℚ)⟩ thresholdNode1177
def thresholdNode1179 : BoxExpr 1 := .add ⟨(657812217506505263007/2361183241434822606848:ℚ),(657812217506505263121/2361183241434822606848:ℚ)⟩ thresholdNode1150 thresholdNode1178
def thresholdNode1180 : BoxExpr 1 := .mul ⟨(-11624994330209782189883/2361183241434822606848:ℚ),(-9785767133621681304163/2361183241434822606848:ℚ)⟩ thresholdNode1119 thresholdNode979
def thresholdNode1181 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1064 thresholdNode971
def thresholdNode1182 : BoxExpr 1 := .mul ⟨(-1584706442033564909883/2361183241434822606848:ℚ),(-1672446494583453548819/4722366482869645213696:ℚ)⟩ thresholdNode966 thresholdNode1072
def thresholdNode1183 : BoxExpr 1 := .add ⟨(-1584706442033564909883/2361183241434822606848:ℚ),(-1672446494583453548819/4722366482869645213696:ℚ)⟩ thresholdNode1181 thresholdNode1182
def thresholdNode1184 : BoxExpr 1 := .mul ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode1097 thresholdNode22
def thresholdNode1185 : BoxExpr 1 := .add ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode1184 thresholdNode1100
def thresholdNode1186 : BoxExpr 1 := .mul ⟨(7636952046515754369/73786976294838206464:ℚ),(977529861954016559237/4722366482869645213696:ℚ)⟩ thresholdNode1112 thresholdNode25
def thresholdNode1187 : BoxExpr 1 := .add ⟨(7636952046515754369/73786976294838206464:ℚ),(977529861954016559237/4722366482869645213696:ℚ)⟩ thresholdNode1186 thresholdNode1115
def thresholdNode1188 : BoxExpr 1 := .add ⟨(-3289128255318707891341/4722366482869645213696:ℚ),(-2800363324341699611719/4722366482869645213696:ℚ)⟩ thresholdNode1185 thresholdNode1187
def thresholdNode1189 : BoxExpr 1 := .add ⟨(-6458541139385837711107/4722366482869645213696:ℚ),(-2236404909462576580269/2361183241434822606848:ℚ)⟩ thresholdNode1183 thresholdNode1188
def thresholdNode1190 : BoxExpr 1 := .mul ⟨(4236441146371210551469/4722366482869645213696:ℚ),(8833019165380761302341/4722366482869645213696:ℚ)⟩ thresholdNode1189 thresholdNode1189
def thresholdNode1191 : BoxExpr 1 := .add ⟨(-19013547514048353828297/4722366482869645213696:ℚ),(-10738515101862601305985/4722366482869645213696:ℚ)⟩ thresholdNode1180 thresholdNode1190
def thresholdNode1192 : BoxExpr 1 := .mul ⟨(-11624994330209782189883/2361183241434822606848:ℚ),(-9785767133621681304163/2361183241434822606848:ℚ)⟩ thresholdNode979 thresholdNode1119
def thresholdNode1193 : BoxExpr 1 := .add ⟨(-19013547514048353828297/4722366482869645213696:ℚ),(-10738515101862601305985/4722366482869645213696:ℚ)⟩ thresholdNode1190 thresholdNode1192
def thresholdNode1194 : BoxExpr 1 := .add ⟨(-19013547514048353828297/2361183241434822606848:ℚ),(-10738515101862601305985/2361183241434822606848:ℚ)⟩ thresholdNode1191 thresholdNode1193
def thresholdNode1195 : BoxExpr 1 := .mul ⟨(-7303739239796809948013/590295810358705651712:ℚ),(-27182909735688012252953/2361183241434822606848:ℚ)⟩ thresholdNode1082 thresholdNode1130
def thresholdNode1196 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode1123
def thresholdNode1197 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode1198 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode1197 thresholdNode1078
def thresholdNode1199 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode1198 thresholdNode49
def thresholdNode1200 : BoxExpr 1 := .mul ⟨(7616704900220450765165/4722366482869645213696:ℚ),(9/4:ℚ)⟩ thresholdNode1122 thresholdNode1122
def thresholdNode1201 : BoxExpr 1 := .inv ⟨(524707386985516134855/1180591620717411303424:ℚ),(2927873075125330283155/4722366482869645213696:ℚ)⟩ thresholdNode1200
def thresholdNode1202 : BoxExpr 1 := .mul ⟨(524707386985516134855/590295810358705651712:ℚ),(2927873075125330283155/2361183241434822606848:ℚ)⟩ thresholdNode1199 thresholdNode1201
def thresholdNode1203 : BoxExpr 1 := .neg ⟨(-2927873075125330283155/2361183241434822606848:ℚ),(-524707386985516134855/590295810358705651712:ℚ)⟩ thresholdNode1202
def thresholdNode1204 : BoxExpr 1 := .mul ⟨(-435879881700336226149543/2361183241434822606848:ℚ),(-624916143283975377027331/4722366482869645213696:ℚ)⟩ thresholdNode171 thresholdNode1203
def thresholdNode1205 : BoxExpr 1 := .add ⟨(-435879881700336226149543/2361183241434822606848:ℚ),(-624916143283975377027331/4722366482869645213696:ℚ)⟩ thresholdNode1196 thresholdNode1204
def thresholdNode1206 : BoxExpr 1 := .add ⟨(-435879881700336226149543/2361183241434822606848:ℚ),(-624916143283975377027331/4722366482869645213696:ℚ)⟩ thresholdNode1205 thresholdNode49
def thresholdNode1207 : BoxExpr 1 := .mul ⟨(47282269747071556685363/2361183241434822606848:ℚ),(51346364194070011763559/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode1126
def thresholdNode1208 : BoxExpr 1 := .inv ⟨(217159925036193066453/4722366482869645213696:ℚ),(29478207843321421917/590295810358705651712:ℚ)⟩ thresholdNode1207
def thresholdNode1209 : BoxExpr 1 := .mul ⟨(-10883490549998081235999/1180591620717411303424:ℚ),(-14368510292639329900133/2361183241434822606848:ℚ)⟩ thresholdNode1206 thresholdNode1208
def thresholdNode1210 : BoxExpr 1 := .add ⟨(-10883490549998081235999/1180591620717411303424:ℚ),(-14368510292639329900133/2361183241434822606848:ℚ)⟩ thresholdNode1209 thresholdNode49
def thresholdNode1211 : BoxExpr 1 := .mul ⟨(-10883490549998081235999/2361183241434822606848:ℚ),(-14368510292639329900133/4722366482869645213696:ℚ)⟩ thresholdNode1210 thresholdNode1128
def thresholdNode1212 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode1213 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode1212
def thresholdNode1214 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode1213
def thresholdNode1215 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1214
def thresholdNode1216 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1127 thresholdNode1215
def thresholdNode1217 : BoxExpr 1 := .add ⟨(-10883490549998081235999/2361183241434822606848:ℚ),(-14368510292639329900133/4722366482869645213696:ℚ)⟩ thresholdNode1211 thresholdNode1216
def thresholdNode1218 : BoxExpr 1 := .add ⟨(-10883490549998081235999/2361183241434822606848:ℚ),(-14368510292639329900133/4722366482869645213696:ℚ)⟩ thresholdNode1217 thresholdNode49
def thresholdNode1219 : BoxExpr 1 := .mul ⟨(1939748889506309536515/2361183241434822606848:ℚ),(10883490549998081235999/4722366482869645213696:ℚ)⟩ thresholdNode1069 thresholdNode1218
def thresholdNode1220 : BoxExpr 1 := .add ⟨(-27275208069680930255537/2361183241434822606848:ℚ),(-43482328921377943269907/4722366482869645213696:ℚ)⟩ thresholdNode1195 thresholdNode1219
def thresholdNode1221 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode1203
def thresholdNode1222 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1196 thresholdNode1221
def thresholdNode1223 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode5
def thresholdNode1224 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode12 thresholdNode49
def thresholdNode1225 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1223 thresholdNode1224
def thresholdNode1226 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1224 thresholdNode1078
def thresholdNode1227 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1225 thresholdNode1226
def thresholdNode1228 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1227 thresholdNode49
def thresholdNode1229 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1228 thresholdNode1201
def thresholdNode1230 : BoxExpr 1 := .mul ⟨(374837839577778088837/147573952589676412928:ℚ),(3/1:ℚ)⟩ thresholdNode1199 thresholdNode1122
def thresholdNode1231 : BoxExpr 1 := .mul ⟨(374837839577778088837/147573952589676412928:ℚ),(3/1:ℚ)⟩ thresholdNode1122 thresholdNode1199
def thresholdNode1232 : BoxExpr 1 := .add ⟨(374837839577778088837/73786976294838206464:ℚ),(6/1:ℚ)⟩ thresholdNode1230 thresholdNode1231
def thresholdNode1233 : BoxExpr 1 := .mul ⟨(6142491666782782519563/2361183241434822606848:ℚ),(81/16:ℚ)⟩ thresholdNode1200 thresholdNode1200
def thresholdNode1234 : BoxExpr 1 := .inv ⟨(932813132418695350853/4722366482869645213696:ℚ),(1815284937147579070715/4722366482869645213696:ℚ)⟩ thresholdNode1233
def thresholdNode1235 : BoxExpr 1 := .mul ⟨(4738690712686972382331/4722366482869645213696:ℚ),(5445854811442737212145/2361183241434822606848:ℚ)⟩ thresholdNode1232 thresholdNode1234
def thresholdNode1236 : BoxExpr 1 := .neg ⟨(-5445854811442737212145/2361183241434822606848:ℚ),(-4738690712686972382331/4722366482869645213696:ℚ)⟩ thresholdNode1235
def thresholdNode1237 : BoxExpr 1 := .mul ⟨(-5445854811442737212145/1180591620717411303424:ℚ),(-4738690712686972382331/2361183241434822606848:ℚ)⟩ thresholdNode1199 thresholdNode1236
def thresholdNode1238 : BoxExpr 1 := .add ⟨(-5445854811442737212145/1180591620717411303424:ℚ),(-4738690712686972382331/2361183241434822606848:ℚ)⟩ thresholdNode1229 thresholdNode1237
def thresholdNode1239 : BoxExpr 1 := .neg ⟨(4738690712686972382331/2361183241434822606848:ℚ),(5445854811442737212145/1180591620717411303424:ℚ)⟩ thresholdNode1238
def thresholdNode1240 : BoxExpr 1 := .mul ⟨(352730445320288323921801/1180591620717411303424:ℚ),(405369100719514129347503/590295810358705651712:ℚ)⟩ thresholdNode171 thresholdNode1239
def thresholdNode1241 : BoxExpr 1 := .add ⟨(352730445320288323921801/1180591620717411303424:ℚ),(405369100719514129347503/590295810358705651712:ℚ)⟩ thresholdNode1221 thresholdNode1240
def thresholdNode1242 : BoxExpr 1 := .add ⟨(352730445320288323921801/1180591620717411303424:ℚ),(405369100719514129347503/590295810358705651712:ℚ)⟩ thresholdNode1222 thresholdNode1241
def thresholdNode1243 : BoxExpr 1 := .add ⟨(352730445320288323921801/1180591620717411303424:ℚ),(405369100719514129347503/590295810358705651712:ℚ)⟩ thresholdNode1242 thresholdNode49
def thresholdNode1244 : BoxExpr 1 := .mul ⟨(64881806476984707460103/4722366482869645213696:ℚ),(161946663277298003387737/4722366482869645213696:ℚ)⟩ thresholdNode1243 thresholdNode1208
def thresholdNode1245 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode1126
def thresholdNode1246 : BoxExpr 1 := .mul ⟨(-10883490549998081235999/590295810358705651712:ℚ),(-14368510292639329900133/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode1209
def thresholdNode1247 : BoxExpr 1 := .add ⟨(-10883490549998081235999/590295810358705651712:ℚ),(-14368510292639329900133/1180591620717411303424:ℚ)⟩ thresholdNode1245 thresholdNode1246
def thresholdNode1248 : BoxExpr 1 := .mul ⟨(1893637895783404711936733/4722366482869645213696:ℚ),(2233159264969186609693375/4722366482869645213696:ℚ)⟩ thresholdNode1207 thresholdNode1207
def thresholdNode1249 : BoxExpr 1 := .inv ⟨(9986186631806724903/4722366482869645213696:ℚ),(5888334102361403625/2361183241434822606848:ℚ)⟩ thresholdNode1248
def thresholdNode1250 : BoxExpr 1 := .mul ⟨(-3392664927147860411/73786976294838206464:ℚ),(-60768949603479121061/2361183241434822606848:ℚ)⟩ thresholdNode1247 thresholdNode1249
def thresholdNode1251 : BoxExpr 1 := .neg ⟨(60768949603479121061/2361183241434822606848:ℚ),(3392664927147860411/73786976294838206464:ℚ)⟩ thresholdNode1250
def thresholdNode1252 : BoxExpr 1 := .mul ⟨(-20041401089334769117179/2361183241434822606848:ℚ),(-8041624417626272001933/2361183241434822606848:ℚ)⟩ thresholdNode1206 thresholdNode1251
def thresholdNode1253 : BoxExpr 1 := .add ⟨(24799004298315169225745/4722366482869645213696:ℚ),(145863414442045459383871/4722366482869645213696:ℚ)⟩ thresholdNode1244 thresholdNode1252
def thresholdNode1254 : BoxExpr 1 := .add ⟨(24799004298315169225745/4722366482869645213696:ℚ),(145863414442045459383871/4722366482869645213696:ℚ)⟩ thresholdNode1253 thresholdNode49
def thresholdNode1255 : BoxExpr 1 := .mul ⟨(1549937768644698076609/590295810358705651712:ℚ),(2279115850656960302873/147573952589676412928:ℚ)⟩ thresholdNode1254 thresholdNode1128
def thresholdNode1256 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1210 thresholdNode1215
def thresholdNode1257 : BoxExpr 1 := .add ⟨(1549937768644698076609/590295810358705651712:ℚ),(2279115850656960302873/147573952589676412928:ℚ)⟩ thresholdNode1255 thresholdNode1256
def thresholdNode1258 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode5 thresholdNode49
def thresholdNode1259 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1223 thresholdNode1258
def thresholdNode1260 : BoxExpr 1 := .mul ⟨(16/1:ℚ),(16/1:ℚ)⟩ thresholdNode1212 thresholdNode1212
def thresholdNode1261 : BoxExpr 1 := .inv ⟨(1/16:ℚ),(1/16:ℚ)⟩ thresholdNode1260
def thresholdNode1262 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1259 thresholdNode1261
def thresholdNode1263 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1262
def thresholdNode1264 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode1263
def thresholdNode1265 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1214 thresholdNode1264
def thresholdNode1266 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1265
def thresholdNode1267 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1127 thresholdNode1266
def thresholdNode1268 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1256 thresholdNode1267
def thresholdNode1269 : BoxExpr 1 := .add ⟨(1549937768644698076609/590295810358705651712:ℚ),(2279115850656960302873/147573952589676412928:ℚ)⟩ thresholdNode1257 thresholdNode1268
def thresholdNode1270 : BoxExpr 1 := .add ⟨(1549937768644698076609/590295810358705651712:ℚ),(2279115850656960302873/147573952589676412928:ℚ)⟩ thresholdNode1269 thresholdNode49
def thresholdNode1271 : BoxExpr 1 := .mul ⟨(11624533264835235574567/4722366482869645213696:ℚ),(35801263428459795221655/2361183241434822606848:ℚ)⟩ thresholdNode970 thresholdNode1270
def thresholdNode1272 : BoxExpr 1 := .add ⟨(15504031043847854647597/4722366482869645213696:ℚ),(82486017406917671679309/4722366482869645213696:ℚ)⟩ thresholdNode1219 thresholdNode1271
def thresholdNode1273 : BoxExpr 1 := .add ⟨(-39046385095514005863477/4722366482869645213696:ℚ),(19501844242769864204701/2361183241434822606848:ℚ)⟩ thresholdNode1220 thresholdNode1272
def thresholdNode1274 : BoxExpr 1 := .neg ⟨(-19501844242769864204701/2361183241434822606848:ℚ),(39046385095514005863477/4722366482869645213696:ℚ)⟩ thresholdNode1273
def thresholdNode1275 : BoxExpr 1 := .add ⟨(-19257695878409109016499/1180591620717411303424:ℚ),(17569354891788803251507/4722366482869645213696:ℚ)⟩ thresholdNode1194 thresholdNode1274
def thresholdCell3Out1 : TaylorCertificate1 :=
  { center := (77/400:ℚ), radius := (23/400:ℚ)
    whole := thresholdNode1133, centerValue := thresholdNode1147, gradient := thresholdNode1179, hessian := thresholdNode1275 }
theorem thresholdCell3Out1_check : thresholdCell3Out1.check = true := by decide +kernel
theorem thresholdCell3Out1_lower_pos : 0 < thresholdCell3Out1.lower := by decide +kernel
theorem thresholdCell3Out1_positive (x : ℝ) (hx : (27/200:ℝ) ≤ x ∧ x ≤ (1/4:ℝ)) :
    0 < thresholdNode1133.eval (fun _ => x) := by
  apply thresholdCell3Out1.positive_sound thresholdCell3Out1_check thresholdCell3Out1_lower_pos x
  norm_num [thresholdCell3Out1]
  exact hx
theorem thresholdCell3_public (x : ℝ)
    (hx : (27/200:ℝ) ≤ x ∧ x ≤ (1/4:ℝ)) : qc x < fA (43/20) x := by
  have hf := thresholdCell3Out0_positive x hx
  have hg := thresholdCell3Out1_positive x hx
  have hfa : thresholdNode979.eval (fun _ => x) = thresholdFA 2 x := by
    norm_num [thresholdNode0, thresholdNode1, thresholdNode960, thresholdNode3, thresholdNode961, thresholdNode5, thresholdNode962, thresholdNode963, thresholdNode964, thresholdNode9, thresholdNode965, thresholdNode966, thresholdNode12, thresholdNode967, thresholdNode968, thresholdNode969, thresholdNode970, thresholdNode971, thresholdNode972, thresholdNode19, thresholdNode973, thresholdNode974, thresholdNode22, thresholdNode975, thresholdNode976, thresholdNode25, thresholdNode977, thresholdNode978, thresholdNode979, BoxExpr.eval, thresholdFA, ftilde, pow_two, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  have hgap : thresholdNode1133.eval (fun _ => x) =
      (thresholdNode979.eval (fun _ => x))^2 - (1-x^2)*(thresholdCapacity 3 x+1/4) := by
    norm_num [thresholdNode1120, thresholdNode12, thresholdNode967, thresholdNode968, thresholdNode969, thresholdNode970, thresholdNode171, thresholdNode5, thresholdNode1121, thresholdNode1122, thresholdNode1123, thresholdNode1124, thresholdNode1125, thresholdNode1126, thresholdNode1127, thresholdNode1128, thresholdNode1129, thresholdNode181, thresholdNode1130, thresholdNode1131, thresholdNode1132, thresholdNode1133, BoxExpr.eval, thresholdCapacity, Da, D5, beta5, eta5, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  rw [hfa] at hf
  rw [hgap, hfa] at hg
  refine threshold_positive_to_public 2 3 x ?_ ?_ ?_ hf hg
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdFADomain] <;> constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdCapacityDomain] <;> constructor <;> linarith [hx.1,hx.2]
theorem threshold_fgt_low_domain (x : ℝ)
    (hx : x ∈ Set.Icc (1/50:ℝ) (1/4:ℝ)) : qc x < fA (43/20) x := by
  have hlo := hx.1
  by_cases h0 : x ≤ (39/800:ℝ)
  · exact thresholdCell0_public x ⟨hlo, h0⟩
  have hlo : (39/800:ℝ) ≤ x := (lt_of_not_ge h0).le
  by_cases h1 : x ≤ (31/400:ℝ)
  · exact thresholdCell1_public x ⟨hlo, h1⟩
  have hlo : (31/400:ℝ) ≤ x := (lt_of_not_ge h1).le
  by_cases h2 : x ≤ (27/200:ℝ)
  · exact thresholdCell2_public x ⟨hlo, h2⟩
  have hlo : (27/200:ℝ) ≤ x := (lt_of_not_ge h2).le
  exact thresholdCell3_public x ⟨hlo,hx.2⟩
#print axioms threshold_fgt_low_domain
end GaussLocalMaxColoring.Certificate.ThresholdBranch2

open GaussLocalMaxColoring.Main

theorem solution (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (1/50:ℝ) (1/4:ℝ)) : qc ρ < fA (43/20) ρ  := by exact GaussLocalMaxColoring.Certificate.ThresholdBranch2.threshold_fgt_low_domain ρ hρ

#print axioms solution
