-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_61_branch_3
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T09:47:57.648823+00:00
-- url     : https://prove2.me/submissions/76cac1d1-620f-4f0f-b198-e5b9d1c278d5

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
namespace GaussLocalMaxColoring.Certificate.ThresholdBranch3
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
def thresholdNode14 : BoxExpr 1 := .mul ⟨(1/16:ℚ),(1065483937697463701341/4722366482869645213696:ℚ)⟩ thresholdNode13 thresholdNode13
def thresholdNode15 : BoxExpr 1 := .neg ⟨(-1065483937697463701341/4722366482869645213696:ℚ),(-1/16:ℚ)⟩ thresholdNode14
def thresholdNode16 : BoxExpr 1 := .add ⟨(3656882545172181512355/4722366482869645213696:ℚ),(15/16:ℚ)⟩ thresholdNode12 thresholdNode15
def thresholdNode17 : BoxExpr 1 := .sqrt ⟨(1038903856328635184045/1180591620717411303424:ℚ),(571551460713819648379/590295810358705651712:ℚ)⟩ thresholdNode16
def thresholdNode18 : BoxExpr 1 := .mul ⟨(10801898955791351462585/4722366482869645213696:ℚ),(2971324578812934206029/1180591620717411303424:ℚ)⟩ thresholdNode11 thresholdNode17
def thresholdNode19 : BoxExpr 1 := .lit (1/50:ℚ)
def thresholdNode20 : BoxExpr 1 := .neg ⟨(-47223664828696452137/2361183241434822606848:ℚ),(-94447329657392904273/4722366482869645213696:ℚ)⟩ thresholdNode19
def thresholdNode21 : BoxExpr 1 := .add ⟨(543072145530009199575/2361183241434822606848:ℚ),(2148676749705688572233/4722366482869645213696:ℚ)⟩ thresholdNode13 thresholdNode20
def thresholdNode22 : BoxExpr 1 := .lit (-4/5:ℚ)
def thresholdNode23 : BoxExpr 1 := .mul ⟨(-1718941399764550857787/4722366482869645213696:ℚ),(-868915432848014719319/4722366482869645213696:ℚ)⟩ thresholdNode21 thresholdNode22
def thresholdNode24 : BoxExpr 1 := .mul ⟨(62453296735951057951/1180591620717411303424:ℚ),(977647921116088300367/4722366482869645213696:ℚ)⟩ thresholdNode21 thresholdNode21
def thresholdNode25 : BoxExpr 1 := .lit (9/20:ℚ)
def thresholdNode26 : BoxExpr 1 := .mul ⟨(112415934124711904311/4722366482869645213696:ℚ),(219970782251119867583/2361183241434822606848:ℚ)⟩ thresholdNode24 thresholdNode25
def thresholdNode27 : BoxExpr 1 := .add ⟨(-401631366409959738369/1180591620717411303424:ℚ),(-428973868345774984153/4722366482869645213696:ℚ)⟩ thresholdNode23 thresholdNode26
def thresholdNode28 : BoxExpr 1 := .add ⟨(9195373490151512509109/4722366482869645213696:ℚ),(11456324446905961839963/4722366482869645213696:ℚ)⟩ thresholdNode18 thresholdNode27
def thresholdNode29 : BoxExpr 1 := .lit (1/4:ℚ)
def thresholdNode30 : BoxExpr 1 := .neg ⟨(-1/4:ℚ),(-1/4:ℚ)⟩ thresholdNode29
def thresholdNode31 : BoxExpr 1 := .add ⟨(0/1:ℚ),(531266229322835086541/2361183241434822606848:ℚ)⟩ thresholdNode13 thresholdNode30
def thresholdNode32 : BoxExpr 1 := .lit (39/100:ℚ)
def thresholdNode33 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(414387658871811367503/4722366482869645213696:ℚ)⟩ thresholdNode31 thresholdNode32
def thresholdNode34 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(14941862699704736809/295147905179352825856:ℚ)⟩ thresholdNode31 thresholdNode31
def thresholdNode35 : BoxExpr 1 := .lit (13/20:ℚ)
def thresholdNode36 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(77697686038464631407/2361183241434822606848:ℚ)⟩ thresholdNode34 thresholdNode35
def thresholdNode37 : BoxExpr 1 := .add ⟨(0/1:ℚ),(569783030948740630317/4722366482869645213696:ℚ)⟩ thresholdNode33 thresholdNode36
def thresholdNode38 : BoxExpr 1 := .add ⟨(9195373490151512509109/4722366482869645213696:ℚ),(1503263434731837808785/590295810358705651712:ℚ)⟩ thresholdNode28 thresholdNode37
def thresholdNode39 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode40 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode39 thresholdNode3
def thresholdNode41 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode42 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode41
def thresholdNode43 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode42 thresholdNode42
def thresholdNode44 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode43 thresholdNode9
def thresholdNode45 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode40 thresholdNode44
def thresholdNode46 : BoxExpr 1 := .var 0
def thresholdNode47 : BoxExpr 1 := .mul ⟨(620548470639589316361/4722366482869645213696:ℚ),(620548470639589316363/4722366482869645213696:ℚ)⟩ thresholdNode46 thresholdNode46
def thresholdNode48 : BoxExpr 1 := .neg ⟨(-620548470639589316363/4722366482869645213696:ℚ),(-620548470639589316361/4722366482869645213696:ℚ)⟩ thresholdNode47
def thresholdNode49 : BoxExpr 1 := .add ⟨(4101818012230055897333/4722366482869645213696:ℚ),(4101818012230055897335/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode48
def thresholdNode50 : BoxExpr 1 := .sqrt ⟨(4401168924250261999291/4722366482869645213696:ℚ),(4401168924250261999293/4722366482869645213696:ℚ)⟩ thresholdNode49
def thresholdNode51 : BoxExpr 1 := .mul ⟨(2860044610812479631963/1180591620717411303424:ℚ),(11440178443249918527867/4722366482869645213696:ℚ)⟩ thresholdNode45 thresholdNode50
def thresholdNode52 : BoxExpr 1 := .neg ⟨(-47223664828696452137/2361183241434822606848:ℚ),(-94447329657392904273/4722366482869645213696:ℚ)⟩ thresholdNode19
def thresholdNode53 : BoxExpr 1 := .add ⟨(808705260191426742845/2361183241434822606848:ℚ),(404352630095713371423/1180591620717411303424:ℚ)⟩ thresholdNode46 thresholdNode52
def thresholdNode54 : BoxExpr 1 := .mul ⟨(-646964208153141394277/2361183241434822606848:ℚ),(-1293928416306282788551/4722366482869645213696:ℚ)⟩ thresholdNode53 thresholdNode22
def thresholdNode55 : BoxExpr 1 := .mul ⟨(8655673487986364357/73786976294838206464:ℚ),(276981551615563659425/2361183241434822606848:ℚ)⟩ thresholdNode53 thresholdNode53
def thresholdNode56 : BoxExpr 1 := .mul ⟨(249283396454007293481/4722366482869645213696:ℚ),(249283396454007293483/4722366482869645213696:ℚ)⟩ thresholdNode55 thresholdNode25
def thresholdNode57 : BoxExpr 1 := .add ⟨(-1044645019852275495073/4722366482869645213696:ℚ),(-261161254963068873767/1180591620717411303424:ℚ)⟩ thresholdNode54 thresholdNode56
def thresholdNode58 : BoxExpr 1 := .add ⟨(10395533423397643032779/4722366482869645213696:ℚ),(10395533423397643032799/4722366482869645213696:ℚ)⟩ thresholdNode51 thresholdNode57
def thresholdNode59 : BoxExpr 1 := .neg ⟨(-1/4:ℚ),(-1/4:ℚ)⟩ thresholdNode29
def thresholdNode60 : BoxExpr 1 := .add ⟨(132816557330708771635/1180591620717411303424:ℚ),(531266229322835086541/4722366482869645213696:ℚ)⟩ thresholdNode46 thresholdNode59
def thresholdNode61 : BoxExpr 1 := .mul ⟨(103596914717952841875/2361183241434822606848:ℚ),(25899228679488210469/590295810358705651712:ℚ)⟩ thresholdNode60 thresholdNode32
def thresholdNode62 : BoxExpr 1 := .mul ⟨(59767450798818947235/4722366482869645213696:ℚ),(14941862699704736809/1180591620717411303424:ℚ)⟩ thresholdNode60 thresholdNode60
def thresholdNode63 : BoxExpr 1 := .mul ⟨(19424421509616157851/2361183241434822606848:ℚ),(4856105377404039463/590295810358705651712:ℚ)⟩ thresholdNode62 thresholdNode35
def thresholdNode64 : BoxExpr 1 := .add ⟨(61510668113784499863/1180591620717411303424:ℚ),(7688833514223062483/147573952589676412928:ℚ)⟩ thresholdNode61 thresholdNode63
def thresholdNode65 : BoxExpr 1 := .add ⟨(10641576095852781032231/4722366482869645213696:ℚ),(10641576095852781032255/4722366482869645213696:ℚ)⟩ thresholdNode58 thresholdNode64
def thresholdNode66 : BoxExpr 1 := .lit (0/1:ℚ)
def thresholdNode67 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66 thresholdNode1
def thresholdNode68 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode66
def thresholdNode69 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode67 thresholdNode68
def thresholdNode70 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode69 thresholdNode66
def thresholdNode71 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66
def thresholdNode72 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66 thresholdNode71
def thresholdNode73 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode72 thresholdNode42
def thresholdNode74 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode42 thresholdNode72
def thresholdNode75 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode73 thresholdNode74
def thresholdNode76 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode75 thresholdNode9
def thresholdNode77 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode43 thresholdNode66
def thresholdNode78 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode76 thresholdNode77
def thresholdNode79 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode70 thresholdNode78
def thresholdNode80 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode79 thresholdNode50
def thresholdNode81 : BoxExpr 1 := .mul ⟨(427964462510061597491/1180591620717411303424:ℚ),(1711857850040246389965/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode46
def thresholdNode82 : BoxExpr 1 := .mul ⟨(427964462510061597491/1180591620717411303424:ℚ),(1711857850040246389965/4722366482869645213696:ℚ)⟩ thresholdNode46 thresholdNode12
def thresholdNode83 : BoxExpr 1 := .add ⟨(427964462510061597491/590295810358705651712:ℚ),(1711857850040246389965/2361183241434822606848:ℚ)⟩ thresholdNode81 thresholdNode82
def thresholdNode84 : BoxExpr 1 := .neg ⟨(-1711857850040246389965/2361183241434822606848:ℚ),(-427964462510061597491/590295810358705651712:ℚ)⟩ thresholdNode83
def thresholdNode85 : BoxExpr 1 := .add ⟨(-1711857850040246389965/2361183241434822606848:ℚ),(-427964462510061597491/590295810358705651712:ℚ)⟩ thresholdNode66 thresholdNode84
def thresholdNode86 : BoxExpr 1 := .mul ⟨(4401168924250261999291/2361183241434822606848:ℚ),(4401168924250261999293/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode50
def thresholdNode87 : BoxExpr 1 := .inv ⟨(2533502528800294728859/4722366482869645213696:ℚ),(2533502528800294728861/4722366482869645213696:ℚ)⟩ thresholdNode86
def thresholdNode88 : BoxExpr 1 := .mul ⟨(-1836789333380213678425/4722366482869645213696:ℚ),(-1836789333380213678421/4722366482869645213696:ℚ)⟩ thresholdNode85 thresholdNode87
def thresholdNode89 : BoxExpr 1 := .mul ⟨(-596807294215232303127/590295810358705651712:ℚ),(-4774458353721858425001/4722366482869645213696:ℚ)⟩ thresholdNode45 thresholdNode88
def thresholdNode90 : BoxExpr 1 := .add ⟨(-596807294215232303127/590295810358705651712:ℚ),(-4774458353721858425001/4722366482869645213696:ℚ)⟩ thresholdNode80 thresholdNode89
def thresholdNode91 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode71
def thresholdNode92 : BoxExpr 1 := .mul ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode91 thresholdNode22
def thresholdNode93 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode53 thresholdNode66
def thresholdNode94 : BoxExpr 1 := .add ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode92 thresholdNode93
def thresholdNode95 : BoxExpr 1 := .mul ⟨(808705260191426742845/2361183241434822606848:ℚ),(404352630095713371423/1180591620717411303424:ℚ)⟩ thresholdNode91 thresholdNode53
def thresholdNode96 : BoxExpr 1 := .mul ⟨(808705260191426742845/2361183241434822606848:ℚ),(404352630095713371423/1180591620717411303424:ℚ)⟩ thresholdNode53 thresholdNode91
def thresholdNode97 : BoxExpr 1 := .add ⟨(808705260191426742845/1180591620717411303424:ℚ),(404352630095713371423/590295810358705651712:ℚ)⟩ thresholdNode95 thresholdNode96
def thresholdNode98 : BoxExpr 1 := .mul ⟨(45489670885767754285/147573952589676412928:ℚ),(363917367086142034281/1180591620717411303424:ℚ)⟩ thresholdNode97 thresholdNode25
def thresholdNode99 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode55 thresholdNode66
def thresholdNode100 : BoxExpr 1 := .add ⟨(45489670885767754285/147573952589676412928:ℚ),(363917367086142034281/1180591620717411303424:ℚ)⟩ thresholdNode98 thresholdNode99
def thresholdNode101 : BoxExpr 1 := .add ⟨(-2322223717951148033837/4722366482869645213696:ℚ),(-290277964743893504229/590295810358705651712:ℚ)⟩ thresholdNode94 thresholdNode100
def thresholdNode102 : BoxExpr 1 := .add ⟨(-7096682071673006458853/4722366482869645213696:ℚ),(-7096682071673006458833/4722366482869645213696:ℚ)⟩ thresholdNode90 thresholdNode101
def thresholdNode103 : BoxExpr 1 := .mul ⟨(1841722928319161633341/4722366482869645213696:ℚ),(920861464159580816671/2361183241434822606848:ℚ)⟩ thresholdNode91 thresholdNode32
def thresholdNode104 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode60 thresholdNode66
def thresholdNode105 : BoxExpr 1 := .add ⟨(1841722928319161633341/4722366482869645213696:ℚ),(920861464159580816671/2361183241434822606848:ℚ)⟩ thresholdNode103 thresholdNode104
def thresholdNode106 : BoxExpr 1 := .mul ⟨(132816557330708771635/1180591620717411303424:ℚ),(531266229322835086541/4722366482869645213696:ℚ)⟩ thresholdNode91 thresholdNode60
def thresholdNode107 : BoxExpr 1 := .mul ⟨(132816557330708771635/1180591620717411303424:ℚ),(531266229322835086541/4722366482869645213696:ℚ)⟩ thresholdNode60 thresholdNode91
def thresholdNode108 : BoxExpr 1 := .add ⟨(132816557330708771635/590295810358705651712:ℚ),(531266229322835086541/2361183241434822606848:ℚ)⟩ thresholdNode106 thresholdNode107
def thresholdNode109 : BoxExpr 1 := .mul ⟨(690646098119685612501/4722366482869645213696:ℚ),(86330762264960701563/590295810358705651712:ℚ)⟩ thresholdNode108 thresholdNode35
def thresholdNode110 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode62 thresholdNode66
def thresholdNode111 : BoxExpr 1 := .add ⟨(690646098119685612501/4722366482869645213696:ℚ),(86330762264960701563/590295810358705651712:ℚ)⟩ thresholdNode109 thresholdNode110
def thresholdNode112 : BoxExpr 1 := .add ⟨(1266184513219423622921/2361183241434822606848:ℚ),(1266184513219423622923/2361183241434822606848:ℚ)⟩ thresholdNode105 thresholdNode111
def thresholdNode113 : BoxExpr 1 := .add ⟨(-4564313045234159213011/4722366482869645213696:ℚ),(-4564313045234159212987/4722366482869645213696:ℚ)⟩ thresholdNode102 thresholdNode112
def thresholdNode114 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66 thresholdNode1
def thresholdNode115 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66 thresholdNode66
def thresholdNode116 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode114 thresholdNode115
def thresholdNode117 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode66
def thresholdNode118 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode115 thresholdNode117
def thresholdNode119 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode116 thresholdNode118
def thresholdNode120 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode119 thresholdNode66
def thresholdNode121 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66
def thresholdNode122 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66 thresholdNode121
def thresholdNode123 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode122 thresholdNode7
def thresholdNode124 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode122 thresholdNode122
def thresholdNode125 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode123 thresholdNode124
def thresholdNode126 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode7 thresholdNode122
def thresholdNode127 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode124 thresholdNode126
def thresholdNode128 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode125 thresholdNode127
def thresholdNode129 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode128 thresholdNode9
def thresholdNode130 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode123 thresholdNode126
def thresholdNode131 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode130 thresholdNode66
def thresholdNode132 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode129 thresholdNode131
def thresholdNode133 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode8 thresholdNode66
def thresholdNode134 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode131 thresholdNode133
def thresholdNode135 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode132 thresholdNode134
def thresholdNode136 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode120 thresholdNode135
def thresholdNode137 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode136 thresholdNode17
def thresholdNode138 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode114 thresholdNode117
def thresholdNode139 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode138 thresholdNode66
def thresholdNode140 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode130 thresholdNode9
def thresholdNode141 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode140 thresholdNode133
def thresholdNode142 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode139 thresholdNode141
def thresholdNode143 : BoxExpr 1 := .mul ⟨(1/4:ℚ),(1121562039681540738253/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode13
def thresholdNode144 : BoxExpr 1 := .mul ⟨(1/4:ℚ),(1121562039681540738253/2361183241434822606848:ℚ)⟩ thresholdNode13 thresholdNode12
def thresholdNode145 : BoxExpr 1 := .add ⟨(1/2:ℚ),(1121562039681540738253/1180591620717411303424:ℚ)⟩ thresholdNode143 thresholdNode144
def thresholdNode146 : BoxExpr 1 := .neg ⟨(-1121562039681540738253/1180591620717411303424:ℚ),(-1/2:ℚ)⟩ thresholdNode145
def thresholdNode147 : BoxExpr 1 := .add ⟨(-1121562039681540738253/1180591620717411303424:ℚ),(-1/2:ℚ)⟩ thresholdNode66 thresholdNode146
def thresholdNode148 : BoxExpr 1 := .mul ⟨(1038903856328635184045/590295810358705651712:ℚ),(571551460713819648379/295147905179352825856:ℚ)⟩ thresholdNode5 thresholdNode17
def thresholdNode149 : BoxExpr 1 := .inv ⟨(152413722857018572901/295147905179352825856:ℚ),(1341603042877979253005/2361183241434822606848:ℚ)⟩ thresholdNode148
def thresholdNode150 : BoxExpr 1 := .mul ⟨(-1274522890734080290355/2361183241434822606848:ℚ),(-152413722857018572901/590295810358705651712:ℚ)⟩ thresholdNode147 thresholdNode149
def thresholdNode151 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode142 thresholdNode150
def thresholdNode152 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode137 thresholdNode151
def thresholdNode153 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66 thresholdNode13
def thresholdNode154 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode12
def thresholdNode155 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode153 thresholdNode154
def thresholdNode156 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode13 thresholdNode66
def thresholdNode157 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode154 thresholdNode156
def thresholdNode158 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode155 thresholdNode157
def thresholdNode159 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode158
def thresholdNode160 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode66 thresholdNode159
def thresholdNode161 : BoxExpr 1 := .mul ⟨(-1341603042877979253005/1180591620717411303424:ℚ),(-152413722857018572901/147573952589676412928:ℚ)⟩ thresholdNode160 thresholdNode149
def thresholdNode162 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66 thresholdNode17
def thresholdNode163 : BoxExpr 1 := .mul ⟨(-1274522890734080290355/1180591620717411303424:ℚ),(-152413722857018572901/295147905179352825856:ℚ)⟩ thresholdNode5 thresholdNode150
def thresholdNode164 : BoxExpr 1 := .add ⟨(-1274522890734080290355/1180591620717411303424:ℚ),(-152413722857018572901/295147905179352825856:ℚ)⟩ thresholdNode162 thresholdNode163
def thresholdNode165 : BoxExpr 1 := .mul ⟨(14627530180688726049417/4722366482869645213696:ℚ),(8854437155380584775683/2361183241434822606848:ℚ)⟩ thresholdNode148 thresholdNode148
def thresholdNode166 : BoxExpr 1 := .inv ⟨(1259297728765238723651/4722366482869645213696:ℚ),(1524573521507552934205/4722366482869645213696:ℚ)⟩ thresholdNode165
def thresholdNode167 : BoxExpr 1 := .mul ⟨(-1645872982384607316037/4722366482869645213696:ℚ),(-325149275428306288855/2361183241434822606848:ℚ)⟩ thresholdNode164 thresholdNode166
def thresholdNode168 : BoxExpr 1 := .neg ⟨(325149275428306288855/2361183241434822606848:ℚ),(1645872982384607316037/4722366482869645213696:ℚ)⟩ thresholdNode167
def thresholdNode169 : BoxExpr 1 := .mul ⟨(-390894833316344237559/1180591620717411303424:ℚ),(-325149275428306288855/4722366482869645213696:ℚ)⟩ thresholdNode147 thresholdNode168
def thresholdNode170 : BoxExpr 1 := .add ⟨(-433124469048580872641/295147905179352825856:ℚ),(-5202388406852900621687/4722366482869645213696:ℚ)⟩ thresholdNode161 thresholdNode169
def thresholdNode171 : BoxExpr 1 := .mul ⟨(-18013473417942859060797/4722366482869645213696:ℚ),(-13205887016946374249/4611686018427387904:ℚ)⟩ thresholdNode11 thresholdNode170
def thresholdNode172 : BoxExpr 1 := .add ⟨(-18013473417942859060797/4722366482869645213696:ℚ),(-13205887016946374249/4611686018427387904:ℚ)⟩ thresholdNode151 thresholdNode171
def thresholdNode173 : BoxExpr 1 := .add ⟨(-18013473417942859060797/4722366482869645213696:ℚ),(-13205887016946374249/4611686018427387904:ℚ)⟩ thresholdNode152 thresholdNode172
def thresholdNode174 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode122 thresholdNode22
def thresholdNode175 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode121
def thresholdNode176 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode175 thresholdNode66
def thresholdNode177 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode174 thresholdNode176
def thresholdNode178 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode21 thresholdNode66
def thresholdNode179 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode176 thresholdNode178
def thresholdNode180 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode177 thresholdNode179
def thresholdNode181 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode122 thresholdNode21
def thresholdNode182 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode175 thresholdNode175
def thresholdNode183 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode181 thresholdNode182
def thresholdNode184 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode21 thresholdNode122
def thresholdNode185 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode182 thresholdNode184
def thresholdNode186 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode183 thresholdNode185
def thresholdNode187 : BoxExpr 1 := .mul ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode186 thresholdNode25
def thresholdNode188 : BoxExpr 1 := .mul ⟨(543072145530009199575/2361183241434822606848:ℚ),(2148676749705688572233/4722366482869645213696:ℚ)⟩ thresholdNode175 thresholdNode21
def thresholdNode189 : BoxExpr 1 := .mul ⟨(543072145530009199575/2361183241434822606848:ℚ),(2148676749705688572233/4722366482869645213696:ℚ)⟩ thresholdNode21 thresholdNode175
def thresholdNode190 : BoxExpr 1 := .add ⟨(543072145530009199575/1180591620717411303424:ℚ),(2148676749705688572233/2361183241434822606848:ℚ)⟩ thresholdNode188 thresholdNode189
def thresholdNode191 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode190 thresholdNode66
def thresholdNode192 : BoxExpr 1 := .add ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode187 thresholdNode191
def thresholdNode193 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode24 thresholdNode66
def thresholdNode194 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode191 thresholdNode193
def thresholdNode195 : BoxExpr 1 := .add ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode192 thresholdNode194
def thresholdNode196 : BoxExpr 1 := .add ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode180 thresholdNode195
def thresholdNode197 : BoxExpr 1 := .add ⟨(-13763343583360178368471/4722366482869645213696:ℚ),(-1159087308846300817331/590295810358705651712:ℚ)⟩ thresholdNode173 thresholdNode196
def thresholdNode198 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode122 thresholdNode32
def thresholdNode199 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode198 thresholdNode176
def thresholdNode200 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode31 thresholdNode66
def thresholdNode201 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode176 thresholdNode200
def thresholdNode202 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode199 thresholdNode201
def thresholdNode203 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode122 thresholdNode31
def thresholdNode204 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode203 thresholdNode182
def thresholdNode205 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode31 thresholdNode122
def thresholdNode206 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode182 thresholdNode205
def thresholdNode207 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode204 thresholdNode206
def thresholdNode208 : BoxExpr 1 := .mul ⟨(1534769106932634694451/1180591620717411303424:ℚ),(3069538213865269388903/2361183241434822606848:ℚ)⟩ thresholdNode207 thresholdNode35
def thresholdNode209 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(531266229322835086541/2361183241434822606848:ℚ)⟩ thresholdNode175 thresholdNode31
def thresholdNode210 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(531266229322835086541/2361183241434822606848:ℚ)⟩ thresholdNode31 thresholdNode175
def thresholdNode211 : BoxExpr 1 := .add ⟨(0/1:ℚ),(531266229322835086541/1180591620717411303424:ℚ)⟩ thresholdNode209 thresholdNode210
def thresholdNode212 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode211 thresholdNode66
def thresholdNode213 : BoxExpr 1 := .add ⟨(1534769106932634694451/1180591620717411303424:ℚ),(3069538213865269388903/2361183241434822606848:ℚ)⟩ thresholdNode208 thresholdNode212
def thresholdNode214 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode34 thresholdNode66
def thresholdNode215 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode212 thresholdNode214
def thresholdNode216 : BoxExpr 1 := .add ⟨(1534769106932634694451/1180591620717411303424:ℚ),(3069538213865269388903/2361183241434822606848:ℚ)⟩ thresholdNode213 thresholdNode215
def thresholdNode217 : BoxExpr 1 := .add ⟨(1534769106932634694451/1180591620717411303424:ℚ),(3069538213865269388903/2361183241434822606848:ℚ)⟩ thresholdNode202 thresholdNode216
def thresholdNode218 : BoxExpr 1 := .add ⟨(-7624267155629639590667/4722366482869645213696:ℚ),(-1566811021519933880421/2361183241434822606848:ℚ)⟩ thresholdNode197 thresholdNode217
def thresholdCell0Out0 : TaylorCertificate1 :=
  { center := (29/80:ℚ), radius := (9/80:ℚ)
    whole := thresholdNode38, centerValue := thresholdNode65, gradient := thresholdNode113, hessian := thresholdNode218 }
theorem thresholdCell0Out0_check : thresholdCell0Out0.check = true := by decide +kernel
theorem thresholdCell0Out0_lower_pos : 0 < thresholdCell0Out0.lower := by decide +kernel
theorem thresholdCell0Out0_positive (x : ℝ) (hx : (1/4:ℝ) ≤ x ∧ x ≤ (19/40:ℝ)) :
    0 < thresholdNode38.eval (fun _ => x) := by
  apply thresholdCell0Out0.positive_sound thresholdCell0Out0_check thresholdCell0Out0_lower_pos x
  norm_num [thresholdCell0Out0]
  exact hx
def thresholdNode219 : BoxExpr 1 := .mul ⟨(1119074699227912986023/295147905179352825856:ℚ),(1914125862445598980087/295147905179352825856:ℚ)⟩ thresholdNode38 thresholdNode38
def thresholdNode220 : BoxExpr 1 := .lit (1769451672197/307399000000:ℚ)
def thresholdNode221 : BoxExpr 1 := .mul ⟨(21049765726573404488377/4722366482869645213696:ℚ),(6370994469301877871787/1180591620717411303424:ℚ)⟩ thresholdNode16 thresholdNode220
def thresholdNode222 : BoxExpr 1 := .neg ⟨(-6370994469301877871787/1180591620717411303424:ℚ),(-21049765726573404488377/4722366482869645213696:ℚ)⟩ thresholdNode221
def thresholdNode223 : BoxExpr 1 := .add ⟨(-1894695672390225927695/1180591620717411303424:ℚ),(9576248072556179193015/4722366482869645213696:ℚ)⟩ thresholdNode219 thresholdNode222
def thresholdNode224 : BoxExpr 1 := .mul ⟨(23980168039607705982395/4722366482869645213696:ℚ),(2997521004950963247813/590295810358705651712:ℚ)⟩ thresholdNode65 thresholdNode65
def thresholdNode225 : BoxExpr 1 := .mul ⟨(5902726375808189848209/1180591620717411303424:ℚ),(11805452751616379696425/2361183241434822606848:ℚ)⟩ thresholdNode49 thresholdNode220
def thresholdNode226 : BoxExpr 1 := .neg ⟨(-11805452751616379696425/2361183241434822606848:ℚ),(-5902726375808189848209/1180591620717411303424:ℚ)⟩ thresholdNode225
def thresholdNode227 : BoxExpr 1 := .add ⟨(369262536374946589545/4722366482869645213696:ℚ),(92315634093736647417/1180591620717411303424:ℚ)⟩ thresholdNode224 thresholdNode226
def thresholdNode228 : BoxExpr 1 := .mul ⟨(-5142705968749523947527/2361183241434822606848:ℚ),(-160709561523422623359/73786976294838206464:ℚ)⟩ thresholdNode113 thresholdNode65
def thresholdNode229 : BoxExpr 1 := .mul ⟨(-5142705968749523947527/2361183241434822606848:ℚ),(-160709561523422623359/73786976294838206464:ℚ)⟩ thresholdNode65 thresholdNode113
def thresholdNode230 : BoxExpr 1 := .add ⟨(-5142705968749523947527/1180591620717411303424:ℚ),(-160709561523422623359/36893488147419103232:ℚ)⟩ thresholdNode228 thresholdNode229
def thresholdNode231 : BoxExpr 1 := .mul ⟨(-19707609558373808883397/4722366482869645213696:ℚ),(-19707609558373808883383/4722366482869645213696:ℚ)⟩ thresholdNode85 thresholdNode220
def thresholdNode232 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode49 thresholdNode66
def thresholdNode233 : BoxExpr 1 := .add ⟨(-19707609558373808883397/4722366482869645213696:ℚ),(-19707609558373808883383/4722366482869645213696:ℚ)⟩ thresholdNode231 thresholdNode232
def thresholdNode234 : BoxExpr 1 := .neg ⟨(19707609558373808883383/4722366482869645213696:ℚ),(19707609558373808883397/4722366482869645213696:ℚ)⟩ thresholdNode233
def thresholdNode235 : BoxExpr 1 := .add ⟨(-863214316624286906725/4722366482869645213696:ℚ),(-863214316624286906555/4722366482869645213696:ℚ)⟩ thresholdNode230 thresholdNode234
def thresholdNode236 : BoxExpr 1 := .mul ⟨(-9708083498610859676887/2361183241434822606848:ℚ),(-1525444137343470645333/1180591620717411303424:ℚ)⟩ thresholdNode218 thresholdNode38
def thresholdNode237 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode142 thresholdNode17
def thresholdNode238 : BoxExpr 1 := .mul ⟨(-6625862152059263205471/4722366482869645213696:ℚ),(-198088305254195613735/295147905179352825856:ℚ)⟩ thresholdNode11 thresholdNode150
def thresholdNode239 : BoxExpr 1 := .add ⟨(-6625862152059263205471/4722366482869645213696:ℚ),(-198088305254195613735/295147905179352825856:ℚ)⟩ thresholdNode237 thresholdNode238
def thresholdNode240 : BoxExpr 1 := .mul ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode175 thresholdNode22
def thresholdNode241 : BoxExpr 1 := .add ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode240 thresholdNode178
def thresholdNode242 : BoxExpr 1 := .mul ⟨(488764930977008279617/2361183241434822606848:ℚ),(1933809074735119715011/4722366482869645213696:ℚ)⟩ thresholdNode190 thresholdNode25
def thresholdNode243 : BoxExpr 1 := .add ⟨(488764930977008279617/2361183241434822606848:ℚ),(1933809074735119715011/4722366482869645213696:ℚ)⟩ thresholdNode242 thresholdNode193
def thresholdNode244 : BoxExpr 1 := .add ⟨(-2800363324341699611723/4722366482869645213696:ℚ),(-1844084111560596455945/4722366482869645213696:ℚ)⟩ thresholdNode241 thresholdNode243
def thresholdNode245 : BoxExpr 1 := .add ⟨(-4713112738200481408597/2361183241434822606848:ℚ),(-5013496995627726275705/4722366482869645213696:ℚ)⟩ thresholdNode239 thresholdNode244
def thresholdNode246 : BoxExpr 1 := .mul ⟨(1841722928319161633341/4722366482869645213696:ℚ),(920861464159580816671/2361183241434822606848:ℚ)⟩ thresholdNode175 thresholdNode32
def thresholdNode247 : BoxExpr 1 := .add ⟨(1841722928319161633341/4722366482869645213696:ℚ),(920861464159580816671/2361183241434822606848:ℚ)⟩ thresholdNode246 thresholdNode200
def thresholdNode248 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(1381292196239371225007/4722366482869645213696:ℚ)⟩ thresholdNode211 thresholdNode35
def thresholdNode249 : BoxExpr 1 := .add ⟨(0/1:ℚ),(1381292196239371225007/4722366482869645213696:ℚ)⟩ thresholdNode248 thresholdNode214
def thresholdNode250 : BoxExpr 1 := .add ⟨(1841722928319161633341/4722366482869645213696:ℚ),(3223015124558532858349/4722366482869645213696:ℚ)⟩ thresholdNode247 thresholdNode249
def thresholdNode251 : BoxExpr 1 := .add ⟨(-7584502548081801183853/4722366482869645213696:ℚ),(-447620467767298354339/1180591620717411303424:ℚ)⟩ thresholdNode245 thresholdNode250
def thresholdNode252 : BoxExpr 1 := .mul ⟨(84857489943245378979/590295810358705651712:ℚ),(12181324577524795387833/4722366482869645213696:ℚ)⟩ thresholdNode251 thresholdNode251
def thresholdNode253 : BoxExpr 1 := .add ⟨(-9368653538837878160971/2361183241434822606848:ℚ),(6079548028150912806501/4722366482869645213696:ℚ)⟩ thresholdNode236 thresholdNode252
def thresholdNode254 : BoxExpr 1 := .mul ⟨(-9708083498610859676887/2361183241434822606848:ℚ),(-1525444137343470645333/1180591620717411303424:ℚ)⟩ thresholdNode38 thresholdNode218
def thresholdNode255 : BoxExpr 1 := .add ⟨(-9368653538837878160971/2361183241434822606848:ℚ),(6079548028150912806501/4722366482869645213696:ℚ)⟩ thresholdNode252 thresholdNode254
def thresholdNode256 : BoxExpr 1 := .add ⟨(-9368653538837878160971/1180591620717411303424:ℚ),(6079548028150912806501/2361183241434822606848:ℚ)⟩ thresholdNode253 thresholdNode255
def thresholdNode257 : BoxExpr 1 := .mul ⟨(-27182909735688012252957/2361183241434822606848:ℚ),(-6795727433922003063239/590295810358705651712:ℚ)⟩ thresholdNode160 thresholdNode220
def thresholdNode258 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode147 thresholdNode66
def thresholdNode259 : BoxExpr 1 := .add ⟨(-27182909735688012252957/2361183241434822606848:ℚ),(-6795727433922003063239/590295810358705651712:ℚ)⟩ thresholdNode257 thresholdNode258
def thresholdNode260 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode16 thresholdNode66
def thresholdNode261 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode258 thresholdNode260
def thresholdNode262 : BoxExpr 1 := .add ⟨(-27182909735688012252957/2361183241434822606848:ℚ),(-6795727433922003063239/590295810358705651712:ℚ)⟩ thresholdNode259 thresholdNode261
def thresholdNode263 : BoxExpr 1 := .neg ⟨(6795727433922003063239/590295810358705651712:ℚ),(27182909735688012252957/2361183241434822606848:ℚ)⟩ thresholdNode262
def thresholdNode264 : BoxExpr 1 := .add ⟨(4222801329006127965507/1180591620717411303424:ℚ),(16631228881919462529729/1180591620717411303424:ℚ)⟩ thresholdNode256 thresholdNode263
def thresholdCell0Out1 : TaylorCertificate1 :=
  { center := (29/80:ℚ), radius := (9/80:ℚ)
    whole := thresholdNode223, centerValue := thresholdNode227, gradient := thresholdNode235, hessian := thresholdNode264 }
theorem thresholdCell0Out1_check : thresholdCell0Out1.check = true := by decide +kernel
theorem thresholdCell0Out1_lower_pos : 0 < thresholdCell0Out1.lower := by decide +kernel
theorem thresholdCell0Out1_positive (x : ℝ) (hx : (1/4:ℝ) ≤ x ∧ x ≤ (19/40:ℝ)) :
    0 < thresholdNode223.eval (fun _ => x) := by
  apply thresholdCell0Out1.positive_sound thresholdCell0Out1_check thresholdCell0Out1_lower_pos x
  norm_num [thresholdCell0Out1]
  exact hx
theorem thresholdCell0_public (x : ℝ)
    (hx : (1/4:ℝ) ≤ x ∧ x ≤ (19/40:ℝ)) : qc x < fA (43/20) x := by
  have hf := thresholdCell0Out0_positive x hx
  have hg := thresholdCell0Out1_positive x hx
  have hfa : thresholdNode38.eval (fun _ => x) = thresholdFA 3 x := by
    norm_num [thresholdNode0, thresholdNode1, thresholdNode2, thresholdNode3, thresholdNode4, thresholdNode5, thresholdNode6, thresholdNode7, thresholdNode8, thresholdNode9, thresholdNode10, thresholdNode11, thresholdNode12, thresholdNode13, thresholdNode14, thresholdNode15, thresholdNode16, thresholdNode17, thresholdNode18, thresholdNode19, thresholdNode20, thresholdNode21, thresholdNode22, thresholdNode23, thresholdNode24, thresholdNode25, thresholdNode26, thresholdNode27, thresholdNode28, thresholdNode29, thresholdNode30, thresholdNode31, thresholdNode32, thresholdNode33, thresholdNode34, thresholdNode35, thresholdNode36, thresholdNode37, thresholdNode38, BoxExpr.eval, thresholdFA, ftilde, pow_two, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  have hgap : thresholdNode223.eval (fun _ => x) =
      (thresholdNode38.eval (fun _ => x))^2 - (1-x^2)*(thresholdCapacity 4 x+1/4) := by
    norm_num [thresholdNode219, thresholdNode12, thresholdNode13, thresholdNode14, thresholdNode15, thresholdNode16, thresholdNode220, thresholdNode221, thresholdNode222, thresholdNode223, BoxExpr.eval, thresholdCapacity, Da, D5, beta5, eta5, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  rw [hfa] at hf
  rw [hgap, hfa] at hg
  refine threshold_positive_to_public 3 4 x ?_ ?_ ?_ hf hg
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdFADomain] <;> constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdCapacityDomain] <;> linarith [hx.1,hx.2]
def thresholdNode265 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode266 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode265 thresholdNode3
def thresholdNode267 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode268 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode267
def thresholdNode269 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode268 thresholdNode268
def thresholdNode270 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode269 thresholdNode9
def thresholdNode271 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode266 thresholdNode270
def thresholdNode272 : BoxExpr 1 := .var 0
def thresholdNode273 : BoxExpr 1 := .mul ⟨(1065483937697463701339/4722366482869645213696:ℚ),(2313959576606126154713/4722366482869645213696:ℚ)⟩ thresholdNode272 thresholdNode272
def thresholdNode274 : BoxExpr 1 := .neg ⟨(-2313959576606126154713/4722366482869645213696:ℚ),(-1065483937697463701339/4722366482869645213696:ℚ)⟩ thresholdNode273
def thresholdNode275 : BoxExpr 1 := .add ⟨(2408406906263519058983/4722366482869645213696:ℚ),(3656882545172181512357/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode274
def thresholdNode276 : BoxExpr 1 := .sqrt ⟨(421555528134539949789/590295810358705651712:ℚ),(2077807712657270368091/2361183241434822606848:ℚ)⟩ thresholdNode275
def thresholdNode277 : BoxExpr 1 := .mul ⟨(2191540724113032836967/1180591620717411303424:ℚ),(10801898955791351462599/4722366482869645213696:ℚ)⟩ thresholdNode271 thresholdNode276
def thresholdNode278 : BoxExpr 1 := .neg ⟨(-47223664828696452137/2361183241434822606848:ℚ),(-94447329657392904273/4722366482869645213696:ℚ)⟩ thresholdNode19
def thresholdNode279 : BoxExpr 1 := .add ⟨(2148676749705688572231/4722366482869645213696:ℚ),(3211209208351358745315/4722366482869645213696:ℚ)⟩ thresholdNode272 thresholdNode278
def thresholdNode280 : BoxExpr 1 := .mul ⟨(-2568967366681086996253/4722366482869645213696:ℚ),(-214867674970568857223/590295810358705651712:ℚ)⟩ thresholdNode279 thresholdNode22
def thresholdNode281 : BoxExpr 1 := .mul ⟨(244411980279022075091/1180591620717411303424:ℚ),(34119097838733186669/73786976294838206464:ℚ)⟩ thresholdNode279 thresholdNode279
def thresholdNode282 : BoxExpr 1 := .mul ⟨(439941564502239735163/4722366482869645213696:ℚ),(245657504438878944017/1180591620717411303424:ℚ)⟩ thresholdNode281 thresholdNode25
def thresholdNode283 : BoxExpr 1 := .add ⟨(-1064512901089423630545/2361183241434822606848:ℚ),(-184077845502258770429/1180591620717411303424:ℚ)⟩ thresholdNode280 thresholdNode282
def thresholdNode284 : BoxExpr 1 := .add ⟨(3318568547136642043389/2361183241434822606848:ℚ),(10065587573782316380883/4722366482869645213696:ℚ)⟩ thresholdNode277 thresholdNode283
def thresholdNode285 : BoxExpr 1 := .neg ⟨(-1/4:ℚ),(-1/4:ℚ)⟩ thresholdNode29
def thresholdNode286 : BoxExpr 1 := .add ⟨(1062532458645670173081/4722366482869645213696:ℚ),(531266229322835086541/1180591620717411303424:ℚ)⟩ thresholdNode272 thresholdNode285
def thresholdNode287 : BoxExpr 1 := .mul ⟨(414387658871811367501/4722366482869645213696:ℚ),(828775317743622735005/4722366482869645213696:ℚ)⟩ thresholdNode286 thresholdNode32
def thresholdNode288 : BoxExpr 1 := .mul ⟨(239069803195275788943/4722366482869645213696:ℚ),(956279212781103155775/4722366482869645213696:ℚ)⟩ thresholdNode286 thresholdNode286
def thresholdNode289 : BoxExpr 1 := .mul ⟨(38848843019232315703/1180591620717411303424:ℚ),(310790744153858525627/2361183241434822606848:ℚ)⟩ thresholdNode288 thresholdNode35
def thresholdNode290 : BoxExpr 1 := .add ⟨(569783030948740630313/4722366482869645213696:ℚ),(1450356806051339786259/4722366482869645213696:ℚ)⟩ thresholdNode287 thresholdNode289
def thresholdNode291 : BoxExpr 1 := .add ⟨(7206920125222024717091/4722366482869645213696:ℚ),(5757972189916828083571/2361183241434822606848:ℚ)⟩ thresholdNode284 thresholdNode290
def thresholdNode292 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode293 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode292 thresholdNode3
def thresholdNode294 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode295 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode294
def thresholdNode296 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode295 thresholdNode295
def thresholdNode297 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode296 thresholdNode9
def thresholdNode298 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode293 thresholdNode297
def thresholdNode299 : BoxExpr 1 := .var 0
def thresholdNode300 : BoxExpr 1 := .mul ⟨(1629954306352975980789/4722366482869645213696:ℚ),(1629954306352975980791/4722366482869645213696:ℚ)⟩ thresholdNode299 thresholdNode299
def thresholdNode301 : BoxExpr 1 := .neg ⟨(-1629954306352975980791/4722366482869645213696:ℚ),(-1629954306352975980789/4722366482869645213696:ℚ)⟩ thresholdNode300
def thresholdNode302 : BoxExpr 1 := .add ⟨(3092412176516669232905/4722366482869645213696:ℚ),(3092412176516669232907/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode301
def thresholdNode303 : BoxExpr 1 := .sqrt ⟨(3821453076200241366485/4722366482869645213696:ℚ),(3821453076200241366487/4722366482869645213696:ℚ)⟩ thresholdNode302
def thresholdNode304 : BoxExpr 1 := .mul ⟨(38801929896957411703/18446744073709551616:ℚ),(4966647026810548697991/2361183241434822606848:ℚ)⟩ thresholdNode298 thresholdNode303
def thresholdNode305 : BoxExpr 1 := .neg ⟨(-47223664828696452137/2361183241434822606848:ℚ),(-94447329657392904273/4722366482869645213696:ℚ)⟩ thresholdNode19
def thresholdNode306 : BoxExpr 1 := .add ⟨(669985744757130914693/1180591620717411303424:ℚ),(1339971489514261829387/2361183241434822606848:ℚ)⟩ thresholdNode299 thresholdNode305
def thresholdNode307 : BoxExpr 1 := .mul ⟨(-535988595805704731755/1180591620717411303424:ℚ),(-2143954383222818927017/4722366482869645213696:ℚ)⟩ thresholdNode306 thresholdNode22
def thresholdNode308 : BoxExpr 1 := .mul ⟨(47527113768708974261/147573952589676412928:ℚ),(380216910149671794089/1180591620717411303424:ℚ)⟩ thresholdNode306 thresholdNode306
def thresholdNode309 : BoxExpr 1 := .mul ⟨(342195219134704614679/2361183241434822606848:ℚ),(684390438269409229361/4722366482869645213696:ℚ)⟩ thresholdNode308 thresholdNode25
def thresholdNode310 : BoxExpr 1 := .add ⟨(-729781972476704848831/2361183241434822606848:ℚ),(-182445493119176212207/590295810358705651712:ℚ)⟩ thresholdNode307 thresholdNode309
def thresholdNode311 : BoxExpr 1 := .add ⟨(4236865054333843849153/2361183241434822606848:ℚ),(4236865054333843849163/2361183241434822606848:ℚ)⟩ thresholdNode304 thresholdNode310
def thresholdNode312 : BoxExpr 1 := .neg ⟨(-1/4:ℚ),(-1/4:ℚ)⟩ thresholdNode29
def thresholdNode313 : BoxExpr 1 := .add ⟨(796899343984252629811/2361183241434822606848:ℚ),(1593798687968505259623/4722366482869645213696:ℚ)⟩ thresholdNode299 thresholdNode312
def thresholdNode314 : BoxExpr 1 := .mul ⟨(155395372076929262813/1180591620717411303424:ℚ),(310790744153858525627/2361183241434822606848:ℚ)⟩ thresholdNode313 thresholdNode32
def thresholdNode315 : BoxExpr 1 := .mul ⟨(268953528594685262561/2361183241434822606848:ℚ),(537907057189370525123/4722366482869645213696:ℚ)⟩ thresholdNode313 thresholdNode313
def thresholdNode316 : BoxExpr 1 := .mul ⟨(349639587173090841329/4722366482869645213696:ℚ),(349639587173090841331/4722366482869645213696:ℚ)⟩ thresholdNode315 thresholdNode35
def thresholdNode317 : BoxExpr 1 := .add ⟨(971221075480807892581/4722366482869645213696:ℚ),(971221075480807892585/4722366482869645213696:ℚ)⟩ thresholdNode314 thresholdNode316
def thresholdNode318 : BoxExpr 1 := .add ⟨(9444951184148495590887/4722366482869645213696:ℚ),(9444951184148495590911/4722366482869645213696:ℚ)⟩ thresholdNode311 thresholdNode317
def thresholdNode319 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66 thresholdNode1
def thresholdNode320 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode66
def thresholdNode321 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode319 thresholdNode320
def thresholdNode322 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode321 thresholdNode66
def thresholdNode323 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66
def thresholdNode324 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66 thresholdNode323
def thresholdNode325 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode324 thresholdNode295
def thresholdNode326 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode295 thresholdNode324
def thresholdNode327 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode325 thresholdNode326
def thresholdNode328 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode327 thresholdNode9
def thresholdNode329 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode296 thresholdNode66
def thresholdNode330 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode328 thresholdNode329
def thresholdNode331 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode322 thresholdNode330
def thresholdNode332 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode331 thresholdNode303
def thresholdNode333 : BoxExpr 1 := .mul ⟨(1387195154342958281523/2361183241434822606848:ℚ),(2774390308685916563047/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode299
def thresholdNode334 : BoxExpr 1 := .mul ⟨(1387195154342958281523/2361183241434822606848:ℚ),(2774390308685916563047/4722366482869645213696:ℚ)⟩ thresholdNode299 thresholdNode12
def thresholdNode335 : BoxExpr 1 := .add ⟨(1387195154342958281523/1180591620717411303424:ℚ),(2774390308685916563047/2361183241434822606848:ℚ)⟩ thresholdNode333 thresholdNode334
def thresholdNode336 : BoxExpr 1 := .neg ⟨(-2774390308685916563047/2361183241434822606848:ℚ),(-1387195154342958281523/1180591620717411303424:ℚ)⟩ thresholdNode335
def thresholdNode337 : BoxExpr 1 := .add ⟨(-2774390308685916563047/2361183241434822606848:ℚ),(-1387195154342958281523/1180591620717411303424:ℚ)⟩ thresholdNode66 thresholdNode336
def thresholdNode338 : BoxExpr 1 := .mul ⟨(3821453076200241366485/2361183241434822606848:ℚ),(3821453076200241366487/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode303
def thresholdNode339 : BoxExpr 1 := .inv ⟨(2917835801441367781615/4722366482869645213696:ℚ),(1458917900720683890809/2361183241434822606848:ℚ)⟩ thresholdNode338
def thresholdNode340 : BoxExpr 1 := .mul ⟨(-1714228533346803571701/2361183241434822606848:ℚ),(-3428457066693607143397/4722366482869645213696:ℚ)⟩ thresholdNode337 thresholdNode339
def thresholdNode341 : BoxExpr 1 := .mul ⟨(-4455879938155013864103/2361183241434822606848:ℚ),(-8911759876310027728185/4722366482869645213696:ℚ)⟩ thresholdNode298 thresholdNode340
def thresholdNode342 : BoxExpr 1 := .add ⟨(-4455879938155013864103/2361183241434822606848:ℚ),(-8911759876310027728185/4722366482869645213696:ℚ)⟩ thresholdNode332 thresholdNode341
def thresholdNode343 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode323
def thresholdNode344 : BoxExpr 1 := .mul ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode343 thresholdNode22
def thresholdNode345 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode306 thresholdNode66
def thresholdNode346 : BoxExpr 1 := .add ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode344 thresholdNode345
def thresholdNode347 : BoxExpr 1 := .mul ⟨(669985744757130914693/1180591620717411303424:ℚ),(1339971489514261829387/2361183241434822606848:ℚ)⟩ thresholdNode343 thresholdNode306
def thresholdNode348 : BoxExpr 1 := .mul ⟨(669985744757130914693/1180591620717411303424:ℚ),(1339971489514261829387/2361183241434822606848:ℚ)⟩ thresholdNode306 thresholdNode343
def thresholdNode349 : BoxExpr 1 := .add ⟨(669985744757130914693/590295810358705651712:ℚ),(1339971489514261829387/1180591620717411303424:ℚ)⟩ thresholdNode347 thresholdNode348
def thresholdNode350 : BoxExpr 1 := .mul ⟨(1205974340562835646447/2361183241434822606848:ℚ),(1205974340562835646449/2361183241434822606848:ℚ)⟩ thresholdNode349 thresholdNode25
def thresholdNode351 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode308 thresholdNode66
def thresholdNode352 : BoxExpr 1 := .add ⟨(1205974340562835646447/2361183241434822606848:ℚ),(1205974340562835646449/2361183241434822606848:ℚ)⟩ thresholdNode350 thresholdNode351
def thresholdNode353 : BoxExpr 1 := .add ⟨(-1365944505170044878063/4722366482869645213696:ℚ),(-682972252585022439029/2361183241434822606848:ℚ)⟩ thresholdNode346 thresholdNode352
def thresholdNode354 : BoxExpr 1 := .add ⟨(-10277704381480072606269/4722366482869645213696:ℚ),(-10277704381480072606243/4722366482869645213696:ℚ)⟩ thresholdNode342 thresholdNode353
def thresholdNode355 : BoxExpr 1 := .mul ⟨(1841722928319161633341/4722366482869645213696:ℚ),(920861464159580816671/2361183241434822606848:ℚ)⟩ thresholdNode343 thresholdNode32
def thresholdNode356 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode313 thresholdNode66
def thresholdNode357 : BoxExpr 1 := .add ⟨(1841722928319161633341/4722366482869645213696:ℚ),(920861464159580816671/2361183241434822606848:ℚ)⟩ thresholdNode355 thresholdNode356
def thresholdNode358 : BoxExpr 1 := .mul ⟨(796899343984252629811/2361183241434822606848:ℚ),(1593798687968505259623/4722366482869645213696:ℚ)⟩ thresholdNode343 thresholdNode313
def thresholdNode359 : BoxExpr 1 := .mul ⟨(796899343984252629811/2361183241434822606848:ℚ),(1593798687968505259623/4722366482869645213696:ℚ)⟩ thresholdNode313 thresholdNode343
def thresholdNode360 : BoxExpr 1 := .add ⟨(796899343984252629811/1180591620717411303424:ℚ),(1593798687968505259623/2361183241434822606848:ℚ)⟩ thresholdNode358 thresholdNode359
def thresholdNode361 : BoxExpr 1 := .mul ⟨(517984573589764209377/1180591620717411303424:ℚ),(2071938294359056837511/4722366482869645213696:ℚ)⟩ thresholdNode360 thresholdNode35
def thresholdNode362 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode315 thresholdNode66
def thresholdNode363 : BoxExpr 1 := .add ⟨(517984573589764209377/1180591620717411303424:ℚ),(2071938294359056837511/4722366482869645213696:ℚ)⟩ thresholdNode361 thresholdNode362
def thresholdNode364 : BoxExpr 1 := .add ⟨(3913661222678218470849/4722366482869645213696:ℚ),(3913661222678218470853/4722366482869645213696:ℚ)⟩ thresholdNode357 thresholdNode363
def thresholdNode365 : BoxExpr 1 := .add ⟨(-1591010789700463533855/1180591620717411303424:ℚ),(-3182021579400927067695/2361183241434822606848:ℚ)⟩ thresholdNode354 thresholdNode364
def thresholdNode366 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66 thresholdNode1
def thresholdNode367 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66 thresholdNode66
def thresholdNode368 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode366 thresholdNode367
def thresholdNode369 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode66
def thresholdNode370 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode367 thresholdNode369
def thresholdNode371 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode368 thresholdNode370
def thresholdNode372 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode371 thresholdNode66
def thresholdNode373 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66
def thresholdNode374 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66 thresholdNode373
def thresholdNode375 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode374 thresholdNode268
def thresholdNode376 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode374 thresholdNode374
def thresholdNode377 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode375 thresholdNode376
def thresholdNode378 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode268 thresholdNode374
def thresholdNode379 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode376 thresholdNode378
def thresholdNode380 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode377 thresholdNode379
def thresholdNode381 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode380 thresholdNode9
def thresholdNode382 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode375 thresholdNode378
def thresholdNode383 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode382 thresholdNode66
def thresholdNode384 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode381 thresholdNode383
def thresholdNode385 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode269 thresholdNode66
def thresholdNode386 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode383 thresholdNode385
def thresholdNode387 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode384 thresholdNode386
def thresholdNode388 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode372 thresholdNode387
def thresholdNode389 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode388 thresholdNode276
def thresholdNode390 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode366 thresholdNode369
def thresholdNode391 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode390 thresholdNode66
def thresholdNode392 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode382 thresholdNode9
def thresholdNode393 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode392 thresholdNode385
def thresholdNode394 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode391 thresholdNode393
def thresholdNode395 : BoxExpr 1 := .mul ⟨(2243124079363081476505/4722366482869645213696:ℚ),(826414134502187912397/1180591620717411303424:ℚ)⟩ thresholdNode12 thresholdNode272
def thresholdNode396 : BoxExpr 1 := .mul ⟨(2243124079363081476505/4722366482869645213696:ℚ),(826414134502187912397/1180591620717411303424:ℚ)⟩ thresholdNode272 thresholdNode12
def thresholdNode397 : BoxExpr 1 := .add ⟨(2243124079363081476505/2361183241434822606848:ℚ),(826414134502187912397/590295810358705651712:ℚ)⟩ thresholdNode395 thresholdNode396
def thresholdNode398 : BoxExpr 1 := .neg ⟨(-826414134502187912397/590295810358705651712:ℚ),(-2243124079363081476505/2361183241434822606848:ℚ)⟩ thresholdNode397
def thresholdNode399 : BoxExpr 1 := .add ⟨(-826414134502187912397/590295810358705651712:ℚ),(-2243124079363081476505/2361183241434822606848:ℚ)⟩ thresholdNode66 thresholdNode398
def thresholdNode400 : BoxExpr 1 := .mul ⟨(421555528134539949789/295147905179352825856:ℚ),(2077807712657270368091/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode276
def thresholdNode401 : BoxExpr 1 := .inv ⟨(2683206085755958506007/4722366482869645213696:ℚ),(1653158933860940979567/2361183241434822606848:ℚ)⟩ thresholdNode400
def thresholdNode402 : BoxExpr 1 := .mul ⟨(-4628845014810634742789/4722366482869645213696:ℚ),(-2549045781468160580705/4722366482869645213696:ℚ)⟩ thresholdNode399 thresholdNode401
def thresholdNode403 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode394 thresholdNode402
def thresholdNode404 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode389 thresholdNode403
def thresholdNode405 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66 thresholdNode272
def thresholdNode406 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode12
def thresholdNode407 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode405 thresholdNode406
def thresholdNode408 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode272 thresholdNode66
def thresholdNode409 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode406 thresholdNode408
def thresholdNode410 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode407 thresholdNode409
def thresholdNode411 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode410
def thresholdNode412 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode66 thresholdNode411
def thresholdNode413 : BoxExpr 1 := .mul ⟨(-1653158933860940979567/1180591620717411303424:ℚ),(-2683206085755958506007/2361183241434822606848:ℚ)⟩ thresholdNode412 thresholdNode401
def thresholdNode414 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66 thresholdNode276
def thresholdNode415 : BoxExpr 1 := .mul ⟨(-4628845014810634742789/2361183241434822606848:ℚ),(-2549045781468160580705/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode402
def thresholdNode416 : BoxExpr 1 := .add ⟨(-4628845014810634742789/2361183241434822606848:ℚ),(-2549045781468160580705/2361183241434822606848:ℚ)⟩ thresholdNode414 thresholdNode415
def thresholdNode417 : BoxExpr 1 := .mul ⟨(9633627625054076235927/4722366482869645213696:ℚ),(1828441272586090756179/590295810358705651712:ℚ)⟩ thresholdNode400 thresholdNode400
def thresholdNode418 : BoxExpr 1 := .inv ⟨(762286760753776467101/2361183241434822606848:ℚ),(2314885530818453536129/4722366482869645213696:ℚ)⟩ thresholdNode417
def thresholdNode419 : BoxExpr 1 := .mul ⟨(-2269041673926781736665/2361183241434822606848:ℚ),(-822936491192303658015/2361183241434822606848:ℚ)⟩ thresholdNode416 thresholdNode418
def thresholdNode420 : BoxExpr 1 := .neg ⟨(822936491192303658015/2361183241434822606848:ℚ),(2269041673926781736665/2361183241434822606848:ℚ)⟩ thresholdNode419
def thresholdNode421 : BoxExpr 1 := .mul ⟨(-794164585874373607833/590295810358705651712:ℚ),(-390894833316344237557/1180591620717411303424:ℚ)⟩ thresholdNode399 thresholdNode420
def thresholdNode422 : BoxExpr 1 := .add ⟨(-3241488105609688195233/1180591620717411303424:ℚ),(-3464995752388646981121/2361183241434822606848:ℚ)⟩ thresholdNode413 thresholdNode421
def thresholdNode423 : BoxExpr 1 := .mul ⟨(-4212881053658271505141/590295810358705651712:ℚ),(-9006736708971429530373/2361183241434822606848:ℚ)⟩ thresholdNode271 thresholdNode422
def thresholdNode424 : BoxExpr 1 := .add ⟨(-4212881053658271505141/590295810358705651712:ℚ),(-9006736708971429530373/2361183241434822606848:ℚ)⟩ thresholdNode403 thresholdNode423
def thresholdNode425 : BoxExpr 1 := .add ⟨(-4212881053658271505141/590295810358705651712:ℚ),(-9006736708971429530373/2361183241434822606848:ℚ)⟩ thresholdNode404 thresholdNode424
def thresholdNode426 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode374 thresholdNode22
def thresholdNode427 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode373
def thresholdNode428 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode427 thresholdNode66
def thresholdNode429 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode426 thresholdNode428
def thresholdNode430 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode279 thresholdNode66
def thresholdNode431 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode428 thresholdNode430
def thresholdNode432 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode429 thresholdNode431
def thresholdNode433 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode374 thresholdNode279
def thresholdNode434 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode427 thresholdNode427
def thresholdNode435 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode433 thresholdNode434
def thresholdNode436 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode279 thresholdNode374
def thresholdNode437 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode434 thresholdNode436
def thresholdNode438 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode435 thresholdNode437
def thresholdNode439 : BoxExpr 1 := .mul ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode438 thresholdNode25
def thresholdNode440 : BoxExpr 1 := .mul ⟨(2148676749705688572231/4722366482869645213696:ℚ),(3211209208351358745315/4722366482869645213696:ℚ)⟩ thresholdNode427 thresholdNode279
def thresholdNode441 : BoxExpr 1 := .mul ⟨(2148676749705688572231/4722366482869645213696:ℚ),(3211209208351358745315/4722366482869645213696:ℚ)⟩ thresholdNode279 thresholdNode427
def thresholdNode442 : BoxExpr 1 := .add ⟨(2148676749705688572231/2361183241434822606848:ℚ),(3211209208351358745315/2361183241434822606848:ℚ)⟩ thresholdNode440 thresholdNode441
def thresholdNode443 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode442 thresholdNode66
def thresholdNode444 : BoxExpr 1 := .add ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode439 thresholdNode443
def thresholdNode445 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode281 thresholdNode66
def thresholdNode446 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode443 thresholdNode445
def thresholdNode447 : BoxExpr 1 := .add ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode444 thresholdNode446
def thresholdNode448 : BoxExpr 1 := .add ⟨(2125064917291340346163/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode432 thresholdNode447
def thresholdNode449 : BoxExpr 1 := .add ⟨(-14726459297341745674401/2361183241434822606848:ℚ),(-6881671791680089184209/2361183241434822606848:ℚ)⟩ thresholdNode425 thresholdNode448
def thresholdNode450 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode374 thresholdNode32
def thresholdNode451 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode450 thresholdNode428
def thresholdNode452 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode286 thresholdNode66
def thresholdNode453 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode428 thresholdNode452
def thresholdNode454 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode451 thresholdNode453
def thresholdNode455 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode374 thresholdNode286
def thresholdNode456 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode455 thresholdNode434
def thresholdNode457 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode286 thresholdNode374
def thresholdNode458 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode434 thresholdNode457
def thresholdNode459 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode456 thresholdNode458
def thresholdNode460 : BoxExpr 1 := .mul ⟨(1534769106932634694451/1180591620717411303424:ℚ),(3069538213865269388903/2361183241434822606848:ℚ)⟩ thresholdNode459 thresholdNode35
def thresholdNode461 : BoxExpr 1 := .mul ⟨(1062532458645670173081/4722366482869645213696:ℚ),(531266229322835086541/1180591620717411303424:ℚ)⟩ thresholdNode427 thresholdNode286
def thresholdNode462 : BoxExpr 1 := .mul ⟨(1062532458645670173081/4722366482869645213696:ℚ),(531266229322835086541/1180591620717411303424:ℚ)⟩ thresholdNode286 thresholdNode427
def thresholdNode463 : BoxExpr 1 := .add ⟨(1062532458645670173081/2361183241434822606848:ℚ),(531266229322835086541/590295810358705651712:ℚ)⟩ thresholdNode461 thresholdNode462
def thresholdNode464 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode463 thresholdNode66
def thresholdNode465 : BoxExpr 1 := .add ⟨(1534769106932634694451/1180591620717411303424:ℚ),(3069538213865269388903/2361183241434822606848:ℚ)⟩ thresholdNode460 thresholdNode464
def thresholdNode466 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode288 thresholdNode66
def thresholdNode467 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode464 thresholdNode466
def thresholdNode468 : BoxExpr 1 := .add ⟨(1534769106932634694451/1180591620717411303424:ℚ),(3069538213865269388903/2361183241434822606848:ℚ)⟩ thresholdNode465 thresholdNode467
def thresholdNode469 : BoxExpr 1 := .add ⟨(1534769106932634694451/1180591620717411303424:ℚ),(3069538213865269388903/2361183241434822606848:ℚ)⟩ thresholdNode454 thresholdNode468
def thresholdNode470 : BoxExpr 1 := .add ⟨(-11656921083476476285499/2361183241434822606848:ℚ),(-1906066788907409897653/1180591620717411303424:ℚ)⟩ thresholdNode449 thresholdNode469
def thresholdCell1Out0 : TaylorCertificate1 :=
  { center := (47/80:ℚ), radius := (9/80:ℚ)
    whole := thresholdNode291, centerValue := thresholdNode318, gradient := thresholdNode365, hessian := thresholdNode470 }
theorem thresholdCell1Out0_check : thresholdCell1Out0.check = true := by decide +kernel
theorem thresholdCell1Out0_lower_pos : 0 < thresholdCell1Out0.lower := by decide +kernel
theorem thresholdCell1Out0_positive (x : ℝ) (hx : (19/40:ℝ) ≤ x ∧ x ≤ (7/10:ℝ)) :
    0 < thresholdNode291.eval (fun _ => x) := by
  apply thresholdCell1Out0.positive_sound thresholdCell1Out0_check thresholdCell1Out0_lower_pos x
  norm_num [thresholdCell1Out0]
  exact hx
def thresholdNode471 : BoxExpr 1 := .mul ⟨(10998658803746209005681/4722366482869645213696:ℚ),(14041368394478659831989/2361183241434822606848:ℚ)⟩ thresholdNode291 thresholdNode291
def thresholdNode472 : BoxExpr 1 := .mul ⟨(3465820991300221562249/1180591620717411303424:ℚ),(21049765726573404488391/4722366482869645213696:ℚ)⟩ thresholdNode275 thresholdNode220
def thresholdNode473 : BoxExpr 1 := .neg ⟨(-21049765726573404488391/4722366482869645213696:ℚ),(-3465820991300221562249/1180591620717411303424:ℚ)⟩ thresholdNode472
def thresholdNode474 : BoxExpr 1 := .add ⟨(-5025553461413597741355/2361183241434822606848:ℚ),(7109726411878216707491/2361183241434822606848:ℚ)⟩ thresholdNode471 thresholdNode473
def thresholdNode475 : BoxExpr 1 := .mul ⟨(18890338815199175033917/4722366482869645213696:ℚ),(9445169407599587517007/2361183241434822606848:ℚ)⟩ thresholdNode318 thresholdNode318
def thresholdNode476 : BoxExpr 1 := .mul ⟨(4450139636807361693441/1180591620717411303424:ℚ),(17800558547229446773777/4722366482869645213696:ℚ)⟩ thresholdNode302 thresholdNode220
def thresholdNode477 : BoxExpr 1 := .neg ⟨(-17800558547229446773777/4722366482869645213696:ℚ),(-4450139636807361693441/1180591620717411303424:ℚ)⟩ thresholdNode476
def thresholdNode478 : BoxExpr 1 := .add ⟨(272445066992432065035/1180591620717411303424:ℚ),(544890133984864130125/2361183241434822606848:ℚ)⟩ thresholdNode475 thresholdNode477
def thresholdNode479 : BoxExpr 1 := .mul ⟨(-12728380397146086955625/4722366482869645213696:ℚ),(-3182095099286521738883/1180591620717411303424:ℚ)⟩ thresholdNode365 thresholdNode318
def thresholdNode480 : BoxExpr 1 := .mul ⟨(-12728380397146086955625/4722366482869645213696:ℚ),(-3182095099286521738883/1180591620717411303424:ℚ)⟩ thresholdNode318 thresholdNode365
def thresholdNode481 : BoxExpr 1 := .add ⟨(-12728380397146086955625/2361183241434822606848:ℚ),(-3182095099286521738883/590295810358705651712:ℚ)⟩ thresholdNode479 thresholdNode480
def thresholdNode482 : BoxExpr 1 := .mul ⟨(-1996244933714588399827/295147905179352825856:ℚ),(-15969959469716707198609/2361183241434822606848:ℚ)⟩ thresholdNode337 thresholdNode220
def thresholdNode483 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode302 thresholdNode66
def thresholdNode484 : BoxExpr 1 := .add ⟨(-1996244933714588399827/295147905179352825856:ℚ),(-15969959469716707198609/2361183241434822606848:ℚ)⟩ thresholdNode482 thresholdNode483
def thresholdNode485 : BoxExpr 1 := .neg ⟨(15969959469716707198609/2361183241434822606848:ℚ),(1996244933714588399827/295147905179352825856:ℚ)⟩ thresholdNode484
def thresholdNode486 : BoxExpr 1 := .add ⟨(405197384071327530373/295147905179352825856:ℚ),(810394768142655060771/590295810358705651712:ℚ)⟩ thresholdNode481 thresholdNode485
def thresholdNode487 : BoxExpr 1 := .mul ⟨(-28426522025425554887803/2361183241434822606848:ℚ),(-11635582414727486161841/4722366482869645213696:ℚ)⟩ thresholdNode470 thresholdNode291
def thresholdNode488 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode394 thresholdNode276
def thresholdNode489 : BoxExpr 1 := .mul ⟨(-12031988289248023418673/4722366482869645213696:ℚ),(-6625862152059263205453/4722366482869645213696:ℚ)⟩ thresholdNode271 thresholdNode402
def thresholdNode490 : BoxExpr 1 := .add ⟨(-12031988289248023418673/4722366482869645213696:ℚ),(-6625862152059263205453/4722366482869645213696:ℚ)⟩ thresholdNode488 thresholdNode489
def thresholdNode491 : BoxExpr 1 := .mul ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode427 thresholdNode22
def thresholdNode492 : BoxExpr 1 := .add ⟨(-3777893186295716170957/4722366482869645213696:ℚ),(-944473296573929042739/1180591620717411303424:ℚ)⟩ thresholdNode491 thresholdNode430
def thresholdNode493 : BoxExpr 1 := .mul ⟨(1933809074735119715007/4722366482869645213696:ℚ),(2890088287516222870785/4722366482869645213696:ℚ)⟩ thresholdNode442 thresholdNode25
def thresholdNode494 : BoxExpr 1 := .add ⟨(1933809074735119715007/4722366482869645213696:ℚ),(2890088287516222870785/4722366482869645213696:ℚ)⟩ thresholdNode493 thresholdNode445
def thresholdNode495 : BoxExpr 1 := .add ⟨(-922042055780298227975/2361183241434822606848:ℚ),(-887804898779493300171/4722366482869645213696:ℚ)⟩ thresholdNode492 thresholdNode494
def thresholdNode496 : BoxExpr 1 := .add ⟨(-13876072400808619874623/4722366482869645213696:ℚ),(-939208381354844563203/590295810358705651712:ℚ)⟩ thresholdNode490 thresholdNode495
def thresholdNode497 : BoxExpr 1 := .mul ⟨(1841722928319161633341/4722366482869645213696:ℚ),(920861464159580816671/2361183241434822606848:ℚ)⟩ thresholdNode427 thresholdNode32
def thresholdNode498 : BoxExpr 1 := .add ⟨(1841722928319161633341/4722366482869645213696:ℚ),(920861464159580816671/2361183241434822606848:ℚ)⟩ thresholdNode497 thresholdNode452
def thresholdNode499 : BoxExpr 1 := .mul ⟨(1381292196239371225005/4722366482869645213696:ℚ),(1381292196239371225007/2361183241434822606848:ℚ)⟩ thresholdNode463 thresholdNode35
def thresholdNode500 : BoxExpr 1 := .add ⟨(1381292196239371225005/4722366482869645213696:ℚ),(1381292196239371225007/2361183241434822606848:ℚ)⟩ thresholdNode499 thresholdNode466
def thresholdNode501 : BoxExpr 1 := .add ⟨(1611507562279266429173/2361183241434822606848:ℚ),(1151076830199476020839/1180591620717411303424:ℚ)⟩ thresholdNode498 thresholdNode500
def thresholdNode502 : BoxExpr 1 := .add ⟨(-10653057276250087016277/4722366482869645213696:ℚ),(-727339932510213105567/1180591620717411303424:ℚ)⟩ thresholdNode496 thresholdNode501
def thresholdNode503 : BoxExpr 1 := .mul ⟨(1792400922183368317715/4722366482869645213696:ℚ),(12015970143649437852561/2361183241434822606848:ℚ)⟩ thresholdNode502 thresholdNode502
def thresholdNode504 : BoxExpr 1 := .add ⟨(-55060643128667741457891/4722366482869645213696:ℚ),(12396357872571389543281/4722366482869645213696:ℚ)⟩ thresholdNode487 thresholdNode503
def thresholdNode505 : BoxExpr 1 := .mul ⟨(-28426522025425554887803/2361183241434822606848:ℚ),(-11635582414727486161841/4722366482869645213696:ℚ)⟩ thresholdNode291 thresholdNode470
def thresholdNode506 : BoxExpr 1 := .add ⟨(-55060643128667741457891/4722366482869645213696:ℚ),(12396357872571389543281/4722366482869645213696:ℚ)⟩ thresholdNode503 thresholdNode505
def thresholdNode507 : BoxExpr 1 := .add ⟨(-55060643128667741457891/2361183241434822606848:ℚ),(12396357872571389543281/2361183241434822606848:ℚ)⟩ thresholdNode504 thresholdNode506
def thresholdNode508 : BoxExpr 1 := .mul ⟨(-27182909735688012252957/2361183241434822606848:ℚ),(-6795727433922003063239/590295810358705651712:ℚ)⟩ thresholdNode412 thresholdNode220
def thresholdNode509 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode399 thresholdNode66
def thresholdNode510 : BoxExpr 1 := .add ⟨(-27182909735688012252957/2361183241434822606848:ℚ),(-6795727433922003063239/590295810358705651712:ℚ)⟩ thresholdNode508 thresholdNode509
def thresholdNode511 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode275 thresholdNode66
def thresholdNode512 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode509 thresholdNode511
def thresholdNode513 : BoxExpr 1 := .add ⟨(-27182909735688012252957/2361183241434822606848:ℚ),(-6795727433922003063239/590295810358705651712:ℚ)⟩ thresholdNode510 thresholdNode512
def thresholdNode514 : BoxExpr 1 := .neg ⟨(6795727433922003063239/590295810358705651712:ℚ),(27182909735688012252957/2361183241434822606848:ℚ)⟩ thresholdNode513
def thresholdNode515 : BoxExpr 1 := .add ⟨(-27877733392979729204935/2361183241434822606848:ℚ),(19789633804129700898119/1180591620717411303424:ℚ)⟩ thresholdNode507 thresholdNode514
def thresholdCell1Out1 : TaylorCertificate1 :=
  { center := (47/80:ℚ), radius := (9/80:ℚ)
    whole := thresholdNode474, centerValue := thresholdNode478, gradient := thresholdNode486, hessian := thresholdNode515 }
theorem thresholdCell1Out1_check : thresholdCell1Out1.check = true := by decide +kernel
theorem thresholdCell1Out1_lower_pos : 0 < thresholdCell1Out1.lower := by decide +kernel
theorem thresholdCell1Out1_positive (x : ℝ) (hx : (19/40:ℝ) ≤ x ∧ x ≤ (7/10:ℝ)) :
    0 < thresholdNode474.eval (fun _ => x) := by
  apply thresholdCell1Out1.positive_sound thresholdCell1Out1_check thresholdCell1Out1_lower_pos x
  norm_num [thresholdCell1Out1]
  exact hx
theorem thresholdCell1_public (x : ℝ)
    (hx : (19/40:ℝ) ≤ x ∧ x ≤ (7/10:ℝ)) : qc x < fA (43/20) x := by
  have hf := thresholdCell1Out0_positive x hx
  have hg := thresholdCell1Out1_positive x hx
  have hfa : thresholdNode291.eval (fun _ => x) = thresholdFA 3 x := by
    norm_num [thresholdNode0, thresholdNode1, thresholdNode265, thresholdNode3, thresholdNode266, thresholdNode5, thresholdNode267, thresholdNode268, thresholdNode269, thresholdNode9, thresholdNode270, thresholdNode271, thresholdNode12, thresholdNode272, thresholdNode273, thresholdNode274, thresholdNode275, thresholdNode276, thresholdNode277, thresholdNode19, thresholdNode278, thresholdNode279, thresholdNode22, thresholdNode280, thresholdNode281, thresholdNode25, thresholdNode282, thresholdNode283, thresholdNode284, thresholdNode29, thresholdNode285, thresholdNode286, thresholdNode32, thresholdNode287, thresholdNode288, thresholdNode35, thresholdNode289, thresholdNode290, thresholdNode291, BoxExpr.eval, thresholdFA, ftilde, pow_two, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  have hgap : thresholdNode474.eval (fun _ => x) =
      (thresholdNode291.eval (fun _ => x))^2 - (1-x^2)*(thresholdCapacity 4 x+1/4) := by
    norm_num [thresholdNode471, thresholdNode12, thresholdNode272, thresholdNode273, thresholdNode274, thresholdNode275, thresholdNode220, thresholdNode472, thresholdNode473, thresholdNode474, BoxExpr.eval, thresholdCapacity, Da, D5, beta5, eta5, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  rw [hfa] at hf
  rw [hgap, hfa] at hg
  refine threshold_positive_to_public 3 4 x ?_ ?_ ?_ hf hg
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdFADomain] <;> constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdCapacityDomain] <;> linarith [hx.1,hx.2]
theorem threshold_fgt_low_domain (x : ℝ)
    (hx : x ∈ Set.Icc (1/4:ℝ) (7/10:ℝ)) : qc x < fA (43/20) x := by
  have hlo := hx.1
  by_cases h0 : x ≤ (19/40:ℝ)
  · exact thresholdCell0_public x ⟨hlo, h0⟩
  have hlo : (19/40:ℝ) ≤ x := (lt_of_not_ge h0).le
  exact thresholdCell1_public x ⟨hlo,hx.2⟩
#print axioms threshold_fgt_low_domain
end GaussLocalMaxColoring.Certificate.ThresholdBranch3

open GaussLocalMaxColoring.Main

theorem solution (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (1/4:ℝ) (7/10:ℝ)) : qc ρ < fA (43/20) ρ  := by exact GaussLocalMaxColoring.Certificate.ThresholdBranch3.threshold_fgt_low_domain ρ hρ

#print axioms solution
