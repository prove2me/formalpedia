-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_61_branch_0
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T09:50:33.690558+00:00
-- url     : https://prove2.me/submissions/10bdeac6-0472-4892-9b52-d0d8ea18c0a7

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
namespace GaussLocalMaxColoring.Certificate.ThresholdBranch0
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
def thresholdNode14 : BoxExpr 1 := .mul ⟨(343201673491366207815/2361183241434822606848:ℚ),(1/4:ℚ)⟩ thresholdNode13 thresholdNode13
def thresholdNode15 : BoxExpr 1 := .neg ⟨(-1/4:ℚ),(-343201673491366207815/2361183241434822606848:ℚ)⟩ thresholdNode14
def thresholdNode16 : BoxExpr 1 := .add ⟨(3/4:ℚ),(2017981567943456399033/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode15
def thresholdNode17 : BoxExpr 1 := .sqrt ⟨(2044844670072641933001/2361183241434822606848:ℚ),(272855967606779907901/295147905179352825856:ℚ)⟩ thresholdNode16
def thresholdNode18 : BoxExpr 1 := .mul ⟨(166102093536041306517/73786976294838206464:ℚ),(2836992637594733414411/1180591620717411303424:ℚ)⟩ thresholdNode11 thresholdNode17
def thresholdNode19 : BoxExpr 1 := .lit (-1/40:ℚ)
def thresholdNode20 : BoxExpr 1 := .neg ⟨(1800402221594052237721/4722366482869645213696:ℚ),(1/2:ℚ)⟩ thresholdNode13
def thresholdNode21 : BoxExpr 1 := .add ⟨(841171529761155553689/2361183241434822606848:ℚ),(1121562039681540738253/2361183241434822606848:ℚ)⟩ thresholdNode19 thresholdNode20
def thresholdNode22 : BoxExpr 1 := .lit (357/500:ℚ)
def thresholdNode23 : BoxExpr 1 := .mul ⟨(1201192944498930130667/4722366482869645213696:ℚ),(800795296332620087113/2361183241434822606848:ℚ)⟩ thresholdNode21 thresholdNode22
def thresholdNode24 : BoxExpr 1 := .neg ⟨(-800795296332620087113/2361183241434822606848:ℚ),(-1201192944498930130667/4722366482869645213696:ℚ)⟩ thresholdNode23
def thresholdNode25 : BoxExpr 1 := .add ⟨(4514471696820701721431/2361183241434822606848:ℚ),(10146777605880003526977/4722366482869645213696:ℚ)⟩ thresholdNode18 thresholdNode24
def thresholdNode26 : BoxExpr 1 := .mul ⟨(299667357477411666001/2361183241434822606848:ℚ),(1065483937697463701341/4722366482869645213696:ℚ)⟩ thresholdNode21 thresholdNode21
def thresholdNode27 : BoxExpr 1 := .lit (413/500:ℚ)
def thresholdNode28 : BoxExpr 1 := .mul ⟨(495050474552684072233/4722366482869645213696:ℚ),(220022433134526254327/1180591620717411303424:ℚ)⟩ thresholdNode26 thresholdNode27
def thresholdNode29 : BoxExpr 1 := .add ⟨(9523993868194087515095/4722366482869645213696:ℚ),(11026867338418108544285/4722366482869645213696:ℚ)⟩ thresholdNode25 thresholdNode28
def thresholdNode30 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode31 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode30 thresholdNode3
def thresholdNode32 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode33 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode32
def thresholdNode34 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode33 thresholdNode33
def thresholdNode35 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode34 thresholdNode9
def thresholdNode36 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode31 thresholdNode35
def thresholdNode37 : BoxExpr 1 := .var 0
def thresholdNode38 : BoxExpr 1 := .mul ⟨(916849297323548989193/4722366482869645213696:ℚ),(916849297323548989195/4722366482869645213696:ℚ)⟩ thresholdNode37 thresholdNode37
def thresholdNode39 : BoxExpr 1 := .neg ⟨(-916849297323548989195/4722366482869645213696:ℚ),(-916849297323548989193/4722366482869645213696:ℚ)⟩ thresholdNode38
def thresholdNode40 : BoxExpr 1 := .add ⟨(3805517185546096224501/4722366482869645213696:ℚ),(3805517185546096224503/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode39
def thresholdNode41 : BoxExpr 1 := .sqrt ⟨(1059806786842751277661/1180591620717411303424:ℚ),(2119613573685502555323/2361183241434822606848:ℚ)⟩ thresholdNode40
def thresholdNode42 : BoxExpr 1 := .mul ⟨(2754808771379705533587/1180591620717411303424:ℚ),(5509617542759411067181/2361183241434822606848:ℚ)⟩ thresholdNode36 thresholdNode41
def thresholdNode43 : BoxExpr 1 := .neg ⟨(520198182878609355571/1180591620717411303424:ℚ),(2080792731514437422285/4722366482869645213696:ℚ)⟩ thresholdNode37
def thresholdNode44 : BoxExpr 1 := .add ⟨(1962733569442696291941/4722366482869645213696:ℚ),(1962733569442696291943/4722366482869645213696:ℚ)⟩ thresholdNode19 thresholdNode43
def thresholdNode45 : BoxExpr 1 := .mul ⟨(1401391768582085152445/4722366482869645213696:ℚ),(21896746384095080507/73786976294838206464:ℚ)⟩ thresholdNode44 thresholdNode22
def thresholdNode46 : BoxExpr 1 := .neg ⟨(-21896746384095080507/73786976294838206464:ℚ),(-1401391768582085152445/4722366482869645213696:ℚ)⟩ thresholdNode45
def thresholdNode47 : BoxExpr 1 := .add ⟨(2404460829234184245475/1180591620717411303424:ℚ),(9617843316936736981917/4722366482869645213696:ℚ)⟩ thresholdNode42 thresholdNode46
def thresholdNode48 : BoxExpr 1 := .mul ⟨(815761139799620646337/4722366482869645213696:ℚ),(203940284949905161585/1180591620717411303424:ℚ)⟩ thresholdNode44 thresholdNode44
def thresholdNode49 : BoxExpr 1 := .mul ⟨(336909350737243326937/2361183241434822606848:ℚ),(673818701474486653877/4722366482869645213696:ℚ)⟩ thresholdNode48 thresholdNode27
def thresholdNode50 : BoxExpr 1 := .add ⟨(5145831009205611817887/2361183241434822606848:ℚ),(5145831009205611817897/2361183241434822606848:ℚ)⟩ thresholdNode47 thresholdNode49
def thresholdNode51 : BoxExpr 1 := .lit (0/1:ℚ)
def thresholdNode52 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1
def thresholdNode53 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode51
def thresholdNode54 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode52 thresholdNode53
def thresholdNode55 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode54 thresholdNode51
def thresholdNode56 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51
def thresholdNode57 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode56
def thresholdNode58 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode57 thresholdNode33
def thresholdNode59 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode33 thresholdNode57
def thresholdNode60 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode58 thresholdNode59
def thresholdNode61 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode60 thresholdNode9
def thresholdNode62 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode34 thresholdNode51
def thresholdNode63 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode61 thresholdNode62
def thresholdNode64 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode55 thresholdNode63
def thresholdNode65 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode64 thresholdNode41
def thresholdNode66 : BoxExpr 1 := .mul ⟨(-2080792731514437422285/4722366482869645213696:ℚ),(-520198182878609355571/1180591620717411303424:ℚ)⟩ thresholdNode12 thresholdNode37
def thresholdNode67 : BoxExpr 1 := .mul ⟨(-2080792731514437422285/4722366482869645213696:ℚ),(-520198182878609355571/1180591620717411303424:ℚ)⟩ thresholdNode37 thresholdNode12
def thresholdNode68 : BoxExpr 1 := .add ⟨(-2080792731514437422285/2361183241434822606848:ℚ),(-520198182878609355571/590295810358705651712:ℚ)⟩ thresholdNode66 thresholdNode67
def thresholdNode69 : BoxExpr 1 := .neg ⟨(520198182878609355571/590295810358705651712:ℚ),(2080792731514437422285/2361183241434822606848:ℚ)⟩ thresholdNode68
def thresholdNode70 : BoxExpr 1 := .add ⟨(520198182878609355571/590295810358705651712:ℚ),(2080792731514437422285/2361183241434822606848:ℚ)⟩ thresholdNode51 thresholdNode69
def thresholdNode71 : BoxExpr 1 := .mul ⟨(1059806786842751277661/590295810358705651712:ℚ),(2119613573685502555323/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode41
def thresholdNode72 : BoxExpr 1 := .inv ⟨(2630284297499914706491/4722366482869645213696:ℚ),(2630284297499914706493/4722366482869645213696:ℚ)⟩ thresholdNode71
def thresholdNode73 : BoxExpr 1 := .mul ⟨(1158969018585899917547/2361183241434822606848:ℚ),(1158969018585899917549/2361183241434822606848:ℚ)⟩ thresholdNode70 thresholdNode72
def thresholdNode74 : BoxExpr 1 := .mul ⟨(6025132236922517901349/4722366482869645213696:ℚ),(6025132236922517901365/4722366482869645213696:ℚ)⟩ thresholdNode36 thresholdNode73
def thresholdNode75 : BoxExpr 1 := .add ⟨(6025132236922517901349/4722366482869645213696:ℚ),(6025132236922517901365/4722366482869645213696:ℚ)⟩ thresholdNode65 thresholdNode74
def thresholdNode76 : BoxExpr 1 := .neg ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode12
def thresholdNode77 : BoxExpr 1 := .add ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode51 thresholdNode76
def thresholdNode78 : BoxExpr 1 := .mul ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode77 thresholdNode22
def thresholdNode79 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode44 thresholdNode51
def thresholdNode80 : BoxExpr 1 := .add ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode78 thresholdNode79
def thresholdNode81 : BoxExpr 1 := .neg ⟨(1685884834384463341289/2361183241434822606848:ℚ),(3371769668768926682579/4722366482869645213696:ℚ)⟩ thresholdNode80
def thresholdNode82 : BoxExpr 1 := .add ⟨(9396901905691444583927/4722366482869645213696:ℚ),(1174612738211430572993/590295810358705651712:ℚ)⟩ thresholdNode75 thresholdNode81
def thresholdNode83 : BoxExpr 1 := .mul ⟨(-1962733569442696291943/4722366482869645213696:ℚ),(-1962733569442696291941/4722366482869645213696:ℚ)⟩ thresholdNode77 thresholdNode44
def thresholdNode84 : BoxExpr 1 := .mul ⟨(-1962733569442696291943/4722366482869645213696:ℚ),(-1962733569442696291941/4722366482869645213696:ℚ)⟩ thresholdNode44 thresholdNode77
def thresholdNode85 : BoxExpr 1 := .add ⟨(-1962733569442696291943/2361183241434822606848:ℚ),(-1962733569442696291941/2361183241434822606848:ℚ)⟩ thresholdNode83 thresholdNode84
def thresholdNode86 : BoxExpr 1 := .mul ⟨(-1621217928359667137145/2361183241434822606848:ℚ),(-3242435856719334274285/4722366482869645213696:ℚ)⟩ thresholdNode85 thresholdNode27
def thresholdNode87 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode48 thresholdNode51
def thresholdNode88 : BoxExpr 1 := .add ⟨(-1621217928359667137145/2361183241434822606848:ℚ),(-3242435856719334274285/4722366482869645213696:ℚ)⟩ thresholdNode86 thresholdNode87
def thresholdNode89 : BoxExpr 1 := .add ⟨(6154466048972110309637/4722366482869645213696:ℚ),(6154466048972110309659/4722366482869645213696:ℚ)⟩ thresholdNode82 thresholdNode88
def thresholdNode90 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1
def thresholdNode91 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode51
def thresholdNode92 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode90 thresholdNode91
def thresholdNode93 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode51
def thresholdNode94 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode91 thresholdNode93
def thresholdNode95 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode92 thresholdNode94
def thresholdNode96 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode95 thresholdNode51
def thresholdNode97 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51
def thresholdNode98 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode97
def thresholdNode99 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode98 thresholdNode7
def thresholdNode100 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode98 thresholdNode98
def thresholdNode101 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode99 thresholdNode100
def thresholdNode102 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode7 thresholdNode98
def thresholdNode103 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode100 thresholdNode102
def thresholdNode104 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode101 thresholdNode103
def thresholdNode105 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode104 thresholdNode9
def thresholdNode106 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode99 thresholdNode102
def thresholdNode107 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode106 thresholdNode51
def thresholdNode108 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode105 thresholdNode107
def thresholdNode109 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode8 thresholdNode51
def thresholdNode110 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode107 thresholdNode109
def thresholdNode111 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode108 thresholdNode110
def thresholdNode112 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode96 thresholdNode111
def thresholdNode113 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode112 thresholdNode17
def thresholdNode114 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode90 thresholdNode93
def thresholdNode115 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode114 thresholdNode51
def thresholdNode116 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode106 thresholdNode9
def thresholdNode117 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode116 thresholdNode109
def thresholdNode118 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode115 thresholdNode117
def thresholdNode119 : BoxExpr 1 := .mul ⟨(-1/2:ℚ),(-1800402221594052237721/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode13
def thresholdNode120 : BoxExpr 1 := .mul ⟨(-1/2:ℚ),(-1800402221594052237721/4722366482869645213696:ℚ)⟩ thresholdNode13 thresholdNode12
def thresholdNode121 : BoxExpr 1 := .add ⟨(-1/1:ℚ),(-1800402221594052237721/2361183241434822606848:ℚ)⟩ thresholdNode119 thresholdNode120
def thresholdNode122 : BoxExpr 1 := .neg ⟨(1800402221594052237721/2361183241434822606848:ℚ),(1/1:ℚ)⟩ thresholdNode121
def thresholdNode123 : BoxExpr 1 := .add ⟨(1800402221594052237721/2361183241434822606848:ℚ),(1/1:ℚ)⟩ thresholdNode51 thresholdNode122
def thresholdNode124 : BoxExpr 1 := .mul ⟨(2044844670072641933001/1180591620717411303424:ℚ),(272855967606779907901/147573952589676412928:ℚ)⟩ thresholdNode5 thresholdNode17
def thresholdNode125 : BoxExpr 1 := .inv ⟨(79815265445559276501/147573952589676412928:ℚ),(2726459560096855910669/4722366482869645213696:ℚ)⟩ thresholdNode124
def thresholdNode126 : BoxExpr 1 := .mul ⟨(1947492476871646346623/4722366482869645213696:ℚ),(2726459560096855910669/4722366482869645213696:ℚ)⟩ thresholdNode123 thresholdNode125
def thresholdNode127 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode118 thresholdNode126
def thresholdNode128 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode113 thresholdNode127
def thresholdNode129 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode13
def thresholdNode130 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode12
def thresholdNode131 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode129 thresholdNode130
def thresholdNode132 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode13 thresholdNode51
def thresholdNode133 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode130 thresholdNode132
def thresholdNode134 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode131 thresholdNode133
def thresholdNode135 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode134
def thresholdNode136 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode135
def thresholdNode137 : BoxExpr 1 := .mul ⟨(-2726459560096855910669/2361183241434822606848:ℚ),(-79815265445559276501/73786976294838206464:ℚ)⟩ thresholdNode136 thresholdNode125
def thresholdNode138 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode17
def thresholdNode139 : BoxExpr 1 := .mul ⟨(1947492476871646346623/2361183241434822606848:ℚ),(2726459560096855910669/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode126
def thresholdNode140 : BoxExpr 1 := .add ⟨(1947492476871646346623/2361183241434822606848:ℚ),(2726459560096855910669/2361183241434822606848:ℚ)⟩ thresholdNode138 thresholdNode139
def thresholdNode141 : BoxExpr 1 := .mul ⟨(7083549724304467820541/2361183241434822606848:ℚ),(16143852543547651192265/4722366482869645213696:ℚ)⟩ thresholdNode124 thresholdNode124
def thresholdNode142 : BoxExpr 1 := .inv ⟨(1381376913495394184727/4722366482869645213696:ℚ),(1574122160956548404567/4722366482869645213696:ℚ)⟩ thresholdNode141
def thresholdNode143 : BoxExpr 1 := .mul ⟨(569676486675740967063/2361183241434822606848:ℚ),(908819853365618636891/2361183241434822606848:ℚ)⟩ thresholdNode140 thresholdNode142
def thresholdNode144 : BoxExpr 1 := .neg ⟨(-908819853365618636891/2361183241434822606848:ℚ),(-569676486675740967063/2361183241434822606848:ℚ)⟩ thresholdNode143
def thresholdNode145 : BoxExpr 1 := .mul ⟨(-908819853365618636891/2361183241434822606848:ℚ),(-434378321090252487385/2361183241434822606848:ℚ)⟩ thresholdNode123 thresholdNode144
def thresholdNode146 : BoxExpr 1 := .add ⟨(-454409926682809318445/295147905179352825856:ℚ),(-2988466815348149335417/2361183241434822606848:ℚ)⟩ thresholdNode137 thresholdNode145
def thresholdNode147 : BoxExpr 1 := .mul ⟨(-18898727086767366430407/4722366482869645213696:ℚ),(-7768071216475211975013/2361183241434822606848:ℚ)⟩ thresholdNode11 thresholdNode146
def thresholdNode148 : BoxExpr 1 := .add ⟨(-18898727086767366430407/4722366482869645213696:ℚ),(-7768071216475211975013/2361183241434822606848:ℚ)⟩ thresholdNode127 thresholdNode147
def thresholdNode149 : BoxExpr 1 := .add ⟨(-18898727086767366430407/4722366482869645213696:ℚ),(-7768071216475211975013/2361183241434822606848:ℚ)⟩ thresholdNode128 thresholdNode148
def thresholdNode150 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode98 thresholdNode22
def thresholdNode151 : BoxExpr 1 := .neg ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode12
def thresholdNode152 : BoxExpr 1 := .add ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode51 thresholdNode151
def thresholdNode153 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode152 thresholdNode51
def thresholdNode154 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode150 thresholdNode153
def thresholdNode155 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode21 thresholdNode51
def thresholdNode156 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode153 thresholdNode155
def thresholdNode157 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode154 thresholdNode156
def thresholdNode158 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode157
def thresholdNode159 : BoxExpr 1 := .add ⟨(-18898727086767366430407/4722366482869645213696:ℚ),(-7768071216475211975013/2361183241434822606848:ℚ)⟩ thresholdNode149 thresholdNode158
def thresholdNode160 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode98 thresholdNode21
def thresholdNode161 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode152 thresholdNode152
def thresholdNode162 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode160 thresholdNode161
def thresholdNode163 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode21 thresholdNode98
def thresholdNode164 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode161 thresholdNode163
def thresholdNode165 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode162 thresholdNode164
def thresholdNode166 : BoxExpr 1 := .mul ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode165 thresholdNode27
def thresholdNode167 : BoxExpr 1 := .mul ⟨(-1121562039681540738253/2361183241434822606848:ℚ),(-841171529761155553689/2361183241434822606848:ℚ)⟩ thresholdNode152 thresholdNode21
def thresholdNode168 : BoxExpr 1 := .mul ⟨(-1121562039681540738253/2361183241434822606848:ℚ),(-841171529761155553689/2361183241434822606848:ℚ)⟩ thresholdNode21 thresholdNode152
def thresholdNode169 : BoxExpr 1 := .add ⟨(-1121562039681540738253/1180591620717411303424:ℚ),(-841171529761155553689/1180591620717411303424:ℚ)⟩ thresholdNode167 thresholdNode168
def thresholdNode170 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode169 thresholdNode51
def thresholdNode171 : BoxExpr 1 := .add ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode166 thresholdNode170
def thresholdNode172 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode26 thresholdNode51
def thresholdNode173 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode170 thresholdNode172
def thresholdNode174 : BoxExpr 1 := .add ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode171 thresholdNode173
def thresholdNode175 : BoxExpr 1 := .add ⟨(-11097377657066712537383/4722366482869645213696:ℚ),(-966849125406221257125/590295810358705651712:ℚ)⟩ thresholdNode159 thresholdNode174
def thresholdCell0Out0 : TaylorCertificate1 :=
  { center := (-141/320:ℚ), radius := (19/320:ℚ)
    whole := thresholdNode29, centerValue := thresholdNode50, gradient := thresholdNode89, hessian := thresholdNode175 }
theorem thresholdCell0Out0_check : thresholdCell0Out0.check = true := by decide +kernel
theorem thresholdCell0Out0_lower_pos : 0 < thresholdCell0Out0.lower := by decide +kernel
theorem thresholdCell0Out0_positive (x : ℝ) (hx : (-(1/2:ℝ)) ≤ x ∧ x ≤ (-(61/160:ℝ))) :
    0 < thresholdNode29.eval (fun _ => x) := by
  apply thresholdCell0Out0.positive_sound thresholdCell0Out0_check thresholdCell0Out0_lower_pos x
  norm_num [thresholdCell0Out0]
  exact hx
def thresholdNode176 : BoxExpr 1 := .mul ⟨(19207839868090646850511/4722366482869645213696:ℚ),(25748065877594541781103/4722366482869645213696:ℚ)⟩ thresholdNode29 thresholdNode29
def thresholdNode177 : BoxExpr 1 := .mul ⟨(-1/1:ℚ),(-1800402221594052237721/2361183241434822606848:ℚ)⟩ thresholdNode13 thresholdNode5
def thresholdNode178 : BoxExpr 1 := .neg ⟨(1800402221594052237721/2361183241434822606848:ℚ),(1/1:ℚ)⟩ thresholdNode177
def thresholdNode179 : BoxExpr 1 := .add ⟨(4161585463028874844569/2361183241434822606848:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode178
def thresholdNode180 : BoxExpr 1 := .lit (7033791386230630914920427/47247072600500000000000:ℚ)
def thresholdNode181 : BoxExpr 1 := .mul ⟨(1239091540355257427262089/4722366482869645213696:ℚ),(351515330597236149577949/1180591620717411303424:ℚ)⟩ thresholdNode179 thresholdNode180
def thresholdNode182 : BoxExpr 1 := .lit (4/1:ℚ)
def thresholdNode183 : BoxExpr 1 := .mul ⟨(-2/1:ℚ),(-1800402221594052237721/1180591620717411303424:ℚ)⟩ thresholdNode13 thresholdNode182
def thresholdNode184 : BoxExpr 1 := .neg ⟨(1800402221594052237721/1180591620717411303424:ℚ),(2/1:ℚ)⟩ thresholdNode183
def thresholdNode185 : BoxExpr 1 := .add ⟨(2980993842311463541145/1180591620717411303424:ℚ),(3/1:ℚ)⟩ thresholdNode12 thresholdNode184
def thresholdNode186 : BoxExpr 1 := .inv ⟨(1574122160956548404565/4722366482869645213696:ℚ),(935122075815771329445/2361183241434822606848:ℚ)⟩ thresholdNode185
def thresholdNode187 : BoxExpr 1 := .mul ⟨(206515256725876237876971/2361183241434822606848:ℚ),(139213992315737088941799/1180591620717411303424:ℚ)⟩ thresholdNode181 thresholdNode186
def thresholdNode188 : BoxExpr 1 := .add ⟨(208876439967311060483819/2361183241434822606848:ℚ),(140394583936454500245223/1180591620717411303424:ℚ)⟩ thresholdNode187 thresholdNode12
def thresholdNode189 : BoxExpr 1 := .sqrt ⟨(44416012859390324252709/4722366482869645213696:ℚ),(51497366051398855124545/4722366482869645213696:ℚ)⟩ thresholdNode188
def thresholdNode190 : BoxExpr 1 := .add ⟨(49138379342259969466405/4722366482869645213696:ℚ),(56219732534268500338241/4722366482869645213696:ℚ)⟩ thresholdNode189 thresholdNode12
def thresholdNode191 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode192 : BoxExpr 1 := .mul ⟨(12284594835564992366601/2361183241434822606848:ℚ),(28109866267134250169121/4722366482869645213696:ℚ)⟩ thresholdNode190 thresholdNode191
def thresholdNode193 : BoxExpr 1 := .lit (1/4:ℚ)
def thresholdNode194 : BoxExpr 1 := .add ⟨(12874890645923698018313/2361183241434822606848:ℚ),(29290457887851661472545/4722366482869645213696:ℚ)⟩ thresholdNode192 thresholdNode193
def thresholdNode195 : BoxExpr 1 := .mul ⟨(19312335968885547027469/4722366482869645213696:ℚ),(12516522033755986354649/2361183241434822606848:ℚ)⟩ thresholdNode16 thresholdNode194
def thresholdNode196 : BoxExpr 1 := .neg ⟨(-12516522033755986354649/2361183241434822606848:ℚ),(-19312335968885547027469/4722366482869645213696:ℚ)⟩ thresholdNode195
def thresholdNode197 : BoxExpr 1 := .add ⟨(-5825204199421325858787/4722366482869645213696:ℚ),(3217864954354497376817/2361183241434822606848:ℚ)⟩ thresholdNode176 thresholdNode196
def thresholdNode198 : BoxExpr 1 := .mul ⟨(11214536979015306848789/2361183241434822606848:ℚ),(11214536979015306848833/2361183241434822606848:ℚ)⟩ thresholdNode50 thresholdNode50
def thresholdNode199 : BoxExpr 1 := .mul ⟨(-2080792731514437422285/2361183241434822606848:ℚ),(-520198182878609355571/590295810358705651712:ℚ)⟩ thresholdNode37 thresholdNode5
def thresholdNode200 : BoxExpr 1 := .neg ⟨(520198182878609355571/590295810358705651712:ℚ),(2080792731514437422285/2361183241434822606848:ℚ)⟩ thresholdNode199
def thresholdNode201 : BoxExpr 1 := .add ⟨(1110493993237315007283/590295810358705651712:ℚ),(4441975972949260029133/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode200
def thresholdNode202 : BoxExpr 1 := .mul ⟨(1322576431372101012786793/4722366482869645213696:ℚ),(1322576431372101012787093/4722366482869645213696:ℚ)⟩ thresholdNode201 thresholdNode180
def thresholdNode203 : BoxExpr 1 := .mul ⟨(-2080792731514437422285/1180591620717411303424:ℚ),(-520198182878609355571/295147905179352825856:ℚ)⟩ thresholdNode37 thresholdNode182
def thresholdNode204 : BoxExpr 1 := .neg ⟨(520198182878609355571/295147905179352825856:ℚ),(2080792731514437422285/1180591620717411303424:ℚ)⟩ thresholdNode203
def thresholdNode205 : BoxExpr 1 := .add ⟨(815346088057962181427/295147905179352825856:ℚ),(3261384352231848725709/1180591620717411303424:ℚ)⟩ thresholdNode12 thresholdNode204
def thresholdNode206 : BoxExpr 1 := .inv ⟨(106840870653159393975/295147905179352825856:ℚ),(1709453930450550303601/4722366482869645213696:ℚ)⟩ thresholdNode205
def thresholdNode207 : BoxExpr 1 := .mul ⟨(478760699139222086076565/4722366482869645213696:ℚ),(478760699139222086076955/4722366482869645213696:ℚ)⟩ thresholdNode202 thresholdNode206
def thresholdNode208 : BoxExpr 1 := .add ⟨(483483065622091731290261/4722366482869645213696:ℚ),(483483065622091731290651/4722366482869645213696:ℚ)⟩ thresholdNode207 thresholdNode12
def thresholdNode209 : BoxExpr 1 := .sqrt ⟨(47782677029744066072429/4722366482869645213696:ℚ),(47782677029744066072449/4722366482869645213696:ℚ)⟩ thresholdNode208
def thresholdNode210 : BoxExpr 1 := .add ⟨(52505043512613711286125/4722366482869645213696:ℚ),(52505043512613711286145/4722366482869645213696:ℚ)⟩ thresholdNode209 thresholdNode12
def thresholdNode211 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode212 : BoxExpr 1 := .mul ⟨(13126260878153427821531/2361183241434822606848:ℚ),(26252521756306855643073/4722366482869645213696:ℚ)⟩ thresholdNode210 thresholdNode211
def thresholdNode213 : BoxExpr 1 := .add ⟨(13716556688512133473243/2361183241434822606848:ℚ),(27433113377024266946497/4722366482869645213696:ℚ)⟩ thresholdNode212 thresholdNode193
def thresholdNode214 : BoxExpr 1 := .mul ⟨(22106963698815092618717/4722366482869645213696:ℚ),(11053481849407546309369/2361183241434822606848:ℚ)⟩ thresholdNode40 thresholdNode213
def thresholdNode215 : BoxExpr 1 := .neg ⟨(-11053481849407546309369/2361183241434822606848:ℚ),(-22106963698815092618717/4722366482869645213696:ℚ)⟩ thresholdNode214
def thresholdNode216 : BoxExpr 1 := .add ⟨(40263782401940134855/590295810358705651712:ℚ),(322110259215521078949/4722366482869645213696:ℚ)⟩ thresholdNode198 thresholdNode215
def thresholdNode217 : BoxExpr 1 := .mul ⟨(6706349952886118172743/2361183241434822606848:ℚ),(13412699905772236345561/4722366482869645213696:ℚ)⟩ thresholdNode89 thresholdNode50
def thresholdNode218 : BoxExpr 1 := .mul ⟨(6706349952886118172743/2361183241434822606848:ℚ),(13412699905772236345561/4722366482869645213696:ℚ)⟩ thresholdNode50 thresholdNode89
def thresholdNode219 : BoxExpr 1 := .add ⟨(6706349952886118172743/1180591620717411303424:ℚ),(13412699905772236345561/2361183241434822606848:ℚ)⟩ thresholdNode217 thresholdNode218
def thresholdNode220 : BoxExpr 1 := .mul ⟨(24175431163502635246581/4722366482869645213696:ℚ),(24175431163502635246603/4722366482869645213696:ℚ)⟩ thresholdNode70 thresholdNode213
def thresholdNode221 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode222 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode37 thresholdNode51
def thresholdNode223 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode221 thresholdNode222
def thresholdNode224 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode223
def thresholdNode225 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode224
def thresholdNode226 : BoxExpr 1 := .mul ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode225 thresholdNode180
def thresholdNode227 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode201 thresholdNode51
def thresholdNode228 : BoxExpr 1 := .add ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode226 thresholdNode227
def thresholdNode229 : BoxExpr 1 := .mul ⟨(-508981474167943745995411/4722366482869645213696:ℚ),(-508981474167943745995111/4722366482869645213696:ℚ)⟩ thresholdNode228 thresholdNode206
def thresholdNode230 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode12 thresholdNode182
def thresholdNode231 : BoxExpr 1 := .add ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode230 thresholdNode222
def thresholdNode232 : BoxExpr 1 := .neg ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode231
def thresholdNode233 : BoxExpr 1 := .add ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode51 thresholdNode232
def thresholdNode234 : BoxExpr 1 := .mul ⟨(4504787136520241052383/590295810358705651712:ℚ),(36038297092161928419087/4722366482869645213696:ℚ)⟩ thresholdNode205 thresholdNode205
def thresholdNode235 : BoxExpr 1 := .inv ⟨(309403426325891457665/2361183241434822606848:ℚ),(618806852651782915331/4722366482869645213696:ℚ)⟩ thresholdNode234
def thresholdNode236 : BoxExpr 1 := .mul ⟨(-618806852651782915331/1180591620717411303424:ℚ),(-309403426325891457665/590295810358705651712:ℚ)⟩ thresholdNode233 thresholdNode235
def thresholdNode237 : BoxExpr 1 := .neg ⟨(309403426325891457665/590295810358705651712:ℚ),(618806852651782915331/1180591620717411303424:ℚ)⟩ thresholdNode236
def thresholdNode238 : BoxExpr 1 := .mul ⟨(346614080824776170914983/2361183241434822606848:ℚ),(693228161649552341831245/4722366482869645213696:ℚ)⟩ thresholdNode202 thresholdNode237
def thresholdNode239 : BoxExpr 1 := .add ⟨(184246687481608595834555/4722366482869645213696:ℚ),(92123343740804297918067/2361183241434822606848:ℚ)⟩ thresholdNode229 thresholdNode238
def thresholdNode240 : BoxExpr 1 := .add ⟨(184246687481608595834555/4722366482869645213696:ℚ),(92123343740804297918067/2361183241434822606848:ℚ)⟩ thresholdNode239 thresholdNode51
def thresholdNode241 : BoxExpr 1 := .mul ⟨(47782677029744066072429/2361183241434822606848:ℚ),(47782677029744066072449/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode209
def thresholdNode242 : BoxExpr 1 := .inv ⟨(233355962712686783903/4722366482869645213696:ℚ),(7292373834771461997/147573952589676412928:ℚ)⟩ thresholdNode241
def thresholdNode243 : BoxExpr 1 := .mul ⟨(569034922557612693787/295147905179352825856:ℚ),(4552279380460901550355/2361183241434822606848:ℚ)⟩ thresholdNode240 thresholdNode242
def thresholdNode244 : BoxExpr 1 := .add ⟨(569034922557612693787/295147905179352825856:ℚ),(4552279380460901550355/2361183241434822606848:ℚ)⟩ thresholdNode243 thresholdNode51
def thresholdNode245 : BoxExpr 1 := .mul ⟨(569034922557612693787/590295810358705651712:ℚ),(4552279380460901550355/4722366482869645213696:ℚ)⟩ thresholdNode244 thresholdNode211
def thresholdNode246 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode247 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode246
def thresholdNode248 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode247
def thresholdNode249 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode248
def thresholdNode250 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode210 thresholdNode249
def thresholdNode251 : BoxExpr 1 := .add ⟨(569034922557612693787/590295810358705651712:ℚ),(4552279380460901550355/4722366482869645213696:ℚ)⟩ thresholdNode245 thresholdNode250
def thresholdNode252 : BoxExpr 1 := .add ⟨(569034922557612693787/590295810358705651712:ℚ),(4552279380460901550355/4722366482869645213696:ℚ)⟩ thresholdNode251 thresholdNode51
def thresholdNode253 : BoxExpr 1 := .mul ⟨(3668452560510284521765/4722366482869645213696:ℚ),(458556570063785565227/590295810358705651712:ℚ)⟩ thresholdNode40 thresholdNode252
def thresholdNode254 : BoxExpr 1 := .add ⟨(13921941862006459884173/2361183241434822606848:ℚ),(27843883724012919768419/4722366482869645213696:ℚ)⟩ thresholdNode220 thresholdNode253
def thresholdNode255 : BoxExpr 1 := .neg ⟨(-27843883724012919768419/4722366482869645213696:ℚ),(-13921941862006459884173/2361183241434822606848:ℚ)⟩ thresholdNode254
def thresholdNode256 : BoxExpr 1 := .add ⟨(-1018483912468447077447/4722366482869645213696:ℚ),(-127310489058555884653/590295810358705651712:ℚ)⟩ thresholdNode219 thresholdNode255
def thresholdNode257 : BoxExpr 1 := .mul ⟨(-6478177396475565506407/1180591620717411303424:ℚ),(-1949925990547449383957/590295810358705651712:ℚ)⟩ thresholdNode175 thresholdNode29
def thresholdNode258 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode118 thresholdNode17
def thresholdNode259 : BoxExpr 1 := .mul ⟨(1265553642439078482773/1180591620717411303424:ℚ),(885877832192220301425/590295810358705651712:ℚ)⟩ thresholdNode11 thresholdNode126
def thresholdNode260 : BoxExpr 1 := .add ⟨(1265553642439078482773/1180591620717411303424:ℚ),(885877832192220301425/590295810358705651712:ℚ)⟩ thresholdNode258 thresholdNode259
def thresholdNode261 : BoxExpr 1 := .mul ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode152 thresholdNode22
def thresholdNode262 : BoxExpr 1 := .add ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode261 thresholdNode155
def thresholdNode263 : BoxExpr 1 := .neg ⟨(1685884834384463341289/2361183241434822606848:ℚ),(3371769668768926682579/4722366482869645213696:ℚ)⟩ thresholdNode262
def thresholdNode264 : BoxExpr 1 := .add ⟨(4216992119262620306835/2361183241434822606848:ℚ),(10458792326306689093979/4722366482869645213696:ℚ)⟩ thresholdNode260 thresholdNode263
def thresholdNode265 : BoxExpr 1 := .mul ⟨(-3705640979107810599189/4722366482869645213696:ℚ),(-2779230734330857949387/4722366482869645213696:ℚ)⟩ thresholdNode169 thresholdNode27
def thresholdNode266 : BoxExpr 1 := .add ⟨(-3705640979107810599189/4722366482869645213696:ℚ),(-2779230734330857949387/4722366482869645213696:ℚ)⟩ thresholdNode265 thresholdNode172
def thresholdNode267 : BoxExpr 1 := .add ⟨(4728343259417430014481/4722366482869645213696:ℚ),(479972599498489446537/295147905179352825856:ℚ)⟩ thresholdNode264 thresholdNode266
def thresholdNode268 : BoxExpr 1 := .mul ⟨(4734327600362859879709/4722366482869645213696:ℚ),(12488583098936565236857/4722366482869645213696:ℚ)⟩ thresholdNode267 thresholdNode267
def thresholdNode269 : BoxExpr 1 := .add ⟨(-21178381985539402145919/4722366482869645213696:ℚ),(-3110824825443029834799/4722366482869645213696:ℚ)⟩ thresholdNode257 thresholdNode268
def thresholdNode270 : BoxExpr 1 := .mul ⟨(-6478177396475565506407/1180591620717411303424:ℚ),(-1949925990547449383957/590295810358705651712:ℚ)⟩ thresholdNode29 thresholdNode175
def thresholdNode271 : BoxExpr 1 := .add ⟨(-21178381985539402145919/4722366482869645213696:ℚ),(-3110824825443029834799/4722366482869645213696:ℚ)⟩ thresholdNode268 thresholdNode270
def thresholdNode272 : BoxExpr 1 := .add ⟨(-21178381985539402145919/2361183241434822606848:ℚ),(-3110824825443029834799/2361183241434822606848:ℚ)⟩ thresholdNode269 thresholdNode271
def thresholdNode273 : BoxExpr 1 := .mul ⟨(-29290457887851661472545/2361183241434822606848:ℚ),(-12874890645923698018313/1180591620717411303424:ℚ)⟩ thresholdNode136 thresholdNode194
def thresholdNode274 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode275 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode274 thresholdNode132
def thresholdNode276 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode275
def thresholdNode277 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode276
def thresholdNode278 : BoxExpr 1 := .mul ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode277 thresholdNode180
def thresholdNode279 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode179 thresholdNode51
def thresholdNode280 : BoxExpr 1 := .add ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode278 thresholdNode279
def thresholdNode281 : BoxExpr 1 := .mul ⟨(-139213992315737088941799/1180591620717411303424:ℚ),(-234343553731490766385249/2361183241434822606848:ℚ)⟩ thresholdNode280 thresholdNode186
def thresholdNode282 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode12 thresholdNode182
def thresholdNode283 : BoxExpr 1 := .add ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode282 thresholdNode132
def thresholdNode284 : BoxExpr 1 := .neg ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode283
def thresholdNode285 : BoxExpr 1 := .add ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode51 thresholdNode284
def thresholdNode286 : BoxExpr 1 := .mul ⟨(15054018903672890882779/2361183241434822606848:ℚ),(9/1:ℚ)⟩ thresholdNode185 thresholdNode185
def thresholdNode287 : BoxExpr 1 := .inv ⟨(524707386985516134855/4722366482869645213696:ℚ),(92586344140175379153/590295810358705651712:ℚ)⟩ thresholdNode286
def thresholdNode288 : BoxExpr 1 := .mul ⟨(-92586344140175379153/147573952589676412928:ℚ),(-524707386985516134855/1180591620717411303424:ℚ)⟩ thresholdNode285 thresholdNode287
def thresholdNode289 : BoxExpr 1 := .neg ⟨(524707386985516134855/1180591620717411303424:ℚ),(92586344140175379153/147573952589676412928:ℚ)⟩ thresholdNode288
def thresholdNode290 : BoxExpr 1 := .mul ⟨(68838418908625412625657/590295810358705651712:ℚ),(110268508764940268468787/590295810358705651712:ℚ)⟩ thresholdNode181 thresholdNode289
def thresholdNode291 : BoxExpr 1 := .add ⟨(-1537154498486263690485/1180591620717411303424:ℚ),(206730481328270307489899/2361183241434822606848:ℚ)⟩ thresholdNode281 thresholdNode290
def thresholdNode292 : BoxExpr 1 := .add ⟨(-1537154498486263690485/1180591620717411303424:ℚ),(206730481328270307489899/2361183241434822606848:ℚ)⟩ thresholdNode291 thresholdNode51
def thresholdNode293 : BoxExpr 1 := .mul ⟨(44416012859390324252709/2361183241434822606848:ℚ),(51497366051398855124545/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode189
def thresholdNode294 : BoxExpr 1 := .inv ⟨(216523163303852644987/4722366482869645213696:ℚ),(251043978993894027711/4722366482869645213696:ℚ)⟩ thresholdNode293
def thresholdNode295 : BoxExpr 1 := .mul ⟨(-326864408366594258633/4722366482869645213696:ℚ),(21979845401763360607313/4722366482869645213696:ℚ)⟩ thresholdNode292 thresholdNode294
def thresholdNode296 : BoxExpr 1 := .add ⟨(-326864408366594258633/4722366482869645213696:ℚ),(21979845401763360607313/4722366482869645213696:ℚ)⟩ thresholdNode295 thresholdNode51
def thresholdNode297 : BoxExpr 1 := .mul ⟨(-163432204183297129317/4722366482869645213696:ℚ),(10989922700881680303657/4722366482869645213696:ℚ)⟩ thresholdNode296 thresholdNode191
def thresholdNode298 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode299 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode298
def thresholdNode300 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode299
def thresholdNode301 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode300
def thresholdNode302 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode190 thresholdNode301
def thresholdNode303 : BoxExpr 1 := .add ⟨(-163432204183297129317/4722366482869645213696:ℚ),(10989922700881680303657/4722366482869645213696:ℚ)⟩ thresholdNode297 thresholdNode302
def thresholdNode304 : BoxExpr 1 := .add ⟨(-163432204183297129317/4722366482869645213696:ℚ),(10989922700881680303657/4722366482869645213696:ℚ)⟩ thresholdNode303 thresholdNode51
def thresholdNode305 : BoxExpr 1 := .mul ⟨(-163432204183297129317/4722366482869645213696:ℚ),(10989922700881680303657/4722366482869645213696:ℚ)⟩ thresholdNode123 thresholdNode304
def thresholdNode306 : BoxExpr 1 := .add ⟨(-58744347979886620074407/4722366482869645213696:ℚ),(-40509639882813111769595/4722366482869645213696:ℚ)⟩ thresholdNode273 thresholdNode305
def thresholdNode307 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode5
def thresholdNode308 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode12 thresholdNode51
def thresholdNode309 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode307 thresholdNode308
def thresholdNode310 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode308 thresholdNode132
def thresholdNode311 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode309 thresholdNode310
def thresholdNode312 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode311
def thresholdNode313 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode312
def thresholdNode314 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode313 thresholdNode180
def thresholdNode315 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode277 thresholdNode51
def thresholdNode316 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode314 thresholdNode315
def thresholdNode317 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode315 thresholdNode279
def thresholdNode318 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode316 thresholdNode317
def thresholdNode319 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode318 thresholdNode186
def thresholdNode320 : BoxExpr 1 := .mul ⟨(-110268508764940268468787/590295810358705651712:ℚ),(-624916143283975377027331/4722366482869645213696:ℚ)⟩ thresholdNode280 thresholdNode289
def thresholdNode321 : BoxExpr 1 := .add ⟨(-110268508764940268468787/590295810358705651712:ℚ),(-624916143283975377027331/4722366482869645213696:ℚ)⟩ thresholdNode319 thresholdNode320
def thresholdNode322 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode182
def thresholdNode323 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode322 thresholdNode308
def thresholdNode324 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode323 thresholdNode310
def thresholdNode325 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode324
def thresholdNode326 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode325
def thresholdNode327 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode326 thresholdNode287
def thresholdNode328 : BoxExpr 1 := .mul ⟨(-12/1:ℚ),(-2980993842311463541145/295147905179352825856:ℚ)⟩ thresholdNode285 thresholdNode185
def thresholdNode329 : BoxExpr 1 := .mul ⟨(-12/1:ℚ),(-2980993842311463541145/295147905179352825856:ℚ)⟩ thresholdNode185 thresholdNode285
def thresholdNode330 : BoxExpr 1 := .add ⟨(-24/1:ℚ),(-2980993842311463541145/147573952589676412928:ℚ)⟩ thresholdNode328 thresholdNode329
def thresholdNode331 : BoxExpr 1 := .mul ⟨(191957558545458949868955/4722366482869645213696:ℚ),(81/1:ℚ)⟩ thresholdNode286 thresholdNode286
def thresholdNode332 : BoxExpr 1 := .inv ⟨(14575205194042114857/1180591620717411303424:ℚ),(58087697529371868109/2361183241434822606848:ℚ)⟩ thresholdNode331
def thresholdNode333 : BoxExpr 1 := .mul ⟨(-174263092588115604327/295147905179352825856:ℚ),(-1177676579678602880445/4722366482869645213696:ℚ)⟩ thresholdNode330 thresholdNode332
def thresholdNode334 : BoxExpr 1 := .neg ⟨(1177676579678602880445/4722366482869645213696:ℚ),(174263092588115604327/295147905179352825856:ℚ)⟩ thresholdNode333
def thresholdNode335 : BoxExpr 1 := .mul ⟨(-174263092588115604327/73786976294838206464:ℚ),(-1177676579678602880445/1180591620717411303424:ℚ)⟩ thresholdNode285 thresholdNode334
def thresholdNode336 : BoxExpr 1 := .add ⟨(-174263092588115604327/73786976294838206464:ℚ),(-1177676579678602880445/1180591620717411303424:ℚ)⟩ thresholdNode327 thresholdNode335
def thresholdNode337 : BoxExpr 1 := .neg ⟨(1177676579678602880445/1180591620717411303424:ℚ),(174263092588115604327/73786976294838206464:ℚ)⟩ thresholdNode336
def thresholdNode338 : BoxExpr 1 := .mul ⟨(618016027535214815568717/2361183241434822606848:ℚ),(830175617404902717225073/1180591620717411303424:ℚ)⟩ thresholdNode181 thresholdNode337
def thresholdNode339 : BoxExpr 1 := .add ⟨(176941992475453741693569/2361183241434822606848:ℚ),(2695786326335635491872961/4722366482869645213696:ℚ)⟩ thresholdNode320 thresholdNode338
def thresholdNode340 : BoxExpr 1 := .add ⟨(-264132042584307332181579/2361183241434822606848:ℚ),(1035435091525830057422815/2361183241434822606848:ℚ)⟩ thresholdNode321 thresholdNode339
def thresholdNode341 : BoxExpr 1 := .add ⟨(-264132042584307332181579/2361183241434822606848:ℚ),(1035435091525830057422815/2361183241434822606848:ℚ)⟩ thresholdNode340 thresholdNode51
def thresholdNode342 : BoxExpr 1 := .mul ⟨(-14041425880579954930861/2361183241434822606848:ℚ),(55044382156590560316021/2361183241434822606848:ℚ)⟩ thresholdNode341 thresholdNode294
def thresholdNode343 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode189
def thresholdNode344 : BoxExpr 1 := .mul ⟨(-326864408366594258633/2361183241434822606848:ℚ),(21979845401763360607313/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode295
def thresholdNode345 : BoxExpr 1 := .add ⟨(-326864408366594258633/2361183241434822606848:ℚ),(21979845401763360607313/2361183241434822606848:ℚ)⟩ thresholdNode343 thresholdNode344
def thresholdNode346 : BoxExpr 1 := .mul ⟨(835505759869244241935263/2361183241434822606848:ℚ),(2246313342983272003923617/4722366482869645213696:ℚ)⟩ thresholdNode293 thresholdNode293
def thresholdNode347 : BoxExpr 1 := .inv ⟨(9927709002927243805/4722366482869645213696:ℚ),(13345656169994965637/4722366482869645213696:ℚ)⟩ thresholdNode346
def thresholdNode348 : BoxExpr 1 := .mul ⟨(-1847472035088051063/4722366482869645213696:ℚ),(62116199677778335567/2361183241434822606848:ℚ)⟩ thresholdNode345 thresholdNode347
def thresholdNode349 : BoxExpr 1 := .neg ⟨(-62116199677778335567/2361183241434822606848:ℚ),(1847472035088051063/4722366482869645213696:ℚ)⟩ thresholdNode348
def thresholdNode350 : BoxExpr 1 := .mul ⟨(-5438507114706934534987/2361183241434822606848:ℚ),(161753131375854098057/4722366482869645213696:ℚ)⟩ thresholdNode292 thresholdNode349
def thresholdNode351 : BoxExpr 1 := .add ⟨(-2434991624410861183231/295147905179352825856:ℚ),(110250517444556974730099/4722366482869645213696:ℚ)⟩ thresholdNode342 thresholdNode350
def thresholdNode352 : BoxExpr 1 := .add ⟨(-2434991624410861183231/295147905179352825856:ℚ),(110250517444556974730099/4722366482869645213696:ℚ)⟩ thresholdNode351 thresholdNode51
def thresholdNode353 : BoxExpr 1 := .mul ⟨(-2434991624410861183231/590295810358705651712:ℚ),(27562629361139243682525/2361183241434822606848:ℚ)⟩ thresholdNode352 thresholdNode191
def thresholdNode354 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode296 thresholdNode301
def thresholdNode355 : BoxExpr 1 := .add ⟨(-2434991624410861183231/590295810358705651712:ℚ),(27562629361139243682525/2361183241434822606848:ℚ)⟩ thresholdNode353 thresholdNode354
def thresholdNode356 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode5 thresholdNode51
def thresholdNode357 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode307 thresholdNode356
def thresholdNode358 : BoxExpr 1 := .mul ⟨(16/1:ℚ),(16/1:ℚ)⟩ thresholdNode298 thresholdNode298
def thresholdNode359 : BoxExpr 1 := .inv ⟨(1/16:ℚ),(1/16:ℚ)⟩ thresholdNode358
def thresholdNode360 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode357 thresholdNode359
def thresholdNode361 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode360
def thresholdNode362 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode361
def thresholdNode363 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode300 thresholdNode362
def thresholdNode364 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode363
def thresholdNode365 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode190 thresholdNode364
def thresholdNode366 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode354 thresholdNode365
def thresholdNode367 : BoxExpr 1 := .add ⟨(-2434991624410861183231/590295810358705651712:ℚ),(27562629361139243682525/2361183241434822606848:ℚ)⟩ thresholdNode355 thresholdNode366
def thresholdNode368 : BoxExpr 1 := .add ⟨(-2434991624410861183231/590295810358705651712:ℚ),(27562629361139243682525/2361183241434822606848:ℚ)⟩ thresholdNode367 thresholdNode51
def thresholdNode369 : BoxExpr 1 := .mul ⟨(-4162123574256658736557/1180591620717411303424:ℚ),(11778179058444638916605/1180591620717411303424:ℚ)⟩ thresholdNode16 thresholdNode368
def thresholdNode370 : BoxExpr 1 := .add ⟨(-16811926501209932075545/4722366482869645213696:ℚ),(58102638934660235970077/4722366482869645213696:ℚ)⟩ thresholdNode305 thresholdNode369
def thresholdNode371 : BoxExpr 1 := .add ⟨(-1180566788767133627343/73786976294838206464:ℚ),(8796499525923562100241/2361183241434822606848:ℚ)⟩ thresholdNode306 thresholdNode370
def thresholdNode372 : BoxExpr 1 := .neg ⟨(-8796499525923562100241/2361183241434822606848:ℚ),(1180566788767133627343/73786976294838206464:ℚ)⟩ thresholdNode371
def thresholdNode373 : BoxExpr 1 := .add ⟨(-1873430094466435265385/147573952589676412928:ℚ),(34667312415105246240177/2361183241434822606848:ℚ)⟩ thresholdNode272 thresholdNode372
def thresholdCell0Out1 : TaylorCertificate1 :=
  { center := (-141/320:ℚ), radius := (19/320:ℚ)
    whole := thresholdNode197, centerValue := thresholdNode216, gradient := thresholdNode256, hessian := thresholdNode373 }
theorem thresholdCell0Out1_check : thresholdCell0Out1.check = true := by decide +kernel
theorem thresholdCell0Out1_lower_pos : 0 < thresholdCell0Out1.lower := by decide +kernel
theorem thresholdCell0Out1_positive (x : ℝ) (hx : (-(1/2:ℝ)) ≤ x ∧ x ≤ (-(61/160:ℝ))) :
    0 < thresholdNode197.eval (fun _ => x) := by
  apply thresholdCell0Out1.positive_sound thresholdCell0Out1_check thresholdCell0Out1_lower_pos x
  norm_num [thresholdCell0Out1]
  exact hx
theorem thresholdCell0_public (x : ℝ)
    (hx : (-(1/2:ℝ)) ≤ x ∧ x ≤ (-(61/160:ℝ))) : qc x < fA (43/20) x := by
  have hf := thresholdCell0Out0_positive x hx
  have hg := thresholdCell0Out1_positive x hx
  have hfa : thresholdNode29.eval (fun _ => x) = thresholdFA 0 x := by
    norm_num [thresholdNode0, thresholdNode1, thresholdNode2, thresholdNode3, thresholdNode4, thresholdNode5, thresholdNode6, thresholdNode7, thresholdNode8, thresholdNode9, thresholdNode10, thresholdNode11, thresholdNode12, thresholdNode13, thresholdNode14, thresholdNode15, thresholdNode16, thresholdNode17, thresholdNode18, thresholdNode19, thresholdNode20, thresholdNode21, thresholdNode22, thresholdNode23, thresholdNode24, thresholdNode25, thresholdNode26, thresholdNode27, thresholdNode28, thresholdNode29, BoxExpr.eval, thresholdFA, ftilde, pow_two, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  have hgap : thresholdNode197.eval (fun _ => x) =
      (thresholdNode29.eval (fun _ => x))^2 - (1-x^2)*(thresholdCapacity 1 x+1/4) := by
    norm_num [thresholdNode176, thresholdNode12, thresholdNode13, thresholdNode14, thresholdNode15, thresholdNode16, thresholdNode5, thresholdNode177, thresholdNode178, thresholdNode179, thresholdNode180, thresholdNode181, thresholdNode182, thresholdNode183, thresholdNode184, thresholdNode185, thresholdNode186, thresholdNode187, thresholdNode188, thresholdNode189, thresholdNode190, thresholdNode191, thresholdNode192, thresholdNode193, thresholdNode194, thresholdNode195, thresholdNode196, thresholdNode197, BoxExpr.eval, thresholdCapacity, Da, D5, beta5, eta5, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  rw [hfa] at hf
  rw [hgap, hfa] at hg
  refine threshold_positive_to_public 0 1 x ?_ ?_ ?_ hf hg
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdFADomain] <;> constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdCapacityDomain] <;> linarith [hx.1,hx.2]
def thresholdNode374 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode375 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode374 thresholdNode3
def thresholdNode376 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode377 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode376
def thresholdNode378 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode377 thresholdNode377
def thresholdNode379 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode378 thresholdNode9
def thresholdNode380 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode375 thresholdNode379
def thresholdNode381 : BoxExpr 1 := .var 0
def thresholdNode382 : BoxExpr 1 := .mul ⟨(162700282730118245253/2361183241434822606848:ℚ),(42900209186420775977/295147905179352825856:ℚ)⟩ thresholdNode381 thresholdNode381
def thresholdNode383 : BoxExpr 1 := .neg ⟨(-42900209186420775977/295147905179352825856:ℚ),(-162700282730118245253/2361183241434822606848:ℚ)⟩ thresholdNode382
def thresholdNode384 : BoxExpr 1 := .add ⟨(252247695992932049879/295147905179352825856:ℚ),(2198482958704704361595/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode383
def thresholdNode385 : BoxExpr 1 := .sqrt ⟨(2182847740854239263207/2361183241434822606848:ℚ),(2278381249631762813519/2361183241434822606848:ℚ)⟩ thresholdNode384
def thresholdNode386 : BoxExpr 1 := .mul ⟨(11347970550378933657629/4722366482869645213696:ℚ),(5922310301230322669323/2361183241434822606848:ℚ)⟩ thresholdNode380 thresholdNode385
def thresholdNode387 : BoxExpr 1 := .neg ⟨(1239621201753281868595/4722366482869645213696:ℚ),(900201110797026118861/2361183241434822606848:ℚ)⟩ thresholdNode381
def thresholdNode388 : BoxExpr 1 := .add ⟨(280390509920385184563/1180591620717411303424:ℚ),(420585764880577776845/1180591620717411303424:ℚ)⟩ thresholdNode19 thresholdNode387
def thresholdNode389 : BoxExpr 1 := .mul ⟨(800795296332620087111/4722366482869645213696:ℚ),(600596472249465065335/2361183241434822606848:ℚ)⟩ thresholdNode388 thresholdNode22
def thresholdNode390 : BoxExpr 1 := .neg ⟨(-600596472249465065335/2361183241434822606848:ℚ),(-800795296332620087111/4722366482869645213696:ℚ)⟩ thresholdNode389
def thresholdNode391 : BoxExpr 1 := .add ⟨(10146777605880003526959/4722366482869645213696:ℚ),(11043825306128025251535/4722366482869645213696:ℚ)⟩ thresholdNode386 thresholdNode390
def thresholdNode392 : BoxExpr 1 := .mul ⟨(133185492212182962667/2361183241434822606848:ℚ),(599334714954823332005/4722366482869645213696:ℚ)⟩ thresholdNode388 thresholdNode388
def thresholdNode393 : BoxExpr 1 := .mul ⟨(220022433134526254325/4722366482869645213696:ℚ),(495050474552684072237/4722366482869645213696:ℚ)⟩ thresholdNode392 thresholdNode27
def thresholdNode394 : BoxExpr 1 := .add ⟨(2591700009753632445321/1180591620717411303424:ℚ),(2884718945170177330943/1180591620717411303424:ℚ)⟩ thresholdNode391 thresholdNode393
def thresholdNode395 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode396 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode395 thresholdNode3
def thresholdNode397 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode398 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode397
def thresholdNode399 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode398 thresholdNode398
def thresholdNode400 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode399 thresholdNode9
def thresholdNode401 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode396 thresholdNode400
def thresholdNode402 : BoxExpr 1 := .var 0
def thresholdNode403 : BoxExpr 1 := .mul ⟨(489253769694961582735/4722366482869645213696:ℚ),(30578360605935098921/295147905179352825856:ℚ)⟩ thresholdNode402 thresholdNode402
def thresholdNode404 : BoxExpr 1 := .neg ⟨(-30578360605935098921/295147905179352825856:ℚ),(-489253769694961582735/4722366482869645213696:ℚ)⟩ thresholdNode403
def thresholdNode405 : BoxExpr 1 := .add ⟨(264569544573417726935/295147905179352825856:ℚ),(4233112713174683630961/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode404
def thresholdNode406 : BoxExpr 1 := .sqrt ⟨(4471052403506976566361/4722366482869645213696:ℚ),(4471052403506976566363/4722366482869645213696:ℚ)⟩ thresholdNode405
def thresholdNode407 : BoxExpr 1 := .mul ⟨(5810915032527929768883/2361183241434822606848:ℚ),(2905457516263964884445/1180591620717411303424:ℚ)⟩ thresholdNode401 thresholdNode406
def thresholdNode408 : BoxExpr 1 := .neg ⟨(760005855836833526579/2361183241434822606848:ℚ),(1520011711673667053159/4722366482869645213696:ℚ)⟩ thresholdNode402
def thresholdNode409 : BoxExpr 1 := .add ⟨(1401952549601925922815/4722366482869645213696:ℚ),(1401952549601925922817/4722366482869645213696:ℚ)⟩ thresholdNode19 thresholdNode408
def thresholdNode410 : BoxExpr 1 := .mul ⟨(1000994120415775108889/4722366482869645213696:ℚ),(250248530103943777223/1180591620717411303424:ℚ)⟩ thresholdNode409 thresholdNode22
def thresholdNode411 : BoxExpr 1 := .neg ⟨(-250248530103943777223/1180591620717411303424:ℚ),(-1000994120415775108889/4722366482869645213696:ℚ)⟩ thresholdNode410
def thresholdNode412 : BoxExpr 1 := .add ⟨(5310417972320042214437/2361183241434822606848:ℚ),(10620835944640084428891/4722366482869645213696:ℚ)⟩ thresholdNode407 thresholdNode411
def thresholdNode413 : BoxExpr 1 := .mul ⟨(416204663163071758335/4722366482869645213696:ℚ),(416204663163071758337/4722366482869645213696:ℚ)⟩ thresholdNode409 thresholdNode409
def thresholdNode414 : BoxExpr 1 := .mul ⟨(5371641433948394881/73786976294838206464:ℚ),(343785051772697272387/4722366482869645213696:ℚ)⟩ thresholdNode413 thresholdNode27
def thresholdNode415 : BoxExpr 1 := .add ⟨(5482310498206390850629/2361183241434822606848:ℚ),(5482310498206390850639/2361183241434822606848:ℚ)⟩ thresholdNode412 thresholdNode414
def thresholdNode416 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1
def thresholdNode417 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode51
def thresholdNode418 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode416 thresholdNode417
def thresholdNode419 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode418 thresholdNode51
def thresholdNode420 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51
def thresholdNode421 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode420
def thresholdNode422 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode421 thresholdNode398
def thresholdNode423 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode398 thresholdNode421
def thresholdNode424 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode422 thresholdNode423
def thresholdNode425 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode424 thresholdNode9
def thresholdNode426 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode399 thresholdNode51
def thresholdNode427 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode425 thresholdNode426
def thresholdNode428 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode419 thresholdNode427
def thresholdNode429 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode428 thresholdNode406
def thresholdNode430 : BoxExpr 1 := .mul ⟨(-1520011711673667053159/4722366482869645213696:ℚ),(-760005855836833526579/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode402
def thresholdNode431 : BoxExpr 1 := .mul ⟨(-1520011711673667053159/4722366482869645213696:ℚ),(-760005855836833526579/2361183241434822606848:ℚ)⟩ thresholdNode402 thresholdNode12
def thresholdNode432 : BoxExpr 1 := .add ⟨(-1520011711673667053159/2361183241434822606848:ℚ),(-760005855836833526579/1180591620717411303424:ℚ)⟩ thresholdNode430 thresholdNode431
def thresholdNode433 : BoxExpr 1 := .neg ⟨(760005855836833526579/1180591620717411303424:ℚ),(1520011711673667053159/2361183241434822606848:ℚ)⟩ thresholdNode432
def thresholdNode434 : BoxExpr 1 := .add ⟨(760005855836833526579/1180591620717411303424:ℚ),(1520011711673667053159/2361183241434822606848:ℚ)⟩ thresholdNode51 thresholdNode433
def thresholdNode435 : BoxExpr 1 := .mul ⟨(4471052403506976566361/2361183241434822606848:ℚ),(4471052403506976566363/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode406
def thresholdNode436 : BoxExpr 1 := .inv ⟨(2493903357187057556815/4722366482869645213696:ℚ),(2493903357187057556817/4722366482869645213696:ℚ)⟩ thresholdNode435
def thresholdNode437 : BoxExpr 1 := .mul ⟨(1605450286189168302199/4722366482869645213696:ℚ),(802725143094584151101/2361183241434822606848:ℚ)⟩ thresholdNode434 thresholdNode436
def thresholdNode438 : BoxExpr 1 := .mul ⟨(4173127201405814626319/4722366482869645213696:ℚ),(4173127201405814626331/4722366482869645213696:ℚ)⟩ thresholdNode401 thresholdNode437
def thresholdNode439 : BoxExpr 1 := .add ⟨(4173127201405814626319/4722366482869645213696:ℚ),(4173127201405814626331/4722366482869645213696:ℚ)⟩ thresholdNode429 thresholdNode438
def thresholdNode440 : BoxExpr 1 := .neg ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode12
def thresholdNode441 : BoxExpr 1 := .add ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode51 thresholdNode440
def thresholdNode442 : BoxExpr 1 := .mul ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode441 thresholdNode22
def thresholdNode443 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode409 thresholdNode51
def thresholdNode444 : BoxExpr 1 := .add ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode442 thresholdNode443
def thresholdNode445 : BoxExpr 1 := .neg ⟨(1685884834384463341289/2361183241434822606848:ℚ),(3371769668768926682579/4722366482869645213696:ℚ)⟩ thresholdNode444
def thresholdNode446 : BoxExpr 1 := .add ⟨(7544896870174741308897/4722366482869645213696:ℚ),(3772448435087370654455/2361183241434822606848:ℚ)⟩ thresholdNode439 thresholdNode445
def thresholdNode447 : BoxExpr 1 := .mul ⟨(-1401952549601925922817/4722366482869645213696:ℚ),(-1401952549601925922815/4722366482869645213696:ℚ)⟩ thresholdNode441 thresholdNode409
def thresholdNode448 : BoxExpr 1 := .mul ⟨(-1401952549601925922817/4722366482869645213696:ℚ),(-1401952549601925922815/4722366482869645213696:ℚ)⟩ thresholdNode409 thresholdNode441
def thresholdNode449 : BoxExpr 1 := .add ⟨(-1401952549601925922817/2361183241434822606848:ℚ),(-1401952549601925922815/2361183241434822606848:ℚ)⟩ thresholdNode447 thresholdNode448
def thresholdNode450 : BoxExpr 1 := .mul ⟨(-1158012805971190812247/2361183241434822606848:ℚ),(-2316025611942381624489/4722366482869645213696:ℚ)⟩ thresholdNode449 thresholdNode27
def thresholdNode451 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode413 thresholdNode51
def thresholdNode452 : BoxExpr 1 := .add ⟨(-1158012805971190812247/2361183241434822606848:ℚ),(-2316025611942381624489/4722366482869645213696:ℚ)⟩ thresholdNode450 thresholdNode451
def thresholdNode453 : BoxExpr 1 := .add ⟨(5228871258232359684403/4722366482869645213696:ℚ),(5228871258232359684421/4722366482869645213696:ℚ)⟩ thresholdNode446 thresholdNode452
def thresholdNode454 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1
def thresholdNode455 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode51
def thresholdNode456 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode454 thresholdNode455
def thresholdNode457 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode51
def thresholdNode458 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode455 thresholdNode457
def thresholdNode459 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode456 thresholdNode458
def thresholdNode460 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode459 thresholdNode51
def thresholdNode461 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51
def thresholdNode462 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode461
def thresholdNode463 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode462 thresholdNode377
def thresholdNode464 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode462 thresholdNode462
def thresholdNode465 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode463 thresholdNode464
def thresholdNode466 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode377 thresholdNode462
def thresholdNode467 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode464 thresholdNode466
def thresholdNode468 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode465 thresholdNode467
def thresholdNode469 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode468 thresholdNode9
def thresholdNode470 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode463 thresholdNode466
def thresholdNode471 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode470 thresholdNode51
def thresholdNode472 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode469 thresholdNode471
def thresholdNode473 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode378 thresholdNode51
def thresholdNode474 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode471 thresholdNode473
def thresholdNode475 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode472 thresholdNode474
def thresholdNode476 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode460 thresholdNode475
def thresholdNode477 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode476 thresholdNode385
def thresholdNode478 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode454 thresholdNode457
def thresholdNode479 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode478 thresholdNode51
def thresholdNode480 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode470 thresholdNode9
def thresholdNode481 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode480 thresholdNode473
def thresholdNode482 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode479 thresholdNode481
def thresholdNode483 : BoxExpr 1 := .mul ⟨(-900201110797026118861/2361183241434822606848:ℚ),(-1239621201753281868595/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode381
def thresholdNode484 : BoxExpr 1 := .mul ⟨(-900201110797026118861/2361183241434822606848:ℚ),(-1239621201753281868595/4722366482869645213696:ℚ)⟩ thresholdNode381 thresholdNode12
def thresholdNode485 : BoxExpr 1 := .add ⟨(-900201110797026118861/1180591620717411303424:ℚ),(-1239621201753281868595/2361183241434822606848:ℚ)⟩ thresholdNode483 thresholdNode484
def thresholdNode486 : BoxExpr 1 := .neg ⟨(1239621201753281868595/2361183241434822606848:ℚ),(900201110797026118861/1180591620717411303424:ℚ)⟩ thresholdNode485
def thresholdNode487 : BoxExpr 1 := .add ⟨(1239621201753281868595/2361183241434822606848:ℚ),(900201110797026118861/1180591620717411303424:ℚ)⟩ thresholdNode51 thresholdNode486
def thresholdNode488 : BoxExpr 1 := .mul ⟨(2182847740854239263207/1180591620717411303424:ℚ),(2278381249631762813519/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode385
def thresholdNode489 : BoxExpr 1 := .inv ⟨(2446994461762591375485/4722366482869645213696:ℚ),(1277044247128948424017/2361183241434822606848:ℚ)⟩ thresholdNode488
def thresholdNode490 : BoxExpr 1 := .mul ⟨(1284672092425360472129/4722366482869645213696:ℚ),(1947492476871646346627/4722366482869645213696:ℚ)⟩ thresholdNode487 thresholdNode489
def thresholdNode491 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode482 thresholdNode490
def thresholdNode492 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode477 thresholdNode491
def thresholdNode493 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode381
def thresholdNode494 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode12
def thresholdNode495 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode493 thresholdNode494
def thresholdNode496 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode381 thresholdNode51
def thresholdNode497 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode494 thresholdNode496
def thresholdNode498 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode495 thresholdNode497
def thresholdNode499 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode498
def thresholdNode500 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode499
def thresholdNode501 : BoxExpr 1 := .mul ⟨(-1277044247128948424017/1180591620717411303424:ℚ),(-2446994461762591375485/2361183241434822606848:ℚ)⟩ thresholdNode500 thresholdNode489
def thresholdNode502 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode385
def thresholdNode503 : BoxExpr 1 := .mul ⟨(1284672092425360472129/2361183241434822606848:ℚ),(1947492476871646346627/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode490
def thresholdNode504 : BoxExpr 1 := .add ⟨(1284672092425360472129/2361183241434822606848:ℚ),(1947492476871646346627/2361183241434822606848:ℚ)⟩ thresholdNode502 thresholdNode503
def thresholdNode505 : BoxExpr 1 := .mul ⟨(16143852543547651192249/4722366482869645213696:ℚ),(17587863669637634892763/4722366482869645213696:ℚ)⟩ thresholdNode488 thresholdNode488
def thresholdNode506 : BoxExpr 1 := .inv ⟨(1267962136699350955179/4722366482869645213696:ℚ),(1381376913495394184729/4722366482869645213696:ℚ)⟩ thresholdNode505
def thresholdNode507 : BoxExpr 1 := .mul ⟨(344936289290246141199/2361183241434822606848:ℚ),(1139352973351481934131/4722366482869645213696:ℚ)⟩ thresholdNode504 thresholdNode506
def thresholdNode508 : BoxExpr 1 := .neg ⟨(-1139352973351481934131/4722366482869645213696:ℚ),(-344936289290246141199/2361183241434822606848:ℚ)⟩ thresholdNode507
def thresholdNode509 : BoxExpr 1 := .mul ⟨(-108594580272563121847/590295810358705651712:ℚ),(-181091551877379224129/2361183241434822606848:ℚ)⟩ thresholdNode487 thresholdNode508
def thresholdNode510 : BoxExpr 1 := .add ⟨(-1494233407674074667711/1180591620717411303424:ℚ),(-1314043006819985299807/1180591620717411303424:ℚ)⟩ thresholdNode501 thresholdNode509
def thresholdNode511 : BoxExpr 1 := .mul ⟨(-971008902059401496879/295147905179352825856:ℚ),(-853914422444382197263/295147905179352825856:ℚ)⟩ thresholdNode380 thresholdNode510
def thresholdNode512 : BoxExpr 1 := .add ⟨(-971008902059401496879/295147905179352825856:ℚ),(-853914422444382197263/295147905179352825856:ℚ)⟩ thresholdNode491 thresholdNode511
def thresholdNode513 : BoxExpr 1 := .add ⟨(-971008902059401496879/295147905179352825856:ℚ),(-853914422444382197263/295147905179352825856:ℚ)⟩ thresholdNode492 thresholdNode512
def thresholdNode514 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode462 thresholdNode22
def thresholdNode515 : BoxExpr 1 := .neg ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode12
def thresholdNode516 : BoxExpr 1 := .add ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode51 thresholdNode515
def thresholdNode517 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode516 thresholdNode51
def thresholdNode518 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode514 thresholdNode517
def thresholdNode519 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode388 thresholdNode51
def thresholdNode520 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode517 thresholdNode519
def thresholdNode521 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode518 thresholdNode520
def thresholdNode522 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode521
def thresholdNode523 : BoxExpr 1 := .add ⟨(-971008902059401496879/295147905179352825856:ℚ),(-853914422444382197263/295147905179352825856:ℚ)⟩ thresholdNode513 thresholdNode522
def thresholdNode524 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode462 thresholdNode388
def thresholdNode525 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode516 thresholdNode516
def thresholdNode526 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode524 thresholdNode525
def thresholdNode527 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode388 thresholdNode462
def thresholdNode528 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode525 thresholdNode527
def thresholdNode529 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode526 thresholdNode528
def thresholdNode530 : BoxExpr 1 := .mul ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode529 thresholdNode27
def thresholdNode531 : BoxExpr 1 := .mul ⟨(-420585764880577776845/1180591620717411303424:ℚ),(-280390509920385184563/1180591620717411303424:ℚ)⟩ thresholdNode516 thresholdNode388
def thresholdNode532 : BoxExpr 1 := .mul ⟨(-420585764880577776845/1180591620717411303424:ℚ),(-280390509920385184563/1180591620717411303424:ℚ)⟩ thresholdNode388 thresholdNode516
def thresholdNode533 : BoxExpr 1 := .add ⟨(-420585764880577776845/590295810358705651712:ℚ),(-280390509920385184563/590295810358705651712:ℚ)⟩ thresholdNode531 thresholdNode532
def thresholdNode534 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode533 thresholdNode51
def thresholdNode535 : BoxExpr 1 := .add ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode530 thresholdNode534
def thresholdNode536 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode392 thresholdNode51
def thresholdNode537 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode534 thresholdNode536
def thresholdNode538 : BoxExpr 1 := .add ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode535 thresholdNode537
def thresholdNode539 : BoxExpr 1 := .add ⟨(-483424562703110628565/295147905179352825856:ℚ),(-2930640664704730631591/2361183241434822606848:ℚ)⟩ thresholdNode523 thresholdNode538
def thresholdCell1Out0 : TaylorCertificate1 :=
  { center := (-103/320:ℚ), radius := (19/320:ℚ)
    whole := thresholdNode394, centerValue := thresholdNode415, gradient := thresholdNode453, hessian := thresholdNode539 }
theorem thresholdCell1Out0_check : thresholdCell1Out0.check = true := by decide +kernel
theorem thresholdCell1Out0_lower_pos : 0 < thresholdCell1Out0.lower := by decide +kernel
theorem thresholdCell1Out0_positive (x : ℝ) (hx : (-(61/160:ℝ)) ≤ x ∧ x ≤ (-(21/80:ℝ))) :
    0 < thresholdNode394.eval (fun _ => x) := by
  apply thresholdCell1Out0.positive_sound thresholdCell1Out0_check thresholdCell1Out0_lower_pos x
  norm_num [thresholdCell1Out0]
  exact hx
def thresholdNode540 : BoxExpr 1 := .mul ⟨(22757772705434950206751/4722366482869645213696:ℚ),(28194688990141886393121/4722366482869645213696:ℚ)⟩ thresholdNode394 thresholdNode394
def thresholdNode541 : BoxExpr 1 := .mul ⟨(-900201110797026118861/1180591620717411303424:ℚ),(-1239621201753281868595/2361183241434822606848:ℚ)⟩ thresholdNode381 thresholdNode5
def thresholdNode542 : BoxExpr 1 := .neg ⟨(1239621201753281868595/2361183241434822606848:ℚ),(900201110797026118861/1180591620717411303424:ℚ)⟩ thresholdNode541
def thresholdNode543 : BoxExpr 1 := .add ⟨(3600804443188104475443/2361183241434822606848:ℚ),(2080792731514437422285/1180591620717411303424:ℚ)⟩ thresholdNode12 thresholdNode542
def thresholdNode544 : BoxExpr 1 := .mul ⟨(1072121758321570256212683/4722366482869645213696:ℚ),(619545770177628713631195/2361183241434822606848:ℚ)⟩ thresholdNode543 thresholdNode180
def thresholdNode545 : BoxExpr 1 := .mul ⟨(-900201110797026118861/590295810358705651712:ℚ),(-1239621201753281868595/1180591620717411303424:ℚ)⟩ thresholdNode381 thresholdNode182
def thresholdNode546 : BoxExpr 1 := .neg ⟨(1239621201753281868595/1180591620717411303424:ℚ),(900201110797026118861/590295810358705651712:ℚ)⟩ thresholdNode545
def thresholdNode547 : BoxExpr 1 := .add ⟨(2420212822470693172019/1180591620717411303424:ℚ),(1490496921155731770573/590295810358705651712:ℚ)⟩ thresholdNode12 thresholdNode546
def thresholdNode548 : BoxExpr 1 := .inv ⟨(1870244151631542658889/4722366482869645213696:ℚ),(2303593406277875713999/4722366482869645213696:ℚ)⟩ thresholdNode547
def thresholdNode549 : BoxExpr 1 := .mul ⟨(424602676562998121272235/4722366482869645213696:ℚ),(604434897734271915738001/4722366482869645213696:ℚ)⟩ thresholdNode544 thresholdNode548
def thresholdNode550 : BoxExpr 1 := .add ⟨(429325043045867766485931/4722366482869645213696:ℚ),(609157264217141560951697/4722366482869645213696:ℚ)⟩ thresholdNode549 thresholdNode12
def thresholdNode551 : BoxExpr 1 := .sqrt ⟨(22513497026985687712959/2361183241434822606848:ℚ),(53634539686060492715553/4722366482869645213696:ℚ)⟩ thresholdNode550
def thresholdNode552 : BoxExpr 1 := .add ⟨(24874680268420510319807/2361183241434822606848:ℚ),(58356906168930137929249/4722366482869645213696:ℚ)⟩ thresholdNode551 thresholdNode12
def thresholdNode553 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode554 : BoxExpr 1 := .mul ⟨(24874680268420510319807/4722366482869645213696:ℚ),(29178453084465068964625/4722366482869645213696:ℚ)⟩ thresholdNode552 thresholdNode553
def thresholdNode555 : BoxExpr 1 := .add ⟨(26055271889137921623231/4722366482869645213696:ℚ),(30359044705182480268049/4722366482869645213696:ℚ)⟩ thresholdNode554 thresholdNode193
def thresholdNode556 : BoxExpr 1 := .mul ⟨(2783512176086174742161/590295810358705651712:ℚ),(28267116780965999987081/4722366482869645213696:ℚ)⟩ thresholdNode384 thresholdNode555
def thresholdNode557 : BoxExpr 1 := .neg ⟨(-28267116780965999987081/4722366482869645213696:ℚ),(-2783512176086174742161/590295810358705651712:ℚ)⟩ thresholdNode556
def thresholdNode558 : BoxExpr 1 := .add ⟨(-2754672037765524890165/2361183241434822606848:ℚ),(5926591581452488455833/4722366482869645213696:ℚ)⟩ thresholdNode540 thresholdNode557
def thresholdNode559 : BoxExpr 1 := .mul ⟨(3182274025932863495577/590295810358705651712:ℚ),(25458192207462907964709/4722366482869645213696:ℚ)⟩ thresholdNode415 thresholdNode415
def thresholdNode560 : BoxExpr 1 := .mul ⟨(-1520011711673667053159/2361183241434822606848:ℚ),(-760005855836833526579/1180591620717411303424:ℚ)⟩ thresholdNode402 thresholdNode5
def thresholdNode561 : BoxExpr 1 := .neg ⟨(760005855836833526579/1180591620717411303424:ℚ),(1520011711673667053159/2361183241434822606848:ℚ)⟩ thresholdNode560
def thresholdNode562 : BoxExpr 1 := .add ⟨(1940597476554244830003/1180591620717411303424:ℚ),(3881194953108489660007/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode561
def thresholdNode563 : BoxExpr 1 := .mul ⟨(577803324669206920868693/2361183241434822606848:ℚ),(577803324669206920868843/2361183241434822606848:ℚ)⟩ thresholdNode562 thresholdNode180
def thresholdNode564 : BoxExpr 1 := .mul ⟨(-1520011711673667053159/1180591620717411303424:ℚ),(-760005855836833526579/590295810358705651712:ℚ)⟩ thresholdNode402 thresholdNode182
def thresholdNode565 : BoxExpr 1 := .neg ⟨(760005855836833526579/590295810358705651712:ℚ),(1520011711673667053159/1180591620717411303424:ℚ)⟩ thresholdNode564
def thresholdNode566 : BoxExpr 1 := .add ⟨(1350301666195539178291/590295810358705651712:ℚ),(2700603332391078356583/1180591620717411303424:ℚ)⟩ thresholdNode12 thresholdNode565
def thresholdNode567 : BoxExpr 1 := .inv ⟨(1032211253086261248895/2361183241434822606848:ℚ),(2064422506172522497791/4722366482869645213696:ℚ)⟩ thresholdNode566
def thresholdNode568 : BoxExpr 1 := .mul ⟨(252591617341729801472579/2361183241434822606848:ℚ),(505183234683459602945535/4722366482869645213696:ℚ)⟩ thresholdNode563 thresholdNode567
def thresholdNode569 : BoxExpr 1 := .add ⟨(254952800583164624079427/2361183241434822606848:ℚ),(509905601166329248159231/4722366482869645213696:ℚ)⟩ thresholdNode568 thresholdNode12
def thresholdNode570 : BoxExpr 1 := .sqrt ⟨(49070980430141910034715/4722366482869645213696:ℚ),(24535490215070955017367/2361183241434822606848:ℚ)⟩ thresholdNode569
def thresholdNode571 : BoxExpr 1 := .add ⟨(53793346913011555248411/4722366482869645213696:ℚ),(26896673456505777624215/2361183241434822606848:ℚ)⟩ thresholdNode570 thresholdNode12
def thresholdNode572 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode573 : BoxExpr 1 := .mul ⟨(26896673456505777624205/4722366482869645213696:ℚ),(26896673456505777624215/4722366482869645213696:ℚ)⟩ thresholdNode571 thresholdNode572
def thresholdNode574 : BoxExpr 1 := .add ⟨(28077265077223188927629/4722366482869645213696:ℚ),(28077265077223188927639/4722366482869645213696:ℚ)⟩ thresholdNode573 thresholdNode193
def thresholdNode575 : BoxExpr 1 := .mul ⟨(25168361706087829441949/4722366482869645213696:ℚ),(25168361706087829441965/4722366482869645213696:ℚ)⟩ thresholdNode405 thresholdNode574
def thresholdNode576 : BoxExpr 1 := .neg ⟨(-25168361706087829441965/4722366482869645213696:ℚ),(-25168361706087829441949/4722366482869645213696:ℚ)⟩ thresholdNode575
def thresholdNode577 : BoxExpr 1 := .add ⟨(289830501375078522651/4722366482869645213696:ℚ),(36228812671884815345/590295810358705651712:ℚ)⟩ thresholdNode559 thresholdNode576
def thresholdNode578 : BoxExpr 1 := .mul ⟨(6070324253054847337805/2361183241434822606848:ℚ),(12140648506109694675675/4722366482869645213696:ℚ)⟩ thresholdNode453 thresholdNode415
def thresholdNode579 : BoxExpr 1 := .mul ⟨(6070324253054847337805/2361183241434822606848:ℚ),(12140648506109694675675/4722366482869645213696:ℚ)⟩ thresholdNode415 thresholdNode453
def thresholdNode580 : BoxExpr 1 := .add ⟨(6070324253054847337805/1180591620717411303424:ℚ),(12140648506109694675675/2361183241434822606848:ℚ)⟩ thresholdNode578 thresholdNode579
def thresholdNode581 : BoxExpr 1 := .mul ⟨(4518684848365606968039/1180591620717411303424:ℚ),(18074739393462427872175/4722366482869645213696:ℚ)⟩ thresholdNode434 thresholdNode574
def thresholdNode582 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode583 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode402 thresholdNode51
def thresholdNode584 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode582 thresholdNode583
def thresholdNode585 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode584
def thresholdNode586 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode585
def thresholdNode587 : BoxExpr 1 := .mul ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode586 thresholdNode180
def thresholdNode588 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode562 thresholdNode51
def thresholdNode589 : BoxExpr 1 := .add ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode587 thresholdNode588
def thresholdNode590 : BoxExpr 1 := .mul ⟨(-614671616344893813469757/4722366482869645213696:ℚ),(-614671616344893813469457/4722366482869645213696:ℚ)⟩ thresholdNode589 thresholdNode567
def thresholdNode591 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode12 thresholdNode182
def thresholdNode592 : BoxExpr 1 := .add ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode591 thresholdNode583
def thresholdNode593 : BoxExpr 1 := .neg ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode592
def thresholdNode594 : BoxExpr 1 := .add ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode51 thresholdNode593
def thresholdNode595 : BoxExpr 1 := .mul ⟨(24710520491378366962721/4722366482869645213696:ℚ),(6177630122844591740685/1180591620717411303424:ℚ)⟩ thresholdNode566 thresholdNode566
def thresholdNode596 : BoxExpr 1 := .inv ⟨(902479784119135518159/4722366482869645213696:ℚ),(902479784119135518161/4722366482869645213696:ℚ)⟩ thresholdNode595
def thresholdNode597 : BoxExpr 1 := .mul ⟨(-902479784119135518161/1180591620717411303424:ℚ),(-902479784119135518159/1180591620717411303424:ℚ)⟩ thresholdNode594 thresholdNode596
def thresholdNode598 : BoxExpr 1 := .neg ⟨(902479784119135518159/1180591620717411303424:ℚ),(902479784119135518161/1180591620717411303424:ℚ)⟩ thresholdNode597
def thresholdNode599 : BoxExpr 1 := .mul ⟨(883380519665065972362567/4722366482869645213696:ℚ),(883380519665065972364755/4722366482869645213696:ℚ)⟩ thresholdNode563 thresholdNode598
def thresholdNode600 : BoxExpr 1 := .add ⟨(134354451660086079446405/2361183241434822606848:ℚ),(134354451660086079447649/2361183241434822606848:ℚ)⟩ thresholdNode590 thresholdNode599
def thresholdNode601 : BoxExpr 1 := .add ⟨(134354451660086079446405/2361183241434822606848:ℚ),(134354451660086079447649/2361183241434822606848:ℚ)⟩ thresholdNode600 thresholdNode51
def thresholdNode602 : BoxExpr 1 := .mul ⟨(49070980430141910034715/2361183241434822606848:ℚ),(24535490215070955017367/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode570
def thresholdNode603 : BoxExpr 1 := .inv ⟨(227229464370273341807/4722366482869645213696:ℚ),(14201841523142083863/295147905179352825856:ℚ)⟩ thresholdNode602
def thresholdNode604 : BoxExpr 1 := .mul ⟨(12929657279767654654997/4722366482869645213696:ℚ),(6464828639883827327587/2361183241434822606848:ℚ)⟩ thresholdNode601 thresholdNode603
def thresholdNode605 : BoxExpr 1 := .add ⟨(12929657279767654654997/4722366482869645213696:ℚ),(6464828639883827327587/2361183241434822606848:ℚ)⟩ thresholdNode604 thresholdNode51
def thresholdNode606 : BoxExpr 1 := .mul ⟨(3232414319941913663749/2361183241434822606848:ℚ),(6464828639883827327587/4722366482869645213696:ℚ)⟩ thresholdNode605 thresholdNode572
def thresholdNode607 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode608 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode607
def thresholdNode609 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode608
def thresholdNode610 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode609
def thresholdNode611 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode571 thresholdNode610
def thresholdNode612 : BoxExpr 1 := .add ⟨(3232414319941913663749/2361183241434822606848:ℚ),(6464828639883827327587/4722366482869645213696:ℚ)⟩ thresholdNode606 thresholdNode611
def thresholdNode613 : BoxExpr 1 := .add ⟨(3232414319941913663749/2361183241434822606848:ℚ),(6464828639883827327587/4722366482869645213696:ℚ)⟩ thresholdNode612 thresholdNode51
def thresholdNode614 : BoxExpr 1 := .mul ⟨(5795049664878675724787/4722366482869645213696:ℚ),(2897524832439337862435/2361183241434822606848:ℚ)⟩ thresholdNode405 thresholdNode613
def thresholdNode615 : BoxExpr 1 := .add ⟨(23869789058341103596943/4722366482869645213696:ℚ),(23869789058341103597045/4722366482869645213696:ℚ)⟩ thresholdNode581 thresholdNode614
def thresholdNode616 : BoxExpr 1 := .neg ⟨(-23869789058341103597045/4722366482869645213696:ℚ),(-23869789058341103596943/4722366482869645213696:ℚ)⟩ thresholdNode615
def thresholdNode617 : BoxExpr 1 := .add ⟨(411507953878285754175/4722366482869645213696:ℚ),(411507953878285754407/4722366482869645213696:ℚ)⟩ thresholdNode580 thresholdNode616
def thresholdNode618 : BoxExpr 1 := .mul ⟨(-18899595357017324364765/4722366482869645213696:ℚ),(-12867008889465390990079/4722366482869645213696:ℚ)⟩ thresholdNode539 thresholdNode394
def thresholdNode619 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode482 thresholdNode385
def thresholdNode620 : BoxExpr 1 := .mul ⟨(3339312403445860743227/4722366482869645213696:ℚ),(5062214569756313931107/4722366482869645213696:ℚ)⟩ thresholdNode380 thresholdNode490
def thresholdNode621 : BoxExpr 1 := .add ⟨(3339312403445860743227/4722366482869645213696:ℚ),(5062214569756313931107/4722366482869645213696:ℚ)⟩ thresholdNode619 thresholdNode620
def thresholdNode622 : BoxExpr 1 := .mul ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode516 thresholdNode22
def thresholdNode623 : BoxExpr 1 := .add ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode622 thresholdNode519
def thresholdNode624 : BoxExpr 1 := .neg ⟨(1685884834384463341289/2361183241434822606848:ℚ),(3371769668768926682579/4722366482869645213696:ℚ)⟩ thresholdNode623
def thresholdNode625 : BoxExpr 1 := .add ⟨(6711082072214787425805/4722366482869645213696:ℚ),(4216992119262620306843/2361183241434822606848:ℚ)⟩ thresholdNode621 thresholdNode624
def thresholdNode626 : BoxExpr 1 := .mul ⟨(-173701920895678621837/295147905179352825856:ℚ),(-1852820489553905299591/4722366482869645213696:ℚ)⟩ thresholdNode533 thresholdNode27
def thresholdNode627 : BoxExpr 1 := .add ⟨(-173701920895678621837/295147905179352825856:ℚ),(-1852820489553905299591/4722366482869645213696:ℚ)⟩ thresholdNode626 thresholdNode536
def thresholdNode628 : BoxExpr 1 := .add ⟨(3931851337883929476413/4722366482869645213696:ℚ),(6581163748971335314095/4722366482869645213696:ℚ)⟩ thresholdNode625 thresholdNode627
def thresholdNode629 : BoxExpr 1 := .mul ⟨(3273666920875099796649/4722366482869645213696:ℚ),(9171612675104191956425/4722366482869645213696:ℚ)⟩ thresholdNode628 thresholdNode628
def thresholdNode630 : BoxExpr 1 := .add ⟨(-3906482109035556142029/1180591620717411303424:ℚ),(-1847698107180599516827/2361183241434822606848:ℚ)⟩ thresholdNode618 thresholdNode629
def thresholdNode631 : BoxExpr 1 := .mul ⟨(-18899595357017324364765/4722366482869645213696:ℚ),(-12867008889465390990079/4722366482869645213696:ℚ)⟩ thresholdNode394 thresholdNode539
def thresholdNode632 : BoxExpr 1 := .add ⟨(-3906482109035556142029/1180591620717411303424:ℚ),(-1847698107180599516827/2361183241434822606848:ℚ)⟩ thresholdNode629 thresholdNode631
def thresholdNode633 : BoxExpr 1 := .add ⟨(-3906482109035556142029/590295810358705651712:ℚ),(-1847698107180599516827/1180591620717411303424:ℚ)⟩ thresholdNode630 thresholdNode632
def thresholdNode634 : BoxExpr 1 := .mul ⟨(-30359044705182480268049/2361183241434822606848:ℚ),(-26055271889137921623231/2361183241434822606848:ℚ)⟩ thresholdNode500 thresholdNode555
def thresholdNode635 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode636 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode635 thresholdNode496
def thresholdNode637 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode636
def thresholdNode638 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode637
def thresholdNode639 : BoxExpr 1 := .mul ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode638 thresholdNode180
def thresholdNode640 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode543 thresholdNode51
def thresholdNode641 : BoxExpr 1 := .add ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode639 thresholdNode640
def thresholdNode642 : BoxExpr 1 := .mul ⟨(-685883571897046145518233/4722366482869645213696:ℚ),(-34803498078934272235431/295147905179352825856:ℚ)⟩ thresholdNode641 thresholdNode548
def thresholdNode643 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode12 thresholdNode182
def thresholdNode644 : BoxExpr 1 := .add ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode643 thresholdNode496
def thresholdNode645 : BoxExpr 1 := .neg ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode644
def thresholdNode646 : BoxExpr 1 := .add ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode51 thresholdNode645
def thresholdNode647 : BoxExpr 1 := .mul ⟨(9922872572129842005277/2361183241434822606848:ℚ),(30108037807345781765579/4722366482869645213696:ℚ)⟩ thresholdNode547 thresholdNode547
def thresholdNode648 : BoxExpr 1 := .inv ⟨(740690753121403033223/4722366482869645213696:ℚ),(1123704100623354006829/4722366482869645213696:ℚ)⟩ thresholdNode647
def thresholdNode649 : BoxExpr 1 := .mul ⟨(-1123704100623354006829/1180591620717411303424:ℚ),(-740690753121403033223/1180591620717411303424:ℚ)⟩ thresholdNode646 thresholdNode648
def thresholdNode650 : BoxExpr 1 := .neg ⟨(740690753121403033223/1180591620717411303424:ℚ),(1123704100623354006829/1180591620717411303424:ℚ)⟩ thresholdNode649
def thresholdNode651 : BoxExpr 1 := .mul ⟨(672637903466135637658653/4722366482869645213696:ℚ),(1179385166310774469732915/4722366482869645213696:ℚ)⟩ thresholdNode544 thresholdNode650
def thresholdNode652 : BoxExpr 1 := .add ⟨(-3311417107727626964895/1180591620717411303424:ℚ),(622529197047826113966019/4722366482869645213696:ℚ)⟩ thresholdNode642 thresholdNode651
def thresholdNode653 : BoxExpr 1 := .add ⟨(-3311417107727626964895/1180591620717411303424:ℚ),(622529197047826113966019/4722366482869645213696:ℚ)⟩ thresholdNode652 thresholdNode51
def thresholdNode654 : BoxExpr 1 := .mul ⟨(22513497026985687712959/1180591620717411303424:ℚ),(53634539686060492715553/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode551
def thresholdNode655 : BoxExpr 1 := .inv ⟨(103947686178830678285/2361183241434822606848:ℚ),(61909376994497870867/1180591620717411303424:ℚ)⟩ thresholdNode654
def thresholdNode656 : BoxExpr 1 := .mul ⟨(-173648335724898799193/1180591620717411303424:ℚ),(16322492076767424986849/2361183241434822606848:ℚ)⟩ thresholdNode653 thresholdNode655
def thresholdNode657 : BoxExpr 1 := .add ⟨(-173648335724898799193/1180591620717411303424:ℚ),(16322492076767424986849/2361183241434822606848:ℚ)⟩ thresholdNode656 thresholdNode51
def thresholdNode658 : BoxExpr 1 := .mul ⟨(-173648335724898799193/2361183241434822606848:ℚ),(16322492076767424986849/4722366482869645213696:ℚ)⟩ thresholdNode657 thresholdNode553
def thresholdNode659 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode660 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode659
def thresholdNode661 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode660
def thresholdNode662 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode661
def thresholdNode663 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode552 thresholdNode662
def thresholdNode664 : BoxExpr 1 := .add ⟨(-173648335724898799193/2361183241434822606848:ℚ),(16322492076767424986849/4722366482869645213696:ℚ)⟩ thresholdNode658 thresholdNode663
def thresholdNode665 : BoxExpr 1 := .add ⟨(-173648335724898799193/2361183241434822606848:ℚ),(16322492076767424986849/4722366482869645213696:ℚ)⟩ thresholdNode664 thresholdNode51
def thresholdNode666 : BoxExpr 1 := .mul ⟨(-132406855990235334385/2361183241434822606848:ℚ),(3111475052133790388119/1180591620717411303424:ℚ)⟩ thresholdNode487 thresholdNode665
def thresholdNode667 : BoxExpr 1 := .add ⟨(-15245725780586357801217/1180591620717411303424:ℚ),(-19832321784870340846993/2361183241434822606848:ℚ)⟩ thresholdNode634 thresholdNode666
def thresholdNode668 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode5
def thresholdNode669 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode12 thresholdNode51
def thresholdNode670 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode668 thresholdNode669
def thresholdNode671 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode669 thresholdNode496
def thresholdNode672 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode670 thresholdNode671
def thresholdNode673 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode672
def thresholdNode674 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode673
def thresholdNode675 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode674 thresholdNode180
def thresholdNode676 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode638 thresholdNode51
def thresholdNode677 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode675 thresholdNode676
def thresholdNode678 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode676 thresholdNode640
def thresholdNode679 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode677 thresholdNode678
def thresholdNode680 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode679 thresholdNode548
def thresholdNode681 : BoxExpr 1 := .mul ⟨(-1338309408579602235157789/4722366482869645213696:ℚ),(-882148070119522147749103/4722366482869645213696:ℚ)⟩ thresholdNode641 thresholdNode650
def thresholdNode682 : BoxExpr 1 := .add ⟨(-1338309408579602235157789/4722366482869645213696:ℚ),(-882148070119522147749103/4722366482869645213696:ℚ)⟩ thresholdNode680 thresholdNode681
def thresholdNode683 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode182
def thresholdNode684 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode683 thresholdNode669
def thresholdNode685 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode684 thresholdNode671
def thresholdNode686 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode685
def thresholdNode687 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode686
def thresholdNode688 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode687 thresholdNode648
def thresholdNode689 : BoxExpr 1 := .mul ⟨(-1490496921155731770573/147573952589676412928:ℚ),(-2420212822470693172019/295147905179352825856:ℚ)⟩ thresholdNode646 thresholdNode547
def thresholdNode690 : BoxExpr 1 := .mul ⟨(-1490496921155731770573/147573952589676412928:ℚ),(-2420212822470693172019/295147905179352825856:ℚ)⟩ thresholdNode547 thresholdNode646
def thresholdNode691 : BoxExpr 1 := .add ⟨(-1490496921155731770573/73786976294838206464:ℚ),(-2420212822470693172019/147573952589676412928:ℚ)⟩ thresholdNode689 thresholdNode690
def thresholdNode692 : BoxExpr 1 := .mul ⟨(41700871984375661027169/2361183241434822606848:ℚ),(23994694818182368733653/590295810358705651712:ℚ)⟩ thresholdNode647 thresholdNode647
def thresholdNode693 : BoxExpr 1 := .inv ⟨(116175395058743736217/4722366482869645213696:ℚ),(133694717504265794983/2361183241434822606848:ℚ)⟩ thresholdNode692
def thresholdNode694 : BoxExpr 1 := .mul ⟨(-2700633293586169058657/2361183241434822606848:ℚ),(-952638239481698636979/2361183241434822606848:ℚ)⟩ thresholdNode691 thresholdNode693
def thresholdNode695 : BoxExpr 1 := .neg ⟨(952638239481698636979/2361183241434822606848:ℚ),(2700633293586169058657/2361183241434822606848:ℚ)⟩ thresholdNode694
def thresholdNode696 : BoxExpr 1 := .mul ⟨(-2700633293586169058657/590295810358705651712:ℚ),(-952638239481698636979/590295810358705651712:ℚ)⟩ thresholdNode646 thresholdNode695
def thresholdNode697 : BoxExpr 1 := .add ⟨(-2700633293586169058657/590295810358705651712:ℚ),(-952638239481698636979/590295810358705651712:ℚ)⟩ thresholdNode688 thresholdNode696
def thresholdNode698 : BoxExpr 1 := .neg ⟨(952638239481698636979/590295810358705651712:ℚ),(2700633293586169058657/590295810358705651712:ℚ)⟩ thresholdNode697
def thresholdNode699 : BoxExpr 1 := .mul ⟨(865112174637359039900435/2361183241434822606848:ℚ),(2834453344375686411502017/2361183241434822606848:ℚ)⟩ thresholdNode544 thresholdNode698
def thresholdNode700 : BoxExpr 1 := .add ⟨(391914940695115844643081/4722366482869645213696:ℚ),(4786758618631850675254931/4722366482869645213696:ℚ)⟩ thresholdNode681 thresholdNode699
def thresholdNode701 : BoxExpr 1 := .add ⟨(-236598616971121597628677/1180591620717411303424:ℚ),(976152637128082131876457/1180591620717411303424:ℚ)⟩ thresholdNode682 thresholdNode700
def thresholdNode702 : BoxExpr 1 := .add ⟨(-236598616971121597628677/1180591620717411303424:ℚ),(976152637128082131876457/1180591620717411303424:ℚ)⟩ thresholdNode701 thresholdNode51
def thresholdNode703 : BoxExpr 1 := .mul ⟨(-49628246439834979400953/4722366482869645213696:ℚ),(102377486940678662368641/2361183241434822606848:ℚ)⟩ thresholdNode702 thresholdNode655
def thresholdNode704 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode551
def thresholdNode705 : BoxExpr 1 := .mul ⟨(-173648335724898799193/590295810358705651712:ℚ),(16322492076767424986849/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode656
def thresholdNode706 : BoxExpr 1 := .add ⟨(-173648335724898799193/590295810358705651712:ℚ),(16322492076767424986849/1180591620717411303424:ℚ)⟩ thresholdNode704 thresholdNode705
def thresholdNode707 : BoxExpr 1 := .mul ⟨(1717300172183471065943717/4722366482869645213696:ℚ),(2436629056868566243806827/4722366482869645213696:ℚ)⟩ thresholdNode654 thresholdNode654
def thresholdNode708 : BoxExpr 1 := .inv ⟨(2288073469335380201/1180591620717411303424:ℚ),(12985933129079125341/4722366482869645213696:ℚ)⟩ thresholdNode707
def thresholdNode709 : BoxExpr 1 := .mul ⟨(-1910047162903907539/2361183241434822606848:ℚ),(179539467237639713985/4722366482869645213696:ℚ)⟩ thresholdNode706 thresholdNode708
def thresholdNode710 : BoxExpr 1 := .neg ⟨(-179539467237639713985/4722366482869645213696:ℚ),(1910047162903907539/2361183241434822606848:ℚ)⟩ thresholdNode709
def thresholdNode711 : BoxExpr 1 := .mul ⟨(-5916978319200875547621/1180591620717411303424:ℚ),(62948318970973347283/590295810358705651712:ℚ)⟩ thresholdNode653 thresholdNode710
def thresholdNode712 : BoxExpr 1 := .add ⟨(-73296159716638481591437/4722366482869645213696:ℚ),(102629280216562555757773/2361183241434822606848:ℚ)⟩ thresholdNode703 thresholdNode711
def thresholdNode713 : BoxExpr 1 := .add ⟨(-73296159716638481591437/4722366482869645213696:ℚ),(102629280216562555757773/2361183241434822606848:ℚ)⟩ thresholdNode712 thresholdNode51
def thresholdNode714 : BoxExpr 1 := .mul ⟨(-36648079858319240795719/4722366482869645213696:ℚ),(102629280216562555757773/4722366482869645213696:ℚ)⟩ thresholdNode713 thresholdNode553
def thresholdNode715 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode657 thresholdNode662
def thresholdNode716 : BoxExpr 1 := .add ⟨(-36648079858319240795719/4722366482869645213696:ℚ),(102629280216562555757773/4722366482869645213696:ℚ)⟩ thresholdNode714 thresholdNode715
def thresholdNode717 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode5 thresholdNode51
def thresholdNode718 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode668 thresholdNode717
def thresholdNode719 : BoxExpr 1 := .mul ⟨(16/1:ℚ),(16/1:ℚ)⟩ thresholdNode659 thresholdNode659
def thresholdNode720 : BoxExpr 1 := .inv ⟨(1/16:ℚ),(1/16:ℚ)⟩ thresholdNode719
def thresholdNode721 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode718 thresholdNode720
def thresholdNode722 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode721
def thresholdNode723 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode722
def thresholdNode724 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode661 thresholdNode723
def thresholdNode725 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode724
def thresholdNode726 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode552 thresholdNode725
def thresholdNode727 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode715 thresholdNode726
def thresholdNode728 : BoxExpr 1 := .add ⟨(-36648079858319240795719/4722366482869645213696:ℚ),(102629280216562555757773/4722366482869645213696:ℚ)⟩ thresholdNode716 thresholdNode727
def thresholdNode729 : BoxExpr 1 := .add ⟨(-36648079858319240795719/4722366482869645213696:ℚ),(102629280216562555757773/4722366482869645213696:ℚ)⟩ thresholdNode728 thresholdNode51
def thresholdNode730 : BoxExpr 1 := .mul ⟨(-34122798105581930609641/4722366482869645213696:ℚ),(95557481376640042150095/4722366482869645213696:ℚ)⟩ thresholdNode384 thresholdNode729
def thresholdNode731 : BoxExpr 1 := .add ⟨(-34387611817562401278411/4722366482869645213696:ℚ),(108003381585175203702571/4722366482869645213696:ℚ)⟩ thresholdNode666 thresholdNode730
def thresholdNode732 : BoxExpr 1 := .add ⟨(-95370514939907832483279/4722366482869645213696:ℚ),(68338738015434522008585/4722366482869645213696:ℚ)⟩ thresholdNode667 thresholdNode731
def thresholdNode733 : BoxExpr 1 := .neg ⟨(-68338738015434522008585/4722366482869645213696:ℚ),(95370514939907832483279/4722366482869645213696:ℚ)⟩ thresholdNode732
def thresholdNode734 : BoxExpr 1 := .add ⟨(-99590594887718971144817/4722366482869645213696:ℚ),(87979722511185434415971/4722366482869645213696:ℚ)⟩ thresholdNode633 thresholdNode733
def thresholdCell1Out1 : TaylorCertificate1 :=
  { center := (-103/320:ℚ), radius := (19/320:ℚ)
    whole := thresholdNode558, centerValue := thresholdNode577, gradient := thresholdNode617, hessian := thresholdNode734 }
theorem thresholdCell1Out1_check : thresholdCell1Out1.check = true := by decide +kernel
theorem thresholdCell1Out1_lower_pos : 0 < thresholdCell1Out1.lower := by decide +kernel
theorem thresholdCell1Out1_positive (x : ℝ) (hx : (-(61/160:ℝ)) ≤ x ∧ x ≤ (-(21/80:ℝ))) :
    0 < thresholdNode558.eval (fun _ => x) := by
  apply thresholdCell1Out1.positive_sound thresholdCell1Out1_check thresholdCell1Out1_lower_pos x
  norm_num [thresholdCell1Out1]
  exact hx
theorem thresholdCell1_public (x : ℝ)
    (hx : (-(61/160:ℝ)) ≤ x ∧ x ≤ (-(21/80:ℝ))) : qc x < fA (43/20) x := by
  have hf := thresholdCell1Out0_positive x hx
  have hg := thresholdCell1Out1_positive x hx
  have hfa : thresholdNode394.eval (fun _ => x) = thresholdFA 0 x := by
    norm_num [thresholdNode0, thresholdNode1, thresholdNode374, thresholdNode3, thresholdNode375, thresholdNode5, thresholdNode376, thresholdNode377, thresholdNode378, thresholdNode9, thresholdNode379, thresholdNode380, thresholdNode12, thresholdNode381, thresholdNode382, thresholdNode383, thresholdNode384, thresholdNode385, thresholdNode386, thresholdNode19, thresholdNode387, thresholdNode388, thresholdNode22, thresholdNode389, thresholdNode390, thresholdNode391, thresholdNode392, thresholdNode27, thresholdNode393, thresholdNode394, BoxExpr.eval, thresholdFA, ftilde, pow_two, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  have hgap : thresholdNode558.eval (fun _ => x) =
      (thresholdNode394.eval (fun _ => x))^2 - (1-x^2)*(thresholdCapacity 1 x+1/4) := by
    norm_num [thresholdNode540, thresholdNode12, thresholdNode381, thresholdNode382, thresholdNode383, thresholdNode384, thresholdNode5, thresholdNode541, thresholdNode542, thresholdNode543, thresholdNode180, thresholdNode544, thresholdNode182, thresholdNode545, thresholdNode546, thresholdNode547, thresholdNode548, thresholdNode549, thresholdNode550, thresholdNode551, thresholdNode552, thresholdNode553, thresholdNode554, thresholdNode193, thresholdNode555, thresholdNode556, thresholdNode557, thresholdNode558, BoxExpr.eval, thresholdCapacity, Da, D5, beta5, eta5, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  rw [hfa] at hf
  rw [hgap, hfa] at hg
  refine threshold_positive_to_public 0 1 x ?_ ?_ ?_ hf hg
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdFADomain] <;> constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdCapacityDomain] <;> linarith [hx.1,hx.2]
def thresholdNode735 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode736 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode735 thresholdNode3
def thresholdNode737 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode738 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode737
def thresholdNode739 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode738 thresholdNode738
def thresholdNode740 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode739 thresholdNode9
def thresholdNode741 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode736 thresholdNode740
def thresholdNode742 : BoxExpr 1 := .var 0
def thresholdNode743 : BoxExpr 1 := .mul ⟨(169/4096:ℚ),(325400565460236490507/4722366482869645213696:ℚ)⟩ thresholdNode742 thresholdNode742
def thresholdNode744 : BoxExpr 1 := .neg ⟨(-325400565460236490507/4722366482869645213696:ℚ),(-169/4096:ℚ)⟩ thresholdNode743
def thresholdNode745 : BoxExpr 1 := .add ⟨(4396965917409408723189/4722366482869645213696:ℚ),(3927/4096:ℚ)⟩ thresholdNode12 thresholdNode744
def thresholdNode746 : BoxExpr 1 := .sqrt ⟨(4556762499263525627037/4722366482869645213696:ℚ),(577989804170135285359/590295810358705651712:ℚ)⟩ thresholdNode745
def thresholdNode747 : BoxExpr 1 := .mul ⟨(5922310301230322669317/2361183241434822606848:ℚ),(3004795594939282307997/1180591620717411303424:ℚ)⟩ thresholdNode741 thresholdNode746
def thresholdNode748 : BoxExpr 1 := .neg ⟨(13/64:ℚ),(309905300438320467149/1180591620717411303424:ℚ)⟩ thresholdNode742
def thresholdNode749 : BoxExpr 1 := .add ⟨(841171529761155553689/4722366482869645213696:ℚ),(560781019840770369127/2361183241434822606848:ℚ)⟩ thresholdNode19 thresholdNode748
def thresholdNode750 : BoxExpr 1 := .mul ⟨(600596472249465065333/4722366482869645213696:ℚ),(400397648166310043557/2361183241434822606848:ℚ)⟩ thresholdNode749 thresholdNode22
def thresholdNode751 : BoxExpr 1 := .neg ⟨(-400397648166310043557/2361183241434822606848:ℚ),(-600596472249465065333/4722366482869645213696:ℚ)⟩ thresholdNode750
def thresholdNode752 : BoxExpr 1 := .add ⟨(172559770408250394555/73786976294838206464:ℚ),(11418585907507664166655/4722366482869645213696:ℚ)⟩ thresholdNode747 thresholdNode751
def thresholdNode753 : BoxExpr 1 := .mul ⟨(18729209842338229125/590295810358705651712:ℚ),(33296373053045740667/590295810358705651712:ℚ)⟩ thresholdNode749 thresholdNode749
def thresholdNode754 : BoxExpr 1 := .mul ⟨(123762618638171018057/4722366482869645213696:ℚ),(27502804141815781791/590295810358705651712:ℚ)⟩ thresholdNode753 thresholdNode27
def thresholdNode755 : BoxExpr 1 := .add ⟨(11167587924766196269577/4722366482869645213696:ℚ),(11638608340642190420983/4722366482869645213696:ℚ)⟩ thresholdNode752 thresholdNode754
def thresholdNode756 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode757 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode756 thresholdNode3
def thresholdNode758 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode759 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode758
def thresholdNode760 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode759 thresholdNode759
def thresholdNode761 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode760 thresholdNode9
def thresholdNode762 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode757 thresholdNode761
def thresholdNode763 : BoxExpr 1 := .var 0
def thresholdNode764 : BoxExpr 1 := .mul ⟨(255960103237766097141/4722366482869645213696:ℚ),(127980051618883048571/2361183241434822606848:ℚ)⟩ thresholdNode763 thresholdNode763
def thresholdNode765 : BoxExpr 1 := .neg ⟨(-127980051618883048571/2361183241434822606848:ℚ),(-255960103237766097141/4722366482869645213696:ℚ)⟩ thresholdNode764
def thresholdNode766 : BoxExpr 1 := .add ⟨(2233203189815939558277/2361183241434822606848:ℚ),(4466406379631879116555/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode765
def thresholdNode767 : BoxExpr 1 := .sqrt ⟨(4592603595570680468649/4722366482869645213696:ℚ),(4592603595570680468651/4722366482869645213696:ℚ)⟩ thresholdNode766
def thresholdNode768 : BoxExpr 1 := .mul ⟨(5968892078073324138089/2361183241434822606848:ℚ),(11937784156146648276193/4722366482869645213696:ℚ)⟩ thresholdNode762 thresholdNode767
def thresholdNode769 : BoxExpr 1 := .neg ⟨(1099425946793089276313/4722366482869645213696:ℚ),(549712973396544638157/2361183241434822606848:ℚ)⟩ thresholdNode763
def thresholdNode770 : BoxExpr 1 := .add ⟨(490683392360674072985/2361183241434822606848:ℚ),(245341696180337036493/1180591620717411303424:ℚ)⟩ thresholdNode19 thresholdNode769
def thresholdNode771 : BoxExpr 1 := .mul ⟨(350347942145521288111/2361183241434822606848:ℚ),(700695884291042576225/4722366482869645213696:ℚ)⟩ thresholdNode770 thresholdNode22
def thresholdNode772 : BoxExpr 1 := .neg ⟨(-700695884291042576225/4722366482869645213696:ℚ),(-350347942145521288111/2361183241434822606848:ℚ)⟩ thresholdNode771
def thresholdNode773 : BoxExpr 1 := .add ⟨(11237088271855605699953/4722366482869645213696:ℚ),(11237088271855605699971/4722366482869645213696:ℚ)⟩ thresholdNode768 thresholdNode772
def thresholdNode774 : BoxExpr 1 := .mul ⟨(12746267809369072599/295147905179352825856:ℚ),(203940284949905161585/4722366482869645213696:ℚ)⟩ thresholdNode770 thresholdNode770
def thresholdNode775 : BoxExpr 1 := .mul ⟨(42113668842155415867/1180591620717411303424:ℚ),(84227337684310831735/2361183241434822606848:ℚ)⟩ thresholdNode774 thresholdNode27
def thresholdNode776 : BoxExpr 1 := .add ⟨(11405542947224227363421/4722366482869645213696:ℚ),(11405542947224227363441/4722366482869645213696:ℚ)⟩ thresholdNode773 thresholdNode775
def thresholdNode777 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1
def thresholdNode778 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode51
def thresholdNode779 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode777 thresholdNode778
def thresholdNode780 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode779 thresholdNode51
def thresholdNode781 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51
def thresholdNode782 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode781
def thresholdNode783 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode782 thresholdNode759
def thresholdNode784 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode759 thresholdNode782
def thresholdNode785 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode783 thresholdNode784
def thresholdNode786 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode785 thresholdNode9
def thresholdNode787 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode760 thresholdNode51
def thresholdNode788 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode786 thresholdNode787
def thresholdNode789 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode780 thresholdNode788
def thresholdNode790 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode789 thresholdNode767
def thresholdNode791 : BoxExpr 1 := .mul ⟨(-549712973396544638157/2361183241434822606848:ℚ),(-1099425946793089276313/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode763
def thresholdNode792 : BoxExpr 1 := .mul ⟨(-549712973396544638157/2361183241434822606848:ℚ),(-1099425946793089276313/4722366482869645213696:ℚ)⟩ thresholdNode763 thresholdNode12
def thresholdNode793 : BoxExpr 1 := .add ⟨(-549712973396544638157/1180591620717411303424:ℚ),(-1099425946793089276313/2361183241434822606848:ℚ)⟩ thresholdNode791 thresholdNode792
def thresholdNode794 : BoxExpr 1 := .neg ⟨(1099425946793089276313/2361183241434822606848:ℚ),(549712973396544638157/1180591620717411303424:ℚ)⟩ thresholdNode793
def thresholdNode795 : BoxExpr 1 := .add ⟨(1099425946793089276313/2361183241434822606848:ℚ),(549712973396544638157/1180591620717411303424:ℚ)⟩ thresholdNode51 thresholdNode794
def thresholdNode796 : BoxExpr 1 := .mul ⟨(4592603595570680468649/2361183241434822606848:ℚ),(4592603595570680468651/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode767
def thresholdNode797 : BoxExpr 1 := .inv ⟨(303487236793614387227/590295810358705651712:ℚ),(2427897894348915097819/4722366482869645213696:ℚ)⟩ thresholdNode796
def thresholdNode798 : BoxExpr 1 := .mul ⟨(1130489957056213592419/4722366482869645213696:ℚ),(1130489957056213592423/4722366482869645213696:ℚ)⟩ thresholdNode795 thresholdNode797
def thresholdNode799 : BoxExpr 1 := .mul ⟨(2938539069874068801453/4722366482869645213696:ℚ),(1469269534937034400733/2361183241434822606848:ℚ)⟩ thresholdNode762 thresholdNode798
def thresholdNode800 : BoxExpr 1 := .add ⟨(2938539069874068801453/4722366482869645213696:ℚ),(1469269534937034400733/2361183241434822606848:ℚ)⟩ thresholdNode790 thresholdNode799
def thresholdNode801 : BoxExpr 1 := .neg ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode12
def thresholdNode802 : BoxExpr 1 := .add ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode51 thresholdNode801
def thresholdNode803 : BoxExpr 1 := .mul ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode802 thresholdNode22
def thresholdNode804 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode770 thresholdNode51
def thresholdNode805 : BoxExpr 1 := .add ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode803 thresholdNode804
def thresholdNode806 : BoxExpr 1 := .neg ⟨(1685884834384463341289/2361183241434822606848:ℚ),(3371769668768926682579/4722366482869645213696:ℚ)⟩ thresholdNode805
def thresholdNode807 : BoxExpr 1 := .add ⟨(6310308738642995484031/4722366482869645213696:ℚ),(6310308738642995484045/4722366482869645213696:ℚ)⟩ thresholdNode800 thresholdNode806
def thresholdNode808 : BoxExpr 1 := .mul ⟨(-245341696180337036493/1180591620717411303424:ℚ),(-490683392360674072985/2361183241434822606848:ℚ)⟩ thresholdNode802 thresholdNode770
def thresholdNode809 : BoxExpr 1 := .mul ⟨(-245341696180337036493/1180591620717411303424:ℚ),(-490683392360674072985/2361183241434822606848:ℚ)⟩ thresholdNode770 thresholdNode802
def thresholdNode810 : BoxExpr 1 := .add ⟨(-245341696180337036493/590295810358705651712:ℚ),(-490683392360674072985/1180591620717411303424:ℚ)⟩ thresholdNode808 thresholdNode809
def thresholdNode811 : BoxExpr 1 := .mul ⟨(-810608964179833568573/2361183241434822606848:ℚ),(-810608964179833568571/2361183241434822606848:ℚ)⟩ thresholdNode810 thresholdNode27
def thresholdNode812 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode774 thresholdNode51
def thresholdNode813 : BoxExpr 1 := .add ⟨(-810608964179833568573/2361183241434822606848:ℚ),(-810608964179833568571/2361183241434822606848:ℚ)⟩ thresholdNode811 thresholdNode812
def thresholdNode814 : BoxExpr 1 := .add ⟨(4689090810283328346885/4722366482869645213696:ℚ),(4689090810283328346903/4722366482869645213696:ℚ)⟩ thresholdNode807 thresholdNode813
def thresholdNode815 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1
def thresholdNode816 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode51
def thresholdNode817 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode815 thresholdNode816
def thresholdNode818 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode51
def thresholdNode819 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode816 thresholdNode818
def thresholdNode820 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode817 thresholdNode819
def thresholdNode821 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode820 thresholdNode51
def thresholdNode822 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51
def thresholdNode823 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode822
def thresholdNode824 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode823 thresholdNode738
def thresholdNode825 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode823 thresholdNode823
def thresholdNode826 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode824 thresholdNode825
def thresholdNode827 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode738 thresholdNode823
def thresholdNode828 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode825 thresholdNode827
def thresholdNode829 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode826 thresholdNode828
def thresholdNode830 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode829 thresholdNode9
def thresholdNode831 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode824 thresholdNode827
def thresholdNode832 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode831 thresholdNode51
def thresholdNode833 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode830 thresholdNode832
def thresholdNode834 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode739 thresholdNode51
def thresholdNode835 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode832 thresholdNode834
def thresholdNode836 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode833 thresholdNode835
def thresholdNode837 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode821 thresholdNode836
def thresholdNode838 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode837 thresholdNode746
def thresholdNode839 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode815 thresholdNode818
def thresholdNode840 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode839 thresholdNode51
def thresholdNode841 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode831 thresholdNode9
def thresholdNode842 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode841 thresholdNode834
def thresholdNode843 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode840 thresholdNode842
def thresholdNode844 : BoxExpr 1 := .mul ⟨(-309905300438320467149/1180591620717411303424:ℚ),(-13/64:ℚ)⟩ thresholdNode12 thresholdNode742
def thresholdNode845 : BoxExpr 1 := .mul ⟨(-309905300438320467149/1180591620717411303424:ℚ),(-13/64:ℚ)⟩ thresholdNode742 thresholdNode12
def thresholdNode846 : BoxExpr 1 := .add ⟨(-309905300438320467149/590295810358705651712:ℚ),(-13/32:ℚ)⟩ thresholdNode844 thresholdNode845
def thresholdNode847 : BoxExpr 1 := .neg ⟨(13/32:ℚ),(309905300438320467149/590295810358705651712:ℚ)⟩ thresholdNode846
def thresholdNode848 : BoxExpr 1 := .add ⟨(13/32:ℚ),(309905300438320467149/590295810358705651712:ℚ)⟩ thresholdNode51 thresholdNode847
def thresholdNode849 : BoxExpr 1 := .mul ⟨(4556762499263525627037/2361183241434822606848:ℚ),(577989804170135285359/295147905179352825856:ℚ)⟩ thresholdNode5 thresholdNode746
def thresholdNode850 : BoxExpr 1 := .inv ⟨(150715956065754655515/295147905179352825856:ℚ),(2446994461762591375487/4722366482869645213696:ℚ)⟩ thresholdNode849
def thresholdNode851 : BoxExpr 1 := .mul ⟨(979653714427405260847/4722366482869645213696:ℚ),(321168023106340118033/1180591620717411303424:ℚ)⟩ thresholdNode848 thresholdNode850
def thresholdNode852 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode843 thresholdNode851
def thresholdNode853 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode838 thresholdNode852
def thresholdNode854 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode742
def thresholdNode855 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode12
def thresholdNode856 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode854 thresholdNode855
def thresholdNode857 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode742 thresholdNode51
def thresholdNode858 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode855 thresholdNode857
def thresholdNode859 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode856 thresholdNode858
def thresholdNode860 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode859
def thresholdNode861 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode860
def thresholdNode862 : BoxExpr 1 := .mul ⟨(-2446994461762591375487/2361183241434822606848:ℚ),(-150715956065754655515/147573952589676412928:ℚ)⟩ thresholdNode861 thresholdNode850
def thresholdNode863 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode746
def thresholdNode864 : BoxExpr 1 := .mul ⟨(979653714427405260847/2361183241434822606848:ℚ),(321168023106340118033/590295810358705651712:ℚ)⟩ thresholdNode5 thresholdNode851
def thresholdNode865 : BoxExpr 1 := .add ⟨(979653714427405260847/2361183241434822606848:ℚ),(321168023106340118033/590295810358705651712:ℚ)⟩ thresholdNode863 thresholdNode864
def thresholdNode866 : BoxExpr 1 := .mul ⟨(17587863669637634892755/4722366482869645213696:ℚ),(18110090994364352299011/4722366482869645213696:ℚ)⟩ thresholdNode849 thresholdNode849
def thresholdNode867 : BoxExpr 1 := .inv ⟨(1231398848601608530385/4722366482869645213696:ℚ),(316990534174837738795/1180591620717411303424:ℚ)⟩ thresholdNode866
def thresholdNode868 : BoxExpr 1 := .mul ⟨(255453374986927167585/2361183241434822606848:ℚ),(689872578580492282401/4722366482869645213696:ℚ)⟩ thresholdNode865 thresholdNode867
def thresholdNode869 : BoxExpr 1 := .neg ⟨(-689872578580492282401/4722366482869645213696:ℚ),(-255453374986927167585/2361183241434822606848:ℚ)⟩ thresholdNode868
def thresholdNode870 : BoxExpr 1 := .mul ⟨(-362183103754758448261/4722366482869645213696:ℚ),(-103777933588439161831/2361183241434822606848:ℚ)⟩ thresholdNode848 thresholdNode869
def thresholdNode871 : BoxExpr 1 := .add ⟨(-5256172027279941199235/4722366482869645213696:ℚ),(-2515233230640513650071/2361183241434822606848:ℚ)⟩ thresholdNode862 thresholdNode870
def thresholdNode872 : BoxExpr 1 := .mul ⟨(-13662630759110115156237/4722366482869645213696:ℚ),(-13075942996130838312619/4722366482869645213696:ℚ)⟩ thresholdNode741 thresholdNode871
def thresholdNode873 : BoxExpr 1 := .add ⟨(-13662630759110115156237/4722366482869645213696:ℚ),(-13075942996130838312619/4722366482869645213696:ℚ)⟩ thresholdNode852 thresholdNode872
def thresholdNode874 : BoxExpr 1 := .add ⟨(-13662630759110115156237/4722366482869645213696:ℚ),(-13075942996130838312619/4722366482869645213696:ℚ)⟩ thresholdNode853 thresholdNode873
def thresholdNode875 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode823 thresholdNode22
def thresholdNode876 : BoxExpr 1 := .neg ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode12
def thresholdNode877 : BoxExpr 1 := .add ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode51 thresholdNode876
def thresholdNode878 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode877 thresholdNode51
def thresholdNode879 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode875 thresholdNode878
def thresholdNode880 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode749 thresholdNode51
def thresholdNode881 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode878 thresholdNode880
def thresholdNode882 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode879 thresholdNode881
def thresholdNode883 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode882
def thresholdNode884 : BoxExpr 1 := .add ⟨(-13662630759110115156237/4722366482869645213696:ℚ),(-13075942996130838312619/4722366482869645213696:ℚ)⟩ thresholdNode874 thresholdNode883
def thresholdNode885 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode823 thresholdNode749
def thresholdNode886 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode877 thresholdNode877
def thresholdNode887 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode885 thresholdNode886
def thresholdNode888 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode749 thresholdNode823
def thresholdNode889 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode886 thresholdNode888
def thresholdNode890 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode887 thresholdNode889
def thresholdNode891 : BoxExpr 1 := .mul ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode890 thresholdNode27
def thresholdNode892 : BoxExpr 1 := .mul ⟨(-560781019840770369127/2361183241434822606848:ℚ),(-841171529761155553689/4722366482869645213696:ℚ)⟩ thresholdNode877 thresholdNode749
def thresholdNode893 : BoxExpr 1 := .mul ⟨(-560781019840770369127/2361183241434822606848:ℚ),(-841171529761155553689/4722366482869645213696:ℚ)⟩ thresholdNode749 thresholdNode877
def thresholdNode894 : BoxExpr 1 := .add ⟨(-560781019840770369127/1180591620717411303424:ℚ),(-841171529761155553689/2361183241434822606848:ℚ)⟩ thresholdNode892 thresholdNode893
def thresholdNode895 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode894 thresholdNode51
def thresholdNode896 : BoxExpr 1 := .add ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode891 thresholdNode895
def thresholdNode897 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode753 thresholdNode51
def thresholdNode898 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode895 thresholdNode897
def thresholdNode899 : BoxExpr 1 := .add ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode896 thresholdNode898
def thresholdNode900 : BoxExpr 1 := .add ⟨(-5861281329409461263213/4722366482869645213696:ℚ),(-5274593566430184419593/4722366482869645213696:ℚ)⟩ thresholdNode884 thresholdNode899
def thresholdCell2Out0 : TaylorCertificate1 :=
  { center := (-149/640:ℚ), radius := (19/640:ℚ)
    whole := thresholdNode755, centerValue := thresholdNode776, gradient := thresholdNode814, hessian := thresholdNode900 }
theorem thresholdCell2Out0_check : thresholdCell2Out0.check = true := by decide +kernel
theorem thresholdCell2Out0_lower_pos : 0 < thresholdCell2Out0.lower := by decide +kernel
theorem thresholdCell2Out0_positive (x : ℝ) (hx : (-(21/80:ℝ)) ≤ x ∧ x ≤ (-(13/64:ℝ))) :
    0 < thresholdNode755.eval (fun _ => x) := by
  apply thresholdCell2Out0.positive_sound thresholdCell2Out0_check thresholdCell2Out0_lower_pos x
  norm_num [thresholdCell2Out0]
  exact hx
def thresholdNode901 : BoxExpr 1 := .mul ⟨(3301179093940154553079/590295810358705651712:ℚ),(28684178705366497741361/4722366482869645213696:ℚ)⟩ thresholdNode755 thresholdNode755
def thresholdNode902 : BoxExpr 1 := .mul ⟨(-309905300438320467149/590295810358705651712:ℚ),(-13/32:ℚ)⟩ thresholdNode742 thresholdNode5
def thresholdNode903 : BoxExpr 1 := .neg ⟨(13/32:ℚ),(309905300438320467149/590295810358705651712:ℚ)⟩ thresholdNode902
def thresholdNode904 : BoxExpr 1 := .add ⟨(45/32:ℚ),(900201110797026118861/590295810358705651712:ℚ)⟩ thresholdNode12 thresholdNode903
def thresholdNode905 : BoxExpr 1 := .mul ⟨(247159216826181667671995/1180591620717411303424:ℚ),(1072121758321570256212983/4722366482869645213696:ℚ)⟩ thresholdNode904 thresholdNode180
def thresholdNode906 : BoxExpr 1 := .mul ⟨(-309905300438320467149/295147905179352825856:ℚ),(-13/16:ℚ)⟩ thresholdNode742 thresholdNode182
def thresholdNode907 : BoxExpr 1 := .neg ⟨(13/16:ℚ),(309905300438320467149/295147905179352825856:ℚ)⟩ thresholdNode906
def thresholdNode908 : BoxExpr 1 := .add ⟨(29/16:ℚ),(605053205617673293005/295147905179352825856:ℚ)⟩ thresholdNode12 thresholdNode907
def thresholdNode909 : BoxExpr 1 := .inv ⟨(2303593406277875713997/4722366482869645213696:ℚ),(1302721788377833162399/2361183241434822606848:ℚ)⟩ thresholdNode908
def thresholdNode910 : BoxExpr 1 := .mul ⟨(482261886490110571067087/4722366482869645213696:ℚ),(591515452867073244807211/4722366482869645213696:ℚ)⟩ thresholdNode905 thresholdNode909
def thresholdNode911 : BoxExpr 1 := .add ⟨(486984252972980216280783/4722366482869645213696:ℚ),(596237819349942890020907/4722366482869645213696:ℚ)⟩ thresholdNode910 thresholdNode12
def thresholdNode912 : BoxExpr 1 := .sqrt ⟨(47955376277586584585453/4722366482869645213696:ℚ),(13265682921351657410191/1180591620717411303424:ℚ)⟩ thresholdNode911
def thresholdNode913 : BoxExpr 1 := .add ⟨(52677742760456229799149/4722366482869645213696:ℚ),(14446274542069068713615/1180591620717411303424:ℚ)⟩ thresholdNode912 thresholdNode12
def thresholdNode914 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode915 : BoxExpr 1 := .mul ⟨(13169435690114057449787/2361183241434822606848:ℚ),(14446274542069068713615/2361183241434822606848:ℚ)⟩ thresholdNode913 thresholdNode914
def thresholdNode916 : BoxExpr 1 := .add ⟨(13759731500472763101499/2361183241434822606848:ℚ),(15036570352427774365327/2361183241434822606848:ℚ)⟩ thresholdNode915 thresholdNode193
def thresholdNode917 : BoxExpr 1 := .mul ⟨(6405800000884155884517/1180591620717411303424:ℚ),(28832329967765561490547/4722366482869645213696:ℚ)⟩ thresholdNode745 thresholdNode916
def thresholdNode918 : BoxExpr 1 := .neg ⟨(-28832329967765561490547/4722366482869645213696:ℚ),(-6405800000884155884517/1180591620717411303424:ℚ)⟩ thresholdNode917
def thresholdNode919 : BoxExpr 1 := .add ⟨(-2422897216244325065915/4722366482869645213696:ℚ),(3060978701829874203293/4722366482869645213696:ℚ)⟩ thresholdNode901 thresholdNode918
def thresholdNode920 : BoxExpr 1 := .mul ⟨(27546868798273905725451/4722366482869645213696:ℚ),(27546868798273905725549/4722366482869645213696:ℚ)⟩ thresholdNode776 thresholdNode776
def thresholdNode921 : BoxExpr 1 := .mul ⟨(-549712973396544638157/1180591620717411303424:ℚ),(-1099425946793089276313/2361183241434822606848:ℚ)⟩ thresholdNode763 thresholdNode5
def thresholdNode922 : BoxExpr 1 := .neg ⟨(1099425946793089276313/2361183241434822606848:ℚ),(549712973396544638157/1180591620717411303424:ℚ)⟩ thresholdNode921
def thresholdNode923 : BoxExpr 1 := .add ⟨(3460609188227911883161/2361183241434822606848:ℚ),(1730304594113955941581/1180591620717411303424:ℚ)⟩ thresholdNode12 thresholdNode922
def thresholdNode924 : BoxExpr 1 := .mul ⟨(515189656406574231725091/2361183241434822606848:ℚ),(1030379312813148463450483/4722366482869645213696:ℚ)⟩ thresholdNode923 thresholdNode180
def thresholdNode925 : BoxExpr 1 := .mul ⟨(-549712973396544638157/590295810358705651712:ℚ),(-1099425946793089276313/1180591620717411303424:ℚ)⟩ thresholdNode763 thresholdNode182
def thresholdNode926 : BoxExpr 1 := .neg ⟨(1099425946793089276313/1180591620717411303424:ℚ),(549712973396544638157/590295810358705651712:ℚ)⟩ thresholdNode925
def thresholdNode927 : BoxExpr 1 := .add ⟨(2280017567510500579737/1180591620717411303424:ℚ),(1140008783755250289869/590295810358705651712:ℚ)⟩ thresholdNode12 thresholdNode926
def thresholdNode928 : BoxExpr 1 := .inv ⟨(1222619154141008469565/2361183241434822606848:ℚ),(611309577070504234783/1180591620717411303424:ℚ)⟩ thresholdNode927
def thresholdNode929 : BoxExpr 1 := .mul ⟨(533529741262471696284749/4722366482869645213696:ℚ),(266764870631235848142671/2361183241434822606848:ℚ)⟩ thresholdNode924 thresholdNode928
def thresholdNode930 : BoxExpr 1 := .add ⟨(538252107745341341498445/4722366482869645213696:ℚ),(269126053872670670749519/2361183241434822606848:ℚ)⟩ thresholdNode929 thresholdNode12
def thresholdNode931 : BoxExpr 1 := .sqrt ⟨(25208251193560318614237/2361183241434822606848:ℚ),(50416502387120637228503/4722366482869645213696:ℚ)⟩ thresholdNode930
def thresholdNode932 : BoxExpr 1 := .add ⟨(27569434434995141221085/2361183241434822606848:ℚ),(55138868869990282442199/4722366482869645213696:ℚ)⟩ thresholdNode931 thresholdNode12
def thresholdNode933 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode934 : BoxExpr 1 := .mul ⟨(27569434434995141221085/4722366482869645213696:ℚ),(6892358608748785305275/1180591620717411303424:ℚ)⟩ thresholdNode932 thresholdNode933
def thresholdNode935 : BoxExpr 1 := .add ⟨(28750026055712552524509/4722366482869645213696:ℚ),(7187506513928138131131/1180591620717411303424:ℚ)⟩ thresholdNode934 thresholdNode193
def thresholdNode936 : BoxExpr 1 := .mul ⟨(6797931728489372030909/1180591620717411303424:ℚ),(13595863456978744061829/2361183241434822606848:ℚ)⟩ thresholdNode766 thresholdNode935
def thresholdNode937 : BoxExpr 1 := .neg ⟨(-13595863456978744061829/2361183241434822606848:ℚ),(-6797931728489372030909/1180591620717411303424:ℚ)⟩ thresholdNode936
def thresholdNode938 : BoxExpr 1 := .add ⟨(355141884316417601793/4722366482869645213696:ℚ),(355141884316417601913/4722366482869645213696:ℚ)⟩ thresholdNode920 thresholdNode937
def thresholdNode939 : BoxExpr 1 := .mul ⟨(11325174954998774060383/4722366482869645213696:ℚ),(11325174954998774060447/4722366482869645213696:ℚ)⟩ thresholdNode814 thresholdNode776
def thresholdNode940 : BoxExpr 1 := .mul ⟨(11325174954998774060383/4722366482869645213696:ℚ),(11325174954998774060447/4722366482869645213696:ℚ)⟩ thresholdNode776 thresholdNode814
def thresholdNode941 : BoxExpr 1 := .add ⟨(11325174954998774060383/2361183241434822606848:ℚ),(11325174954998774060447/2361183241434822606848:ℚ)⟩ thresholdNode939 thresholdNode940
def thresholdNode942 : BoxExpr 1 := .mul ⟨(13386730882191157269217/4722366482869645213696:ℚ),(13386730882191157269237/4722366482869645213696:ℚ)⟩ thresholdNode795 thresholdNode935
def thresholdNode943 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode944 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode763 thresholdNode51
def thresholdNode945 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode943 thresholdNode944
def thresholdNode946 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode945
def thresholdNode947 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode946
def thresholdNode948 : BoxExpr 1 := .mul ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode947 thresholdNode180
def thresholdNode949 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode923 thresholdNode51
def thresholdNode950 : BoxExpr 1 := .add ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode948 thresholdNode949
def thresholdNode951 : BoxExpr 1 := .mul ⟨(-728057642660942186828527/4722366482869645213696:ℚ),(-364028821330471093413965/2361183241434822606848:ℚ)⟩ thresholdNode950 thresholdNode928
def thresholdNode952 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode12 thresholdNode182
def thresholdNode953 : BoxExpr 1 := .add ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode952 thresholdNode944
def thresholdNode954 : BoxExpr 1 := .neg ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode953
def thresholdNode955 : BoxExpr 1 := .add ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode51 thresholdNode954
def thresholdNode956 : BoxExpr 1 := .mul ⟨(17613135709018616978463/4722366482869645213696:ℚ),(1100820981813663561155/295147905179352825856:ℚ)⟩ thresholdNode927 thresholdNode927
def thresholdNode957 : BoxExpr 1 := .inv ⟨(1266142813349911683691/4722366482869645213696:ℚ),(1266142813349911683693/4722366482869645213696:ℚ)⟩ thresholdNode956
def thresholdNode958 : BoxExpr 1 := .mul ⟨(-1266142813349911683693/1180591620717411303424:ℚ),(-1266142813349911683691/1180591620717411303424:ℚ)⟩ thresholdNode955 thresholdNode957
def thresholdNode959 : BoxExpr 1 := .neg ⟨(1266142813349911683691/1180591620717411303424:ℚ),(1266142813349911683693/1180591620717411303424:ℚ)⟩ thresholdNode958
def thresholdNode960 : BoxExpr 1 := .mul ⟨(1105045418796057882271827/4722366482869645213696:ℚ),(138130677349507235284237/590295810358705651712:ℚ)⟩ thresholdNode924 thresholdNode959
def thresholdNode961 : BoxExpr 1 := .add ⟨(94246944033778923860825/1180591620717411303424:ℚ),(188493888067557847722983/2361183241434822606848:ℚ)⟩ thresholdNode951 thresholdNode960
def thresholdNode962 : BoxExpr 1 := .add ⟨(94246944033778923860825/1180591620717411303424:ℚ),(188493888067557847722983/2361183241434822606848:ℚ)⟩ thresholdNode961 thresholdNode51
def thresholdNode963 : BoxExpr 1 := .mul ⟨(25208251193560318614237/1180591620717411303424:ℚ),(50416502387120637228503/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode931
def thresholdNode964 : BoxExpr 1 := .inv ⟨(221165135844762162393/4722366482869645213696:ℚ),(110582567922381081197/2361183241434822606848:ℚ)⟩ thresholdNode963
def thresholdNode965 : BoxExpr 1 := .mul ⟨(8827835897868745663693/2361183241434822606848:ℚ),(17655671795737491327591/4722366482869645213696:ℚ)⟩ thresholdNode962 thresholdNode964
def thresholdNode966 : BoxExpr 1 := .add ⟨(8827835897868745663693/2361183241434822606848:ℚ),(17655671795737491327591/4722366482869645213696:ℚ)⟩ thresholdNode965 thresholdNode51
def thresholdNode967 : BoxExpr 1 := .mul ⟨(8827835897868745663693/4722366482869645213696:ℚ),(2206958974467186415949/1180591620717411303424:ℚ)⟩ thresholdNode966 thresholdNode933
def thresholdNode968 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode969 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode968
def thresholdNode970 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode969
def thresholdNode971 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode970
def thresholdNode972 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode932 thresholdNode971
def thresholdNode973 : BoxExpr 1 := .add ⟨(8827835897868745663693/4722366482869645213696:ℚ),(2206958974467186415949/1180591620717411303424:ℚ)⟩ thresholdNode967 thresholdNode972
def thresholdNode974 : BoxExpr 1 := .add ⟨(8827835897868745663693/4722366482869645213696:ℚ),(2206958974467186415949/1180591620717411303424:ℚ)⟩ thresholdNode973 thresholdNode51
def thresholdNode975 : BoxExpr 1 := .mul ⟨(1043669067077164978445/590295810358705651712:ℚ),(2087338134154329956915/1180591620717411303424:ℚ)⟩ thresholdNode766 thresholdNode974
def thresholdNode976 : BoxExpr 1 := .add ⟨(21736083418808477096777/4722366482869645213696:ℚ),(21736083418808477096897/4722366482869645213696:ℚ)⟩ thresholdNode942 thresholdNode975
def thresholdNode977 : BoxExpr 1 := .neg ⟨(-21736083418808477096897/4722366482869645213696:ℚ),(-21736083418808477096777/4722366482869645213696:ℚ)⟩ thresholdNode976
def thresholdNode978 : BoxExpr 1 := .add ⟨(914266491189071023869/4722366482869645213696:ℚ),(914266491189071024117/4722366482869645213696:ℚ)⟩ thresholdNode941 thresholdNode977
def thresholdNode979 : BoxExpr 1 := .mul ⟨(-7222772524620083345119/2361183241434822606848:ℚ),(-12473510396575710875355/4722366482869645213696:ℚ)⟩ thresholdNode900 thresholdNode755
def thresholdNode980 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode843 thresholdNode746
def thresholdNode981 : BoxExpr 1 := .mul ⟨(2546462882596875864781/4722366482869645213696:ℚ),(1669656201722930371619/2361183241434822606848:ℚ)⟩ thresholdNode741 thresholdNode851
def thresholdNode982 : BoxExpr 1 := .add ⟨(2546462882596875864781/4722366482869645213696:ℚ),(1669656201722930371619/2361183241434822606848:ℚ)⟩ thresholdNode980 thresholdNode981
def thresholdNode983 : BoxExpr 1 := .mul ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode877 thresholdNode22
def thresholdNode984 : BoxExpr 1 := .add ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode983 thresholdNode880
def thresholdNode985 : BoxExpr 1 := .neg ⟨(1685884834384463341289/2361183241434822606848:ℚ),(3371769668768926682579/4722366482869645213696:ℚ)⟩ thresholdNode984
def thresholdNode986 : BoxExpr 1 := .add ⟨(5918232551365802547359/4722366482869645213696:ℚ),(6711082072214787425817/4722366482869645213696:ℚ)⟩ thresholdNode982 thresholdNode985
def thresholdNode987 : BoxExpr 1 := .mul ⟨(-463205122388476324899/1180591620717411303424:ℚ),(-1389615367165428974693/4722366482869645213696:ℚ)⟩ thresholdNode894 thresholdNode27
def thresholdNode988 : BoxExpr 1 := .add ⟨(-463205122388476324899/1180591620717411303424:ℚ),(-1389615367165428974693/4722366482869645213696:ℚ)⟩ thresholdNode987 thresholdNode897
def thresholdNode989 : BoxExpr 1 := .add ⟨(4065412061811897247763/4722366482869645213696:ℚ),(1330366676262339612781/1180591620717411303424:ℚ)⟩ thresholdNode986 thresholdNode988
def thresholdNode990 : BoxExpr 1 := .mul ⟨(1749925095000497833235/2361183241434822606848:ℚ),(2998285710741878217729/2361183241434822606848:ℚ)⟩ thresholdNode989 thresholdNode989
def thresholdNode991 : BoxExpr 1 := .add ⟨(-1368211857404896377971/590295810358705651712:ℚ),(-6476938975091954439897/4722366482869645213696:ℚ)⟩ thresholdNode979 thresholdNode990
def thresholdNode992 : BoxExpr 1 := .mul ⟨(-7222772524620083345119/2361183241434822606848:ℚ),(-12473510396575710875355/4722366482869645213696:ℚ)⟩ thresholdNode755 thresholdNode900
def thresholdNode993 : BoxExpr 1 := .add ⟨(-1368211857404896377971/590295810358705651712:ℚ),(-6476938975091954439897/4722366482869645213696:ℚ)⟩ thresholdNode990 thresholdNode992
def thresholdNode994 : BoxExpr 1 := .add ⟨(-1368211857404896377971/295147905179352825856:ℚ),(-6476938975091954439897/2361183241434822606848:ℚ)⟩ thresholdNode991 thresholdNode993
def thresholdNode995 : BoxExpr 1 := .mul ⟨(-15036570352427774365327/1180591620717411303424:ℚ),(-13759731500472763101499/1180591620717411303424:ℚ)⟩ thresholdNode861 thresholdNode916
def thresholdNode996 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode997 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode996 thresholdNode857
def thresholdNode998 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode997
def thresholdNode999 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode998
def thresholdNode1000 : BoxExpr 1 := .mul ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode999 thresholdNode180
def thresholdNode1001 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode904 thresholdNode51
def thresholdNode1002 : BoxExpr 1 := .add ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode1000 thresholdNode1001
def thresholdNode1003 : BoxExpr 1 := .mul ⟨(-775757970973210812861743/4722366482869645213696:ℚ),(-171470892974261536379409/1180591620717411303424:ℚ)⟩ thresholdNode1002 thresholdNode909
def thresholdNode1004 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode12 thresholdNode182
def thresholdNode1005 : BoxExpr 1 := .add ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode1004 thresholdNode857
def thresholdNode1006 : BoxExpr 1 := .neg ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode1005
def thresholdNode1007 : BoxExpr 1 := .add ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode51 thresholdNode1006
def thresholdNode1008 : BoxExpr 1 := .mul ⟨(841/256:ℚ),(19845745144259684010571/4722366482869645213696:ℚ)⟩ thresholdNode908 thresholdNode908
def thresholdNode1009 : BoxExpr 1 := .inv ⟨(1123704100623354006827/4722366482869645213696:ℚ),(1437486111313471075751/4722366482869645213696:ℚ)⟩ thresholdNode1008
def thresholdNode1010 : BoxExpr 1 := .mul ⟨(-1437486111313471075751/1180591620717411303424:ℚ),(-1123704100623354006827/1180591620717411303424:ℚ)⟩ thresholdNode1007 thresholdNode1009
def thresholdNode1011 : BoxExpr 1 := .neg ⟨(1123704100623354006827/1180591620717411303424:ℚ),(1437486111313471075751/1180591620717411303424:ℚ)⟩ thresholdNode1010
def thresholdNode1012 : BoxExpr 1 := .mul ⟨(940998802907532821593643/4722366482869645213696:ℚ),(1305413413223885781643843/4722366482869645213696:ℚ)⟩ thresholdNode905 thresholdNode1011
def thresholdNode1013 : BoxExpr 1 := .add ⟨(41310207983580502182975/1180591620717411303424:ℚ),(619529841326839636126207/4722366482869645213696:ℚ)⟩ thresholdNode1003 thresholdNode1012
def thresholdNode1014 : BoxExpr 1 := .add ⟨(41310207983580502182975/1180591620717411303424:ℚ),(619529841326839636126207/4722366482869645213696:ℚ)⟩ thresholdNode1013 thresholdNode51
def thresholdNode1015 : BoxExpr 1 := .mul ⟨(47955376277586584585453/2361183241434822606848:ℚ),(13265682921351657410191/590295810358705651712:ℚ)⟩ thresholdNode5 thresholdNode912
def thresholdNode1016 : BoxExpr 1 := .inv ⟨(210135668577573423495/4722366482869645213696:ℚ),(232515589800027907931/4722366482869645213696:ℚ)⟩ thresholdNode1015
def thresholdNode1017 : BoxExpr 1 := .mul ⟨(7352879709948526563087/4722366482869645213696:ℚ),(15251923688829483087191/2361183241434822606848:ℚ)⟩ thresholdNode1014 thresholdNode1016
def thresholdNode1018 : BoxExpr 1 := .add ⟨(7352879709948526563087/4722366482869645213696:ℚ),(15251923688829483087191/2361183241434822606848:ℚ)⟩ thresholdNode1017 thresholdNode51
def thresholdNode1019 : BoxExpr 1 := .mul ⟨(3676439854974263281543/4722366482869645213696:ℚ),(15251923688829483087191/4722366482869645213696:ℚ)⟩ thresholdNode1018 thresholdNode914
def thresholdNode1020 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode1021 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode1020
def thresholdNode1022 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1021
def thresholdNode1023 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1022
def thresholdNode1024 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode913 thresholdNode1023
def thresholdNode1025 : BoxExpr 1 := .add ⟨(3676439854974263281543/4722366482869645213696:ℚ),(15251923688829483087191/4722366482869645213696:ℚ)⟩ thresholdNode1019 thresholdNode1024
def thresholdNode1026 : BoxExpr 1 := .add ⟨(3676439854974263281543/4722366482869645213696:ℚ),(15251923688829483087191/4722366482869645213696:ℚ)⟩ thresholdNode1025 thresholdNode51
def thresholdNode1027 : BoxExpr 1 := .mul ⟨(746776845541647229063/2361183241434822606848:ℚ),(8007259936635478620781/4722366482869645213696:ℚ)⟩ thresholdNode848 thresholdNode1026
def thresholdNode1028 : BoxExpr 1 := .add ⟨(-29326363859313901501591/2361183241434822606848:ℚ),(-47031666065255573785215/4722366482869645213696:ℚ)⟩ thresholdNode995 thresholdNode1027
def thresholdNode1029 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode5
def thresholdNode1030 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode12 thresholdNode51
def thresholdNode1031 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1029 thresholdNode1030
def thresholdNode1032 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1030 thresholdNode857
def thresholdNode1033 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1031 thresholdNode1032
def thresholdNode1034 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1033
def thresholdNode1035 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1034
def thresholdNode1036 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1035 thresholdNode180
def thresholdNode1037 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode999 thresholdNode51
def thresholdNode1038 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1036 thresholdNode1037
def thresholdNode1039 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1037 thresholdNode1001
def thresholdNode1040 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1038 thresholdNode1039
def thresholdNode1041 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1040 thresholdNode909
def thresholdNode1042 : BoxExpr 1 := .mul ⟨(-1712017591113292828384987/4722366482869645213696:ℚ),(-334577352144900558788851/1180591620717411303424:ℚ)⟩ thresholdNode1002 thresholdNode1011
def thresholdNode1043 : BoxExpr 1 := .add ⟨(-1712017591113292828384987/4722366482869645213696:ℚ),(-334577352144900558788851/1180591620717411303424:ℚ)⟩ thresholdNode1041 thresholdNode1042
def thresholdNode1044 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode182
def thresholdNode1045 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1044 thresholdNode1030
def thresholdNode1046 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1045 thresholdNode1032
def thresholdNode1047 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1046
def thresholdNode1048 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1047
def thresholdNode1049 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1048 thresholdNode1009
def thresholdNode1050 : BoxExpr 1 := .mul ⟨(-605053205617673293005/73786976294838206464:ℚ),(-29/4:ℚ)⟩ thresholdNode1007 thresholdNode908
def thresholdNode1051 : BoxExpr 1 := .mul ⟨(-605053205617673293005/73786976294838206464:ℚ),(-29/4:ℚ)⟩ thresholdNode908 thresholdNode1007
def thresholdNode1052 : BoxExpr 1 := .add ⟨(-605053205617673293005/36893488147419103232:ℚ),(-29/2:ℚ)⟩ thresholdNode1050 thresholdNode1051
def thresholdNode1053 : BoxExpr 1 := .mul ⟨(707281/65536:ℚ),(41700871984375661027241/2361183241434822606848:ℚ)⟩ thresholdNode1008 thresholdNode1008
def thresholdNode1054 : BoxExpr 1 := .inv ⟨(66847358752132897491/1180591620717411303424:ℚ),(218785044290278594169/2361183241434822606848:ℚ)⟩ thresholdNode1053
def thresholdNode1055 : BoxExpr 1 := .mul ⟨(-3588074726360568944373/2361183241434822606848:ℚ),(-1938573403811854027239/2361183241434822606848:ℚ)⟩ thresholdNode1052 thresholdNode1054
def thresholdNode1056 : BoxExpr 1 := .neg ⟨(1938573403811854027239/2361183241434822606848:ℚ),(3588074726360568944373/2361183241434822606848:ℚ)⟩ thresholdNode1055
def thresholdNode1057 : BoxExpr 1 := .mul ⟨(-3588074726360568944373/590295810358705651712:ℚ),(-1938573403811854027239/590295810358705651712:ℚ)⟩ thresholdNode1007 thresholdNode1056
def thresholdNode1058 : BoxExpr 1 := .add ⟨(-3588074726360568944373/590295810358705651712:ℚ),(-1938573403811854027239/590295810358705651712:ℚ)⟩ thresholdNode1049 thresholdNode1057
def thresholdNode1059 : BoxExpr 1 := .neg ⟨(1938573403811854027239/590295810358705651712:ℚ),(3588074726360568944373/590295810358705651712:ℚ)⟩ thresholdNode1058
def thresholdNode1060 : BoxExpr 1 := .mul ⟨(3246753751852284571818651/4722366482869645213696:ℚ),(6516822442424687355119711/4722366482869645213696:ℚ)⟩ thresholdNode905 thresholdNode1059
def thresholdNode1061 : BoxExpr 1 := .add ⟨(23980252511546745991151/73786976294838206464:ℚ),(5178513033845085119964307/4722366482869645213696:ℚ)⟩ thresholdNode1042 thresholdNode1060
def thresholdNode1062 : BoxExpr 1 := .add ⟨(-177281430374301084951323/4722366482869645213696:ℚ),(3840203625265482884808903/4722366482869645213696:ℚ)⟩ thresholdNode1043 thresholdNode1061
def thresholdNode1063 : BoxExpr 1 := .add ⟨(-177281430374301084951323/4722366482869645213696:ℚ),(3840203625265482884808903/4722366482869645213696:ℚ)⟩ thresholdNode1062 thresholdNode51
def thresholdNode1064 : BoxExpr 1 := .mul ⟨(-4364410989024360608037/2361183241434822606848:ℚ),(94540228307123601232493/2361183241434822606848:ℚ)⟩ thresholdNode1063 thresholdNode1016
def thresholdNode1065 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode912
def thresholdNode1066 : BoxExpr 1 := .mul ⟨(7352879709948526563087/2361183241434822606848:ℚ),(15251923688829483087191/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode1017
def thresholdNode1067 : BoxExpr 1 := .add ⟨(7352879709948526563087/2361183241434822606848:ℚ),(15251923688829483087191/1180591620717411303424:ℚ)⟩ thresholdNode1065 thresholdNode1066
def thresholdNode1068 : BoxExpr 1 := .mul ⟨(486984252972980216280775/1180591620717411303424:ℚ),(2384951277399771560083679/4722366482869645213696:ℚ)⟩ thresholdNode1015 thresholdNode1015
def thresholdNode1069 : BoxExpr 1 := .inv ⟨(584413018461228817/295147905179352825856:ℚ),(11448391330103211455/4722366482869645213696:ℚ)⟩ thresholdNode1068
def thresholdNode1070 : BoxExpr 1 := .mul ⟨(3639801054205440341/590295810358705651712:ℚ),(73950207617298611517/2361183241434822606848:ℚ)⟩ thresholdNode1067 thresholdNode1069
def thresholdNode1071 : BoxExpr 1 := .neg ⟨(-73950207617298611517/2361183241434822606848:ℚ),(-3639801054205440341/590295810358705651712:ℚ)⟩ thresholdNode1070
def thresholdNode1072 : BoxExpr 1 := .mul ⟨(-9701568177188949957719/2361183241434822606848:ℚ),(-509442675788982226521/2361183241434822606848:ℚ)⟩ thresholdNode1014 thresholdNode1071
def thresholdNode1073 : BoxExpr 1 := .add ⟨(-3516494791553327641439/590295810358705651712:ℚ),(23507696407833654751493/590295810358705651712:ℚ)⟩ thresholdNode1064 thresholdNode1072
def thresholdNode1074 : BoxExpr 1 := .add ⟨(-3516494791553327641439/590295810358705651712:ℚ),(23507696407833654751493/590295810358705651712:ℚ)⟩ thresholdNode1073 thresholdNode51
def thresholdNode1075 : BoxExpr 1 := .mul ⟨(-3516494791553327641439/1180591620717411303424:ℚ),(23507696407833654751493/1180591620717411303424:ℚ)⟩ thresholdNode1074 thresholdNode914
def thresholdNode1076 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1018 thresholdNode1023
def thresholdNode1077 : BoxExpr 1 := .add ⟨(-3516494791553327641439/1180591620717411303424:ℚ),(23507696407833654751493/1180591620717411303424:ℚ)⟩ thresholdNode1075 thresholdNode1076
def thresholdNode1078 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode5 thresholdNode51
def thresholdNode1079 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1029 thresholdNode1078
def thresholdNode1080 : BoxExpr 1 := .mul ⟨(16/1:ℚ),(16/1:ℚ)⟩ thresholdNode1020 thresholdNode1020
def thresholdNode1081 : BoxExpr 1 := .inv ⟨(1/16:ℚ),(1/16:ℚ)⟩ thresholdNode1080
def thresholdNode1082 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1079 thresholdNode1081
def thresholdNode1083 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1082
def thresholdNode1084 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1083
def thresholdNode1085 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1022 thresholdNode1084
def thresholdNode1086 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1085
def thresholdNode1087 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode913 thresholdNode1086
def thresholdNode1088 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1076 thresholdNode1087
def thresholdNode1089 : BoxExpr 1 := .add ⟨(-3516494791553327641439/1180591620717411303424:ℚ),(23507696407833654751493/1180591620717411303424:ℚ)⟩ thresholdNode1077 thresholdNode1088
def thresholdNode1090 : BoxExpr 1 := .add ⟨(-3516494791553327641439/1180591620717411303424:ℚ),(23507696407833654751493/1180591620717411303424:ℚ)⟩ thresholdNode1089 thresholdNode51
def thresholdNode1091 : BoxExpr 1 := .mul ⟨(-6742810081264608226529/2361183241434822606848:ℚ),(90151097454651134969837/4722366482869645213696:ℚ)⟩ thresholdNode745 thresholdNode1090
def thresholdNode1092 : BoxExpr 1 := .add ⟨(-2998016617861480498733/1180591620717411303424:ℚ),(49079178695643306795309/2361183241434822606848:ℚ)⟩ thresholdNode1027 thresholdNode1091
def thresholdNode1093 : BoxExpr 1 := .add ⟨(-35322397095036862499057/2361183241434822606848:ℚ),(51126691326031039805403/4722366482869645213696:ℚ)⟩ thresholdNode1028 thresholdNode1092
def thresholdNode1094 : BoxExpr 1 := .neg ⟨(-51126691326031039805403/4722366482869645213696:ℚ),(35322397095036862499057/2361183241434822606848:ℚ)⟩ thresholdNode1093
def thresholdNode1095 : BoxExpr 1 := .add ⟨(-73018081044509381852939/4722366482869645213696:ℚ),(3605682264993113507395/295147905179352825856:ℚ)⟩ thresholdNode994 thresholdNode1094
def thresholdCell2Out1 : TaylorCertificate1 :=
  { center := (-149/640:ℚ), radius := (19/640:ℚ)
    whole := thresholdNode919, centerValue := thresholdNode938, gradient := thresholdNode978, hessian := thresholdNode1095 }
theorem thresholdCell2Out1_check : thresholdCell2Out1.check = true := by decide +kernel
theorem thresholdCell2Out1_lower_pos : 0 < thresholdCell2Out1.lower := by decide +kernel
theorem thresholdCell2Out1_positive (x : ℝ) (hx : (-(21/80:ℝ)) ≤ x ∧ x ≤ (-(13/64:ℝ))) :
    0 < thresholdNode919.eval (fun _ => x) := by
  apply thresholdCell2Out1.positive_sound thresholdCell2Out1_check thresholdCell2Out1_lower_pos x
  norm_num [thresholdCell2Out1]
  exact hx
theorem thresholdCell2_public (x : ℝ)
    (hx : (-(21/80:ℝ)) ≤ x ∧ x ≤ (-(13/64:ℝ))) : qc x < fA (43/20) x := by
  have hf := thresholdCell2Out0_positive x hx
  have hg := thresholdCell2Out1_positive x hx
  have hfa : thresholdNode755.eval (fun _ => x) = thresholdFA 0 x := by
    norm_num [thresholdNode0, thresholdNode1, thresholdNode735, thresholdNode3, thresholdNode736, thresholdNode5, thresholdNode737, thresholdNode738, thresholdNode739, thresholdNode9, thresholdNode740, thresholdNode741, thresholdNode12, thresholdNode742, thresholdNode743, thresholdNode744, thresholdNode745, thresholdNode746, thresholdNode747, thresholdNode19, thresholdNode748, thresholdNode749, thresholdNode22, thresholdNode750, thresholdNode751, thresholdNode752, thresholdNode753, thresholdNode27, thresholdNode754, thresholdNode755, BoxExpr.eval, thresholdFA, ftilde, pow_two, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  have hgap : thresholdNode919.eval (fun _ => x) =
      (thresholdNode755.eval (fun _ => x))^2 - (1-x^2)*(thresholdCapacity 1 x+1/4) := by
    norm_num [thresholdNode901, thresholdNode12, thresholdNode742, thresholdNode743, thresholdNode744, thresholdNode745, thresholdNode5, thresholdNode902, thresholdNode903, thresholdNode904, thresholdNode180, thresholdNode905, thresholdNode182, thresholdNode906, thresholdNode907, thresholdNode908, thresholdNode909, thresholdNode910, thresholdNode911, thresholdNode912, thresholdNode913, thresholdNode914, thresholdNode915, thresholdNode193, thresholdNode916, thresholdNode917, thresholdNode918, thresholdNode919, BoxExpr.eval, thresholdCapacity, Da, D5, beta5, eta5, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  rw [hfa] at hf
  rw [hgap, hfa] at hg
  refine threshold_positive_to_public 0 1 x ?_ ?_ ?_ hf hg
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdFADomain] <;> constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdCapacityDomain] <;> linarith [hx.1,hx.2]
def thresholdNode1096 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode1097 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode1096 thresholdNode3
def thresholdNode1098 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode1099 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1098
def thresholdNode1100 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode1099 thresholdNode1099
def thresholdNode1101 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode1100 thresholdNode9
def thresholdNode1102 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode1097 thresholdNode1101
def thresholdNode1103 : BoxExpr 1 := .var 0
def thresholdNode1104 : BoxExpr 1 := .mul ⟨(6098954759370220503/295147905179352825856:ℚ),(169/4096:ℚ)⟩ thresholdNode1103 thresholdNode1103
def thresholdNode1105 : BoxExpr 1 := .neg ⟨(-169/4096:ℚ),(-6098954759370220503/295147905179352825856:ℚ)⟩ thresholdNode1104
def thresholdNode1106 : BoxExpr 1 := .add ⟨(3927/4096:ℚ),(289048950419982605353/295147905179352825856:ℚ)⟩ thresholdNode12 thresholdNode1105
def thresholdNode1107 : BoxExpr 1 := .sqrt ⟨(4623918433361082282871/4722366482869645213696:ℚ),(4673320148026626629987/4722366482869645213696:ℚ)⟩ thresholdNode1106
def thresholdNode1108 : BoxExpr 1 := .mul ⟨(1502397797469641153997/590295810358705651712:ℚ),(12147594726773011930661/4722366482869645213696:ℚ)⟩ thresholdNode1102 thresholdNode1107
def thresholdNode1109 : BoxExpr 1 := .neg ⟨(169710045478127874867/1180591620717411303424:ℚ),(13/64:ℚ)⟩ thresholdNode1103
def thresholdNode1110 : BoxExpr 1 := .add ⟨(560781019840770369125/4722366482869645213696:ℚ),(420585764880577776845/2361183241434822606848:ℚ)⟩ thresholdNode19 thresholdNode1109
def thresholdNode1111 : BoxExpr 1 := .mul ⟨(400397648166310043555/4722366482869645213696:ℚ),(600596472249465065335/4722366482869645213696:ℚ)⟩ thresholdNode1110 thresholdNode22
def thresholdNode1112 : BoxExpr 1 := .neg ⟨(-600596472249465065335/4722366482869645213696:ℚ),(-400397648166310043555/4722366482869645213696:ℚ)⟩ thresholdNode1111
def thresholdNode1113 : BoxExpr 1 := .add ⟨(11418585907507664166641/4722366482869645213696:ℚ),(5873598539303350943553/2361183241434822606848:ℚ)⟩ thresholdNode1108 thresholdNode1112
def thresholdNode1114 : BoxExpr 1 := .mul ⟨(66592746106091481333/4722366482869645213696:ℚ),(74916839369352916501/2361183241434822606848:ℚ)⟩ thresholdNode1110 thresholdNode1110
def thresholdNode1115 : BoxExpr 1 := .mul ⟨(55005608283631563581/4722366482869645213696:ℚ),(30940654659542754515/1180591620717411303424:ℚ)⟩ thresholdNode1114 thresholdNode27
def thresholdNode1116 : BoxExpr 1 := .add ⟨(5736795757895647865111/2361183241434822606848:ℚ),(5935479848622436452583/2361183241434822606848:ℚ)⟩ thresholdNode1113 thresholdNode1115
def thresholdNode1117 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode1118 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode1117 thresholdNode3
def thresholdNode1119 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode1120 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1119
def thresholdNode1121 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode1120 thresholdNode1120
def thresholdNode1122 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode1121 thresholdNode9
def thresholdNode1123 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode1118 thresholdNode1122
def thresholdNode1124 : BoxExpr 1 := .var 0
def thresholdNode1125 : BoxExpr 1 := .mul ⟨(17756432322826201989/590295810358705651712:ℚ),(71025729291304807957/2361183241434822606848:ℚ)⟩ thresholdNode1124 thresholdNode1124
def thresholdNode1126 : BoxExpr 1 := .neg ⟨(-71025729291304807957/2361183241434822606848:ℚ),(-17756432322826201989/590295810358705651712:ℚ)⟩ thresholdNode1125
def thresholdNode1127 : BoxExpr 1 := .add ⟨(2290157512143517798891/2361183241434822606848:ℚ),(572539378035879449723/590295810358705651712:ℚ)⟩ thresholdNode12 thresholdNode1126
def thresholdNode1128 : BoxExpr 1 := .sqrt ⟨(1162699610595890377011/1180591620717411303424:ℚ),(2325399221191780754023/2361183241434822606848:ℚ)⟩ thresholdNode1127
def thresholdNode1129 : BoxExpr 1 := .mul ⟨(12089052931209710605929/4722366482869645213696:ℚ),(1511131616401213825743/590295810358705651712:ℚ)⟩ thresholdNode1123 thresholdNode1128
def thresholdNode1130 : BoxExpr 1 := .neg ⟨(409517718436352045875/2361183241434822606848:ℚ),(819035436872704091751/4722366482869645213696:ℚ)⟩ thresholdNode1124
def thresholdNode1131 : BoxExpr 1 := .add ⟨(700976274800962961407/4722366482869645213696:ℚ),(700976274800962961409/4722366482869645213696:ℚ)⟩ thresholdNode19 thresholdNode1130
def thresholdNode1132 : BoxExpr 1 := .mul ⟨(125124265051971888611/1180591620717411303424:ℚ),(500497060207887554447/4722366482869645213696:ℚ)⟩ thresholdNode1131 thresholdNode22
def thresholdNode1133 : BoxExpr 1 := .neg ⟨(-500497060207887554447/4722366482869645213696:ℚ),(-125124265051971888611/1180591620717411303424:ℚ)⟩ thresholdNode1132
def thresholdNode1134 : BoxExpr 1 := .add ⟨(5794277935500911525741/2361183241434822606848:ℚ),(2897138967750455762875/1180591620717411303424:ℚ)⟩ thresholdNode1129 thresholdNode1133
def thresholdNode1135 : BoxExpr 1 := .mul ⟨(104051165790767939583/4722366482869645213696:ℚ),(104051165790767939585/4722366482869645213696:ℚ)⟩ thresholdNode1131 thresholdNode1131
def thresholdNode1136 : BoxExpr 1 := .mul ⟨(85946262943174318095/4722366482869645213696:ℚ),(42973131471587159049/2361183241434822606848:ℚ)⟩ thresholdNode1135 thresholdNode27
def thresholdNode1137 : BoxExpr 1 := .add ⟨(11674502133944997369577/4722366482869645213696:ℚ),(5837251066972498684799/2361183241434822606848:ℚ)⟩ thresholdNode1134 thresholdNode1136
def thresholdNode1138 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1
def thresholdNode1139 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode51
def thresholdNode1140 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1138 thresholdNode1139
def thresholdNode1141 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1140 thresholdNode51
def thresholdNode1142 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51
def thresholdNode1143 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1142
def thresholdNode1144 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1143 thresholdNode1120
def thresholdNode1145 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1120 thresholdNode1143
def thresholdNode1146 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1144 thresholdNode1145
def thresholdNode1147 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1146 thresholdNode9
def thresholdNode1148 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1121 thresholdNode51
def thresholdNode1149 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1147 thresholdNode1148
def thresholdNode1150 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1141 thresholdNode1149
def thresholdNode1151 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1150 thresholdNode1128
def thresholdNode1152 : BoxExpr 1 := .mul ⟨(-819035436872704091751/4722366482869645213696:ℚ),(-409517718436352045875/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode1124
def thresholdNode1153 : BoxExpr 1 := .mul ⟨(-819035436872704091751/4722366482869645213696:ℚ),(-409517718436352045875/2361183241434822606848:ℚ)⟩ thresholdNode1124 thresholdNode12
def thresholdNode1154 : BoxExpr 1 := .add ⟨(-819035436872704091751/2361183241434822606848:ℚ),(-409517718436352045875/1180591620717411303424:ℚ)⟩ thresholdNode1152 thresholdNode1153
def thresholdNode1155 : BoxExpr 1 := .neg ⟨(409517718436352045875/1180591620717411303424:ℚ),(819035436872704091751/2361183241434822606848:ℚ)⟩ thresholdNode1154
def thresholdNode1156 : BoxExpr 1 := .add ⟨(409517718436352045875/1180591620717411303424:ℚ),(819035436872704091751/2361183241434822606848:ℚ)⟩ thresholdNode51 thresholdNode1155
def thresholdNode1157 : BoxExpr 1 := .mul ⟨(1162699610595890377011/590295810358705651712:ℚ),(2325399221191780754023/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode1128
def thresholdNode1158 : BoxExpr 1 := .inv ⟨(1198758959069260389861/2361183241434822606848:ℚ),(599379479534630194931/1180591620717411303424:ℚ)⟩ thresholdNode1157
def thresholdNode1159 : BoxExpr 1 := .mul ⟨(831639027854299395465/4722366482869645213696:ℚ),(207909756963574848867/1180591620717411303424:ℚ)⟩ thresholdNode1156 thresholdNode1158
def thresholdNode1160 : BoxExpr 1 := .mul ⟨(2161720907053073133601/4722366482869645213696:ℚ),(2161720907053073133611/4722366482869645213696:ℚ)⟩ thresholdNode1123 thresholdNode1159
def thresholdNode1161 : BoxExpr 1 := .add ⟨(2161720907053073133601/4722366482869645213696:ℚ),(2161720907053073133611/4722366482869645213696:ℚ)⟩ thresholdNode1151 thresholdNode1160
def thresholdNode1162 : BoxExpr 1 := .neg ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode12
def thresholdNode1163 : BoxExpr 1 := .add ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode51 thresholdNode1162
def thresholdNode1164 : BoxExpr 1 := .mul ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode1163 thresholdNode22
def thresholdNode1165 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1131 thresholdNode51
def thresholdNode1166 : BoxExpr 1 := .add ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode1164 thresholdNode1165
def thresholdNode1167 : BoxExpr 1 := .neg ⟨(1685884834384463341289/2361183241434822606848:ℚ),(3371769668768926682579/4722366482869645213696:ℚ)⟩ thresholdNode1166
def thresholdNode1168 : BoxExpr 1 := .add ⟨(5533490575821999816179/4722366482869645213696:ℚ),(2766745287910999908095/2361183241434822606848:ℚ)⟩ thresholdNode1161 thresholdNode1167
def thresholdNode1169 : BoxExpr 1 := .mul ⟨(-700976274800962961409/4722366482869645213696:ℚ),(-700976274800962961407/4722366482869645213696:ℚ)⟩ thresholdNode1163 thresholdNode1131
def thresholdNode1170 : BoxExpr 1 := .mul ⟨(-700976274800962961409/4722366482869645213696:ℚ),(-700976274800962961407/4722366482869645213696:ℚ)⟩ thresholdNode1131 thresholdNode1163
def thresholdNode1171 : BoxExpr 1 := .add ⟨(-700976274800962961409/2361183241434822606848:ℚ),(-700976274800962961407/2361183241434822606848:ℚ)⟩ thresholdNode1169 thresholdNode1170
def thresholdNode1172 : BoxExpr 1 := .mul ⟨(-144751600746398851531/590295810358705651712:ℚ),(-289503201492797703061/1180591620717411303424:ℚ)⟩ thresholdNode1171 thresholdNode27
def thresholdNode1173 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1135 thresholdNode51
def thresholdNode1174 : BoxExpr 1 := .add ⟨(-144751600746398851531/590295810358705651712:ℚ),(-289503201492797703061/1180591620717411303424:ℚ)⟩ thresholdNode1172 thresholdNode1173
def thresholdNode1175 : BoxExpr 1 := .add ⟨(4375477769850809003931/4722366482869645213696:ℚ),(2187738884925404501973/2361183241434822606848:ℚ)⟩ thresholdNode1168 thresholdNode1174
def thresholdNode1176 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1
def thresholdNode1177 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode51
def thresholdNode1178 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1176 thresholdNode1177
def thresholdNode1179 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode51
def thresholdNode1180 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1177 thresholdNode1179
def thresholdNode1181 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1178 thresholdNode1180
def thresholdNode1182 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1181 thresholdNode51
def thresholdNode1183 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51
def thresholdNode1184 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1183
def thresholdNode1185 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1184 thresholdNode1099
def thresholdNode1186 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1184 thresholdNode1184
def thresholdNode1187 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1185 thresholdNode1186
def thresholdNode1188 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1099 thresholdNode1184
def thresholdNode1189 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1186 thresholdNode1188
def thresholdNode1190 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1187 thresholdNode1189
def thresholdNode1191 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1190 thresholdNode9
def thresholdNode1192 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1185 thresholdNode1188
def thresholdNode1193 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1192 thresholdNode51
def thresholdNode1194 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1191 thresholdNode1193
def thresholdNode1195 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1100 thresholdNode51
def thresholdNode1196 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1193 thresholdNode1195
def thresholdNode1197 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1194 thresholdNode1196
def thresholdNode1198 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1182 thresholdNode1197
def thresholdNode1199 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1198 thresholdNode1107
def thresholdNode1200 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1176 thresholdNode1179
def thresholdNode1201 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1200 thresholdNode51
def thresholdNode1202 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1192 thresholdNode9
def thresholdNode1203 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1202 thresholdNode1195
def thresholdNode1204 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1201 thresholdNode1203
def thresholdNode1205 : BoxExpr 1 := .mul ⟨(-13/64:ℚ),(-169710045478127874867/1180591620717411303424:ℚ)⟩ thresholdNode12 thresholdNode1103
def thresholdNode1206 : BoxExpr 1 := .mul ⟨(-13/64:ℚ),(-169710045478127874867/1180591620717411303424:ℚ)⟩ thresholdNode1103 thresholdNode12
def thresholdNode1207 : BoxExpr 1 := .add ⟨(-13/32:ℚ),(-169710045478127874867/590295810358705651712:ℚ)⟩ thresholdNode1205 thresholdNode1206
def thresholdNode1208 : BoxExpr 1 := .neg ⟨(169710045478127874867/590295810358705651712:ℚ),(13/32:ℚ)⟩ thresholdNode1207
def thresholdNode1209 : BoxExpr 1 := .add ⟨(169710045478127874867/590295810358705651712:ℚ),(13/32:ℚ)⟩ thresholdNode51 thresholdNode1208
def thresholdNode1210 : BoxExpr 1 := .mul ⟨(4623918433361082282871/2361183241434822606848:ℚ),(4673320148026626629987/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode1107
def thresholdNode1211 : BoxExpr 1 := .inv ⟨(1192981889329121711615/2361183241434822606848:ℚ),(1205727648526037244121/2361183241434822606848:ℚ)⟩ thresholdNode1210
def thresholdNode1212 : BoxExpr 1 := .mul ⟨(685964586364244984177/4722366482869645213696:ℚ),(979653714427405260849/4722366482869645213696:ℚ)⟩ thresholdNode1209 thresholdNode1211
def thresholdNode1213 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1204 thresholdNode1212
def thresholdNode1214 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1199 thresholdNode1213
def thresholdNode1215 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1103
def thresholdNode1216 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode12
def thresholdNode1217 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1215 thresholdNode1216
def thresholdNode1218 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1103 thresholdNode51
def thresholdNode1219 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1216 thresholdNode1218
def thresholdNode1220 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode1217 thresholdNode1219
def thresholdNode1221 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode1220
def thresholdNode1222 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode1221
def thresholdNode1223 : BoxExpr 1 := .mul ⟨(-1205727648526037244121/1180591620717411303424:ℚ),(-1192981889329121711615/1180591620717411303424:ℚ)⟩ thresholdNode1222 thresholdNode1211
def thresholdNode1224 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1107
def thresholdNode1225 : BoxExpr 1 := .mul ⟨(685964586364244984177/2361183241434822606848:ℚ),(979653714427405260849/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode1212
def thresholdNode1226 : BoxExpr 1 := .add ⟨(685964586364244984177/2361183241434822606848:ℚ),(979653714427405260849/2361183241434822606848:ℚ)⟩ thresholdNode1224 thresholdNode1225
def thresholdNode1227 : BoxExpr 1 := .mul ⟨(9055045497182176149501/2361183241434822606848:ℚ),(18499132826878886742597/4722366482869645213696:ℚ)⟩ thresholdNode1210 thresholdNode1210
def thresholdNode1228 : BoxExpr 1 := .inv ⟨(1205502193385414597249/4722366482869645213696:ℚ),(1231398848601608530387/4722366482869645213696:ℚ)⟩ thresholdNode1227
def thresholdNode1229 : BoxExpr 1 := .mul ⟨(350219245561099908159/4722366482869645213696:ℚ),(510906749973854335173/4722366482869645213696:ℚ)⟩ thresholdNode1226 thresholdNode1228
def thresholdNode1230 : BoxExpr 1 := .neg ⟨(-510906749973854335173/4722366482869645213696:ℚ),(-350219245561099908159/4722366482869645213696:ℚ)⟩ thresholdNode1229
def thresholdNode1231 : BoxExpr 1 := .mul ⟨(-207555867176878323665/4722366482869645213696:ℚ),(-100688033098816223595/4722366482869645213696:ℚ)⟩ thresholdNode1209 thresholdNode1230
def thresholdNode1232 : BoxExpr 1 := .add ⟨(-5030466461281027300149/4722366482869645213696:ℚ),(-4872615590415303070055/4722366482869645213696:ℚ)⟩ thresholdNode1223 thresholdNode1231
def thresholdNode1233 : BoxExpr 1 := .mul ⟨(-13075942996130838312647/4722366482869645213696:ℚ),(-6332816667473009017571/2361183241434822606848:ℚ)⟩ thresholdNode1102 thresholdNode1232
def thresholdNode1234 : BoxExpr 1 := .add ⟨(-13075942996130838312647/4722366482869645213696:ℚ),(-6332816667473009017571/2361183241434822606848:ℚ)⟩ thresholdNode1213 thresholdNode1233
def thresholdNode1235 : BoxExpr 1 := .add ⟨(-13075942996130838312647/4722366482869645213696:ℚ),(-6332816667473009017571/2361183241434822606848:ℚ)⟩ thresholdNode1214 thresholdNode1234
def thresholdNode1236 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1184 thresholdNode22
def thresholdNode1237 : BoxExpr 1 := .neg ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode12
def thresholdNode1238 : BoxExpr 1 := .add ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode51 thresholdNode1237
def thresholdNode1239 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1238 thresholdNode51
def thresholdNode1240 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1236 thresholdNode1239
def thresholdNode1241 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1110 thresholdNode51
def thresholdNode1242 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1239 thresholdNode1241
def thresholdNode1243 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1240 thresholdNode1242
def thresholdNode1244 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1243
def thresholdNode1245 : BoxExpr 1 := .add ⟨(-13075942996130838312647/4722366482869645213696:ℚ),(-6332816667473009017571/2361183241434822606848:ℚ)⟩ thresholdNode1235 thresholdNode1244
def thresholdNode1246 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1184 thresholdNode1110
def thresholdNode1247 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1238 thresholdNode1238
def thresholdNode1248 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1246 thresholdNode1247
def thresholdNode1249 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1110 thresholdNode1184
def thresholdNode1250 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1247 thresholdNode1249
def thresholdNode1251 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode1248 thresholdNode1250
def thresholdNode1252 : BoxExpr 1 := .mul ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode1251 thresholdNode27
def thresholdNode1253 : BoxExpr 1 := .mul ⟨(-420585764880577776845/2361183241434822606848:ℚ),(-560781019840770369125/4722366482869645213696:ℚ)⟩ thresholdNode1238 thresholdNode1110
def thresholdNode1254 : BoxExpr 1 := .mul ⟨(-420585764880577776845/2361183241434822606848:ℚ),(-560781019840770369125/4722366482869645213696:ℚ)⟩ thresholdNode1110 thresholdNode1238
def thresholdNode1255 : BoxExpr 1 := .add ⟨(-420585764880577776845/1180591620717411303424:ℚ),(-560781019840770369125/2361183241434822606848:ℚ)⟩ thresholdNode1253 thresholdNode1254
def thresholdNode1256 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1255 thresholdNode51
def thresholdNode1257 : BoxExpr 1 := .add ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode1252 thresholdNode1256
def thresholdNode1258 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1114 thresholdNode51
def thresholdNode1259 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1256 thresholdNode1258
def thresholdNode1260 : BoxExpr 1 := .add ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode1257 thresholdNode1259
def thresholdNode1261 : BoxExpr 1 := .add ⟨(-5274593566430184419623/4722366482869645213696:ℚ),(-1216070976311341035529/1180591620717411303424:ℚ)⟩ thresholdNode1245 thresholdNode1260
def thresholdCell3Out0 : TaylorCertificate1 :=
  { center := (-111/640:ℚ), radius := (19/640:ℚ)
    whole := thresholdNode1116, centerValue := thresholdNode1137, gradient := thresholdNode1175, hessian := thresholdNode1261 }
theorem thresholdCell3Out0_check : thresholdCell3Out0.check = true := by decide +kernel
theorem thresholdCell3Out0_lower_pos : 0 < thresholdCell3Out0.lower := by decide +kernel
theorem thresholdCell3Out0_positive (x : ℝ) (hx : (-(13/64:ℝ)) ≤ x ∧ x ≤ (-(23/160:ℝ))) :
    0 < thresholdNode1116.eval (fun _ => x) := by
  apply thresholdCell3Out0.positive_sound thresholdCell3Out0_check thresholdCell3Out0_lower_pos x
  norm_num [thresholdCell3Out0]
  exact hx
def thresholdNode1262 : BoxExpr 1 := .mul ⟨(6969138394318465973363/1180591620717411303424:ℚ),(29840903844459627304417/4722366482869645213696:ℚ)⟩ thresholdNode1116 thresholdNode1116
def thresholdNode1263 : BoxExpr 1 := .mul ⟨(-13/32:ℚ),(-169710045478127874867/590295810358705651712:ℚ)⟩ thresholdNode1103 thresholdNode5
def thresholdNode1264 : BoxExpr 1 := .neg ⟨(169710045478127874867/590295810358705651712:ℚ),(13/32:ℚ)⟩ thresholdNode1263
def thresholdNode1265 : BoxExpr 1 := .add ⟨(760005855836833526579/590295810358705651712:ℚ),(45/32:ℚ)⟩ thresholdNode12 thresholdNode1264
def thresholdNode1266 : BoxExpr 1 := .mul ⟨(905151976287883085162979/4722366482869645213696:ℚ),(494318433652363335343991/2361183241434822606848:ℚ)⟩ thresholdNode1265 thresholdNode180
def thresholdNode1267 : BoxExpr 1 := .mul ⟨(-13/16:ℚ),(-169710045478127874867/295147905179352825856:ℚ)⟩ thresholdNode1103 thresholdNode182
def thresholdNode1268 : BoxExpr 1 := .neg ⟨(169710045478127874867/295147905179352825856:ℚ),(13/16:ℚ)⟩ thresholdNode1267
def thresholdNode1269 : BoxExpr 1 := .add ⟨(464857950657480700723/295147905179352825856:ℚ),(29/16:ℚ)⟩ thresholdNode12 thresholdNode1268
def thresholdNode1270 : BoxExpr 1 := .inv ⟨(2605443576755666324797/4722366482869645213696:ℚ),(1499163962815760385301/2361183241434822606848:ℚ)⟩ thresholdNode1269
def thresholdNode1271 : BoxExpr 1 := .mul ⟨(249697096907002230389711/2361183241434822606848:ℚ),(627705947495064552818053/4722366482869645213696:ℚ)⟩ thresholdNode1266 thresholdNode1270
def thresholdNode1272 : BoxExpr 1 := .add ⟨(252058280148437052996559/2361183241434822606848:ℚ),(632428313977934198031749/4722366482869645213696:ℚ)⟩ thresholdNode1271 thresholdNode12
def thresholdNode1273 : BoxExpr 1 := .sqrt ⟨(3049476868434191985315/295147905179352825856:ℚ),(54649412373301479083521/4722366482869645213696:ℚ)⟩ thresholdNode1272
def thresholdNode1274 : BoxExpr 1 := .add ⟨(3344624773613544811171/295147905179352825856:ℚ),(59371778856171124297217/4722366482869645213696:ℚ)⟩ thresholdNode1273 thresholdNode12
def thresholdNode1275 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode1276 : BoxExpr 1 := .mul ⟨(3344624773613544811171/590295810358705651712:ℚ),(29685889428085562148609/4722366482869645213696:ℚ)⟩ thresholdNode1274 thresholdNode1275
def thresholdNode1277 : BoxExpr 1 := .add ⟨(3492198726203221224099/590295810358705651712:ℚ),(30866481048802973452033/4722366482869645213696:ℚ)⟩ thresholdNode1276 thresholdNode193
def thresholdNode1278 : BoxExpr 1 := .mul ⟨(26784891401953222162181/4722366482869645213696:ℚ),(30228654155255443258439/4722366482869645213696:ℚ)⟩ thresholdNode1106 thresholdNode1277
def thresholdNode1279 : BoxExpr 1 := .neg ⟨(-30228654155255443258439/4722366482869645213696:ℚ),(-26784891401953222162181/4722366482869645213696:ℚ)⟩ thresholdNode1278
def thresholdNode1280 : BoxExpr 1 := .add ⟨(-2352100577981579364987/4722366482869645213696:ℚ),(764003110626601285559/1180591620717411303424:ℚ)⟩ thresholdNode1262 thresholdNode1279
def thresholdNode1281 : BoxExpr 1 := .mul ⟨(7215344286063561955955/1180591620717411303424:ℚ),(7215344286063561955981/1180591620717411303424:ℚ)⟩ thresholdNode1137 thresholdNode1137
def thresholdNode1282 : BoxExpr 1 := .mul ⟨(-819035436872704091751/2361183241434822606848:ℚ),(-409517718436352045875/1180591620717411303424:ℚ)⟩ thresholdNode1124 thresholdNode5
def thresholdNode1283 : BoxExpr 1 := .neg ⟨(409517718436352045875/1180591620717411303424:ℚ),(819035436872704091751/2361183241434822606848:ℚ)⟩ thresholdNode1282
def thresholdNode1284 : BoxExpr 1 := .add ⟨(1590109339153763349299/1180591620717411303424:ℚ),(3180218678307526698599/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode1283
def thresholdNode1285 : BoxExpr 1 := .mul ⟨(946894421796304877925479/4722366482869645213696:ℚ),(946894421796304877925779/4722366482869645213696:ℚ)⟩ thresholdNode1284 thresholdNode180
def thresholdNode1286 : BoxExpr 1 := .mul ⟨(-819035436872704091751/1180591620717411303424:ℚ),(-409517718436352045875/590295810358705651712:ℚ)⟩ thresholdNode1124 thresholdNode182
def thresholdNode1287 : BoxExpr 1 := .neg ⟨(409517718436352045875/590295810358705651712:ℚ),(819035436872704091751/1180591620717411303424:ℚ)⟩ thresholdNode1286
def thresholdNode1288 : BoxExpr 1 := .add ⟨(999813528795057697587/590295810358705651712:ℚ),(1999627057590115395175/1180591620717411303424:ℚ)⟩ thresholdNode12 thresholdNode1287
def thresholdNode1289 : BoxExpr 1 := .inv ⟨(697028263154191175453/1180591620717411303424:ℚ),(1394056526308382350907/2361183241434822606848:ℚ)⟩ thresholdNode1288
def thresholdNode1290 : BoxExpr 1 := .mul ⟨(559052057149109891025885/4722366482869645213696:ℚ),(17470376785909684094577/147573952589676412928:ℚ)⟩ thresholdNode1285 thresholdNode1289
def thresholdNode1291 : BoxExpr 1 := .add ⟨(563774423631979536239581/4722366482869645213696:ℚ),(17617950738499360507505/147573952589676412928:ℚ)⟩ thresholdNode1290 thresholdNode12
def thresholdNode1292 : BoxExpr 1 := .sqrt ⟨(25798979834766783828059/2361183241434822606848:ℚ),(25798979834766783828073/2361183241434822606848:ℚ)⟩ thresholdNode1291
def thresholdNode1293 : BoxExpr 1 := .add ⟨(28160163076201606434907/2361183241434822606848:ℚ),(28160163076201606434921/2361183241434822606848:ℚ)⟩ thresholdNode1292 thresholdNode12
def thresholdNode1294 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode1295 : BoxExpr 1 := .mul ⟨(28160163076201606434907/4722366482869645213696:ℚ),(28160163076201606434921/4722366482869645213696:ℚ)⟩ thresholdNode1293 thresholdNode1294
def thresholdNode1296 : BoxExpr 1 := .add ⟨(29340754696919017738331/4722366482869645213696:ℚ),(29340754696919017738345/4722366482869645213696:ℚ)⟩ thresholdNode1295 thresholdNode193
def thresholdNode1297 : BoxExpr 1 := .mul ⟨(3557271022106106704121/590295810358705651712:ℚ),(28458168176848853632995/4722366482869645213696:ℚ)⟩ thresholdNode1127 thresholdNode1296
def thresholdNode1298 : BoxExpr 1 := .neg ⟨(-28458168176848853632995/4722366482869645213696:ℚ),(-3557271022106106704121/590295810358705651712:ℚ)⟩ thresholdNode1297
def thresholdNode1299 : BoxExpr 1 := .add ⟨(403208967405394190825/4722366482869645213696:ℚ),(100802241851348547739/1180591620717411303424:ℚ)⟩ thresholdNode1281 thresholdNode1298
def thresholdNode1300 : BoxExpr 1 := .mul ⟨(676058348426182053371/295147905179352825856:ℚ),(5408466787409456426997/2361183241434822606848:ℚ)⟩ thresholdNode1175 thresholdNode1137
def thresholdNode1301 : BoxExpr 1 := .mul ⟨(676058348426182053371/295147905179352825856:ℚ),(5408466787409456426997/2361183241434822606848:ℚ)⟩ thresholdNode1137 thresholdNode1175
def thresholdNode1302 : BoxExpr 1 := .add ⟨(676058348426182053371/147573952589676412928:ℚ),(5408466787409456426997/1180591620717411303424:ℚ)⟩ thresholdNode1300 thresholdNode1301
def thresholdNode1303 : BoxExpr 1 := .mul ⟨(5088787142746892138989/2361183241434822606848:ℚ),(2544393571373446069499/1180591620717411303424:ℚ)⟩ thresholdNode1156 thresholdNode1296
def thresholdNode1304 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode1305 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1124 thresholdNode51
def thresholdNode1306 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode1304 thresholdNode1305
def thresholdNode1307 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode1306
def thresholdNode1308 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode1307
def thresholdNode1309 : BoxExpr 1 := .mul ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode1308 thresholdNode180
def thresholdNode1310 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1284 thresholdNode51
def thresholdNode1311 : BoxExpr 1 := .add ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode1309 thresholdNode1310
def thresholdNode1312 : BoxExpr 1 := .mul ⟨(-51884181637968435362075/295147905179352825856:ℚ),(-415073453103747482896301/2361183241434822606848:ℚ)⟩ thresholdNode1311 thresholdNode1289
def thresholdNode1313 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode12 thresholdNode182
def thresholdNode1314 : BoxExpr 1 := .add ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode1313 thresholdNode1305
def thresholdNode1315 : BoxExpr 1 := .neg ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode1314
def thresholdNode1316 : BoxExpr 1 := .add ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode51 thresholdNode1315
def thresholdNode1317 : BoxExpr 1 := .mul ⟨(13547473315173031802301/4722366482869645213696:ℚ),(13547473315173031802315/4722366482869645213696:ℚ)⟩ thresholdNode1288 thresholdNode1288
def thresholdNode1318 : BoxExpr 1 := .inv ⟨(1646118407449012370073/4722366482869645213696:ℚ),(1646118407449012370075/4722366482869645213696:ℚ)⟩ thresholdNode1317
def thresholdNode1319 : BoxExpr 1 := .mul ⟨(-1646118407449012370075/1180591620717411303424:ℚ),(-1646118407449012370073/1180591620717411303424:ℚ)⟩ thresholdNode1316 thresholdNode1318
def thresholdNode1320 : BoxExpr 1 := .neg ⟨(1646118407449012370073/1180591620717411303424:ℚ),(1646118407449012370075/1180591620717411303424:ℚ)⟩ thresholdNode1319
def thresholdNode1321 : BoxExpr 1 := .mul ⟨(660135270434373303056193/2361183241434822606848:ℚ),(1320270540868746606114409/4722366482869645213696:ℚ)⟩ thresholdNode1285 thresholdNode1320
def thresholdNode1322 : BoxExpr 1 := .add ⟨(245061817330625820159593/2361183241434822606848:ℚ),(490123634661251640321807/4722366482869645213696:ℚ)⟩ thresholdNode1312 thresholdNode1321
def thresholdNode1323 : BoxExpr 1 := .add ⟨(245061817330625820159593/2361183241434822606848:ℚ),(490123634661251640321807/4722366482869645213696:ℚ)⟩ thresholdNode1322 thresholdNode51
def thresholdNode1324 : BoxExpr 1 := .mul ⟨(25798979834766783828059/1180591620717411303424:ℚ),(25798979834766783828073/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode1292
def thresholdNode1325 : BoxExpr 1 := .inv ⟨(54025259286798597961/1180591620717411303424:ℚ),(216101037147194391845/4722366482869645213696:ℚ)⟩ thresholdNode1324
def thresholdNode1326 : BoxExpr 1 := .mul ⟨(5607158305314693278005/1180591620717411303424:ℚ),(22428633221258773112245/4722366482869645213696:ℚ)⟩ thresholdNode1323 thresholdNode1325
def thresholdNode1327 : BoxExpr 1 := .add ⟨(5607158305314693278005/1180591620717411303424:ℚ),(22428633221258773112245/4722366482869645213696:ℚ)⟩ thresholdNode1326 thresholdNode51
def thresholdNode1328 : BoxExpr 1 := .mul ⟨(5607158305314693278005/2361183241434822606848:ℚ),(11214316610629386556123/4722366482869645213696:ℚ)⟩ thresholdNode1327 thresholdNode1294
def thresholdNode1329 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode1330 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode1329
def thresholdNode1331 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1330
def thresholdNode1332 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1331
def thresholdNode1333 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1293 thresholdNode1332
def thresholdNode1334 : BoxExpr 1 := .add ⟨(5607158305314693278005/2361183241434822606848:ℚ),(11214316610629386556123/4722366482869645213696:ℚ)⟩ thresholdNode1328 thresholdNode1333
def thresholdNode1335 : BoxExpr 1 := .add ⟨(5607158305314693278005/2361183241434822606848:ℚ),(11214316610629386556123/4722366482869645213696:ℚ)⟩ thresholdNode1334 thresholdNode51
def thresholdNode1336 : BoxExpr 1 := .mul ⟨(10876983615122636869101/4722366482869645213696:ℚ),(10876983615122636869217/4722366482869645213696:ℚ)⟩ thresholdNode1127 thresholdNode1335
def thresholdNode1337 : BoxExpr 1 := .add ⟨(21054557900616421147079/4722366482869645213696:ℚ),(21054557900616421147213/4722366482869645213696:ℚ)⟩ thresholdNode1303 thresholdNode1336
def thresholdNode1338 : BoxExpr 1 := .neg ⟨(-21054557900616421147213/4722366482869645213696:ℚ),(-21054557900616421147079/4722366482869645213696:ℚ)⟩ thresholdNode1337
def thresholdNode1339 : BoxExpr 1 := .add ⟨(579309249021404560659/4722366482869645213696:ℚ),(579309249021404560909/4722366482869645213696:ℚ)⟩ thresholdNode1302 thresholdNode1338
def thresholdNode1340 : BoxExpr 1 := .mul ⟨(-3314783375748868577073/1180591620717411303424:ℚ),(-11818397989244738132963/4722366482869645213696:ℚ)⟩ thresholdNode1261 thresholdNode1116
def thresholdNode1341 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1204 thresholdNode1107
def thresholdNode1342 : BoxExpr 1 := .mul ⟨(1783062047565900199619/4722366482869645213696:ℚ),(2546462882596875864789/4722366482869645213696:ℚ)⟩ thresholdNode1102 thresholdNode1212
def thresholdNode1343 : BoxExpr 1 := .add ⟨(1783062047565900199619/4722366482869645213696:ℚ),(2546462882596875864789/4722366482869645213696:ℚ)⟩ thresholdNode1341 thresholdNode1342
def thresholdNode1344 : BoxExpr 1 := .mul ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode1238 thresholdNode22
def thresholdNode1345 : BoxExpr 1 := .add ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode1344 thresholdNode1241
def thresholdNode1346 : BoxExpr 1 := .neg ⟨(1685884834384463341289/2361183241434822606848:ℚ),(3371769668768926682579/4722366482869645213696:ℚ)⟩ thresholdNode1345
def thresholdNode1347 : BoxExpr 1 := .add ⟨(5154831716334826882197/4722366482869645213696:ℚ),(739779068920725318421/590295810358705651712:ℚ)⟩ thresholdNode1343 thresholdNode1346
def thresholdNode1348 : BoxExpr 1 := .mul ⟨(-173701920895678621837/590295810358705651712:ℚ),(-463205122388476324897/2361183241434822606848:ℚ)⟩ thresholdNode1255 thresholdNode27
def thresholdNode1349 : BoxExpr 1 := .add ⟨(-173701920895678621837/590295810358705651712:ℚ),(-463205122388476324897/2361183241434822606848:ℚ)⟩ thresholdNode1348 thresholdNode1258
def thresholdNode1350 : BoxExpr 1 := .add ⟨(3765216349169397907501/4722366482869645213696:ℚ),(2495911153294424948787/2361183241434822606848:ℚ)⟩ thresholdNode1347 thresholdNode1349
def thresholdNode1351 : BoxExpr 1 := .mul ⟨(1501032819824443829339/2361183241434822606848:ℚ),(5276653142222012237735/4722366482869645213696:ℚ)⟩ thresholdNode1350 thresholdNode1350
def thresholdNode1352 : BoxExpr 1 := .add ⟨(-5128533931673293324807/2361183241434822606848:ℚ),(-1635436211755681473807/1180591620717411303424:ℚ)⟩ thresholdNode1340 thresholdNode1351
def thresholdNode1353 : BoxExpr 1 := .mul ⟨(-3314783375748868577073/1180591620717411303424:ℚ),(-11818397989244738132963/4722366482869645213696:ℚ)⟩ thresholdNode1116 thresholdNode1261
def thresholdNode1354 : BoxExpr 1 := .add ⟨(-5128533931673293324807/2361183241434822606848:ℚ),(-1635436211755681473807/1180591620717411303424:ℚ)⟩ thresholdNode1351 thresholdNode1353
def thresholdNode1355 : BoxExpr 1 := .add ⟨(-5128533931673293324807/1180591620717411303424:ℚ),(-1635436211755681473807/590295810358705651712:ℚ)⟩ thresholdNode1352 thresholdNode1354
def thresholdNode1356 : BoxExpr 1 := .mul ⟨(-30866481048802973452033/2361183241434822606848:ℚ),(-3492198726203221224099/295147905179352825856:ℚ)⟩ thresholdNode1222 thresholdNode1277
def thresholdNode1357 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode1358 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode1357 thresholdNode1218
def thresholdNode1359 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode1358
def thresholdNode1360 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode1359
def thresholdNode1361 : BoxExpr 1 := .mul ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode1360 thresholdNode180
def thresholdNode1362 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1265 thresholdNode51
def thresholdNode1363 : BoxExpr 1 := .add ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode1361 thresholdNode1362
def thresholdNode1364 : BoxExpr 1 := .mul ⟨(-892737347548536252896785/4722366482869645213696:ℚ),(-775757970973210812861443/4722366482869645213696:ℚ)⟩ thresholdNode1363 thresholdNode1270
def thresholdNode1365 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode12 thresholdNode182
def thresholdNode1366 : BoxExpr 1 := .add ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode1365 thresholdNode1218
def thresholdNode1367 : BoxExpr 1 := .neg ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode1366
def thresholdNode1368 : BoxExpr 1 := .add ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode51 thresholdNode1367
def thresholdNode1369 : BoxExpr 1 := .mul ⟨(5857210178284256829107/2361183241434822606848:ℚ),(841/256:ℚ)⟩ thresholdNode1269 thresholdNode1269
def thresholdNode1370 : BoxExpr 1 := .inv ⟨(718743055656735537875/2361183241434822606848:ℚ),(1903700270242235409907/4722366482869645213696:ℚ)⟩ thresholdNode1369
def thresholdNode1371 : BoxExpr 1 := .mul ⟨(-1903700270242235409907/1180591620717411303424:ℚ),(-718743055656735537875/590295810358705651712:ℚ)⟩ thresholdNode1368 thresholdNode1370
def thresholdNode1372 : BoxExpr 1 := .neg ⟨(718743055656735537875/590295810358705651712:ℚ),(1903700270242235409907/1180591620717411303424:ℚ)⟩ thresholdNode1371
def thresholdNode1373 : BoxExpr 1 := .mul ⟨(34440978883724445570993/147573952589676412928:ℚ),(797086917454050225801107/2361183241434822606848:ℚ)⟩ thresholdNode1266 thresholdNode1372
def thresholdNode1374 : BoxExpr 1 := .add ⟨(209373976730646005374991/4722366482869645213696:ℚ),(818415863934889638740771/4722366482869645213696:ℚ)⟩ thresholdNode1364 thresholdNode1373
def thresholdNode1375 : BoxExpr 1 := .add ⟨(209373976730646005374991/4722366482869645213696:ℚ),(818415863934889638740771/4722366482869645213696:ℚ)⟩ thresholdNode1374 thresholdNode51
def thresholdNode1376 : BoxExpr 1 := .mul ⟨(3049476868434191985315/147573952589676412928:ℚ),(54649412373301479083521/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode1273
def thresholdNode1377 : BoxExpr 1 := .inv ⟨(204034629377144673395/4722366482869645213696:ℚ),(228530438996875148017/4722366482869645213696:ℚ)⟩ thresholdNode1376
def thresholdNode1378 : BoxExpr 1 := .mul ⟨(9046214837078219223515/4722366482869645213696:ℚ),(4950720611834870619197/590295810358705651712:ℚ)⟩ thresholdNode1375 thresholdNode1377
def thresholdNode1379 : BoxExpr 1 := .add ⟨(9046214837078219223515/4722366482869645213696:ℚ),(4950720611834870619197/590295810358705651712:ℚ)⟩ thresholdNode1378 thresholdNode51
def thresholdNode1380 : BoxExpr 1 := .mul ⟨(4523107418539109611757/4722366482869645213696:ℚ),(4950720611834870619197/1180591620717411303424:ℚ)⟩ thresholdNode1379 thresholdNode1275
def thresholdNode1381 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode1382 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode1381
def thresholdNode1383 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1382
def thresholdNode1384 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1383
def thresholdNode1385 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1274 thresholdNode1384
def thresholdNode1386 : BoxExpr 1 := .add ⟨(4523107418539109611757/4722366482869645213696:ℚ),(4950720611834870619197/1180591620717411303424:ℚ)⟩ thresholdNode1380 thresholdNode1385
def thresholdNode1387 : BoxExpr 1 := .add ⟨(4523107418539109611757/4722366482869645213696:ℚ),(4950720611834870619197/1180591620717411303424:ℚ)⟩ thresholdNode1386 thresholdNode51
def thresholdNode1388 : BoxExpr 1 := .mul ⟨(650196691414997006689/2361183241434822606848:ℚ),(2011230248557916189049/1180591620717411303424:ℚ)⟩ thresholdNode1209 thresholdNode1387
def thresholdNode1389 : BoxExpr 1 := .add ⟨(-944258886168374263917/73786976294838206464:ℚ),(-11957564656254968707347/1180591620717411303424:ℚ)⟩ thresholdNode1356 thresholdNode1388
def thresholdNode1390 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode5
def thresholdNode1391 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode12 thresholdNode51
def thresholdNode1392 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1390 thresholdNode1391
def thresholdNode1393 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1391 thresholdNode1218
def thresholdNode1394 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1392 thresholdNode1393
def thresholdNode1395 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1394
def thresholdNode1396 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1395
def thresholdNode1397 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1396 thresholdNode180
def thresholdNode1398 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1360 thresholdNode51
def thresholdNode1399 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1397 thresholdNode1398
def thresholdNode1400 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1398 thresholdNode1362
def thresholdNode1401 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1399 thresholdNode1400
def thresholdNode1402 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1401 thresholdNode1270
def thresholdNode1403 : BoxExpr 1 := .mul ⟨(-2267269454091520642278703/4722366482869645213696:ℚ),(-107001099444580801773987/295147905179352825856:ℚ)⟩ thresholdNode1363 thresholdNode1372
def thresholdNode1404 : BoxExpr 1 := .add ⟨(-2267269454091520642278703/4722366482869645213696:ℚ),(-107001099444580801773987/295147905179352825856:ℚ)⟩ thresholdNode1402 thresholdNode1403
def thresholdNode1405 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode182
def thresholdNode1406 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1405 thresholdNode1391
def thresholdNode1407 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1406 thresholdNode1393
def thresholdNode1408 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1407
def thresholdNode1409 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1408
def thresholdNode1410 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1409 thresholdNode1370
def thresholdNode1411 : BoxExpr 1 := .mul ⟨(-29/4:ℚ),(-464857950657480700723/73786976294838206464:ℚ)⟩ thresholdNode1368 thresholdNode1269
def thresholdNode1412 : BoxExpr 1 := .mul ⟨(-29/4:ℚ),(-464857950657480700723/73786976294838206464:ℚ)⟩ thresholdNode1269 thresholdNode1368
def thresholdNode1413 : BoxExpr 1 := .add ⟨(-29/2:ℚ),(-464857950657480700723/36893488147419103232:ℚ)⟩ thresholdNode1411 thresholdNode1412
def thresholdNode1414 : BoxExpr 1 := .mul ⟨(7264770999253192298345/1180591620717411303424:ℚ),(707281/65536:ℚ)⟩ thresholdNode1369 thresholdNode1369
def thresholdNode1415 : BoxExpr 1 := .inv ⟨(437570088580557188337/4722366482869645213696:ℚ),(767427672559228182377/4722366482869645213696:ℚ)⟩ thresholdNode1414
def thresholdNode1416 : BoxExpr 1 := .mul ⟨(-11127701252108808644467/4722366482869645213696:ℚ),(-5513383116115020573043/4722366482869645213696:ℚ)⟩ thresholdNode1413 thresholdNode1415
def thresholdNode1417 : BoxExpr 1 := .neg ⟨(5513383116115020573043/4722366482869645213696:ℚ),(11127701252108808644467/4722366482869645213696:ℚ)⟩ thresholdNode1416
def thresholdNode1418 : BoxExpr 1 := .mul ⟨(-11127701252108808644467/1180591620717411303424:ℚ),(-5513383116115020573043/1180591620717411303424:ℚ)⟩ thresholdNode1368 thresholdNode1417
def thresholdNode1419 : BoxExpr 1 := .add ⟨(-11127701252108808644467/1180591620717411303424:ℚ),(-5513383116115020573043/1180591620717411303424:ℚ)⟩ thresholdNode1410 thresholdNode1418
def thresholdNode1420 : BoxExpr 1 := .neg ⟨(5513383116115020573043/1180591620717411303424:ℚ),(11127701252108808644467/1180591620717411303424:ℚ)⟩ thresholdNode1419
def thresholdNode1421 : BoxExpr 1 := .mul ⟨(4227075252788264318993753/4722366482869645213696:ℚ),(9318426044310388127289193/4722366482869645213696:ℚ)⟩ thresholdNode1266 thresholdNode1420
def thresholdNode1422 : BoxExpr 1 := .add ⟨(979902899348371838357525/2361183241434822606848:ℚ),(7606408453197095298905401/4722366482869645213696:ℚ)⟩ thresholdNode1403 thresholdNode1421
def thresholdNode1423 : BoxExpr 1 := .add ⟨(-307463655394776965563653/4722366482869645213696:ℚ),(5894390862083802470521609/4722366482869645213696:ℚ)⟩ thresholdNode1404 thresholdNode1422
def thresholdNode1424 : BoxExpr 1 := .add ⟨(-307463655394776965563653/4722366482869645213696:ℚ),(5894390862083802470521609/4722366482869645213696:ℚ)⟩ thresholdNode1423 thresholdNode51
def thresholdNode1425 : BoxExpr 1 := .mul ⟨(-1859893879420346133365/590295810358705651712:ℚ),(142624226245208618158783/2361183241434822606848:ℚ)⟩ thresholdNode1424 thresholdNode1377
def thresholdNode1426 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1273
def thresholdNode1427 : BoxExpr 1 := .mul ⟨(9046214837078219223515/2361183241434822606848:ℚ),(4950720611834870619197/295147905179352825856:ℚ)⟩ thresholdNode5 thresholdNode1378
def thresholdNode1428 : BoxExpr 1 := .add ⟨(9046214837078219223515/2361183241434822606848:ℚ),(4950720611834870619197/295147905179352825856:ℚ)⟩ thresholdNode1426 thresholdNode1427
def thresholdNode1429 : BoxExpr 1 := .mul ⟨(126029140074218526498279/295147905179352825856:ℚ),(79053539247241774753969/147573952589676412928:ℚ)⟩ thresholdNode1376 thresholdNode1376
def thresholdNode1430 : BoxExpr 1 := .inv ⟨(8815522923958109453/4722366482869645213696:ℚ),(5529659942483768121/2361183241434822606848:ℚ)⟩ thresholdNode1429
def thresholdNode1431 : BoxExpr 1 := .mul ⟨(16887108309063934895/2361183241434822606848:ℚ),(185505646310154463409/4722366482869645213696:ℚ)⟩ thresholdNode1428 thresholdNode1430
def thresholdNode1432 : BoxExpr 1 := .neg ⟨(-185505646310154463409/4722366482869645213696:ℚ),(-16887108309063934895/2361183241434822606848:ℚ)⟩ thresholdNode1431
def thresholdNode1433 : BoxExpr 1 := .mul ⟨(-32149297251802460810947/4722366482869645213696:ℚ),(-374359024757571965097/1180591620717411303424:ℚ)⟩ thresholdNode1375 thresholdNode1432
def thresholdNode1434 : BoxExpr 1 := .add ⟨(-47028448287165229877867/4722366482869645213696:ℚ),(141875508195693474228589/2361183241434822606848:ℚ)⟩ thresholdNode1425 thresholdNode1433
def thresholdNode1435 : BoxExpr 1 := .add ⟨(-47028448287165229877867/4722366482869645213696:ℚ),(141875508195693474228589/2361183241434822606848:ℚ)⟩ thresholdNode1434 thresholdNode51
def thresholdNode1436 : BoxExpr 1 := .mul ⟨(-11757112071791307469467/2361183241434822606848:ℚ),(141875508195693474228589/4722366482869645213696:ℚ)⟩ thresholdNode1435 thresholdNode1275
def thresholdNode1437 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1379 thresholdNode1384
def thresholdNode1438 : BoxExpr 1 := .add ⟨(-11757112071791307469467/2361183241434822606848:ℚ),(141875508195693474228589/4722366482869645213696:ℚ)⟩ thresholdNode1436 thresholdNode1437
def thresholdNode1439 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode5 thresholdNode51
def thresholdNode1440 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1390 thresholdNode1439
def thresholdNode1441 : BoxExpr 1 := .mul ⟨(16/1:ℚ),(16/1:ℚ)⟩ thresholdNode1381 thresholdNode1381
def thresholdNode1442 : BoxExpr 1 := .inv ⟨(1/16:ℚ),(1/16:ℚ)⟩ thresholdNode1441
def thresholdNode1443 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1440 thresholdNode1442
def thresholdNode1444 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1443
def thresholdNode1445 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1444
def thresholdNode1446 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1383 thresholdNode1445
def thresholdNode1447 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1446
def thresholdNode1448 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1274 thresholdNode1447
def thresholdNode1449 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1437 thresholdNode1448
def thresholdNode1450 : BoxExpr 1 := .add ⟨(-11757112071791307469467/2361183241434822606848:ℚ),(141875508195693474228589/4722366482869645213696:ℚ)⟩ thresholdNode1438 thresholdNode1449
def thresholdNode1451 : BoxExpr 1 := .add ⟨(-11757112071791307469467/2361183241434822606848:ℚ),(141875508195693474228589/4722366482869645213696:ℚ)⟩ thresholdNode1450 thresholdNode51
def thresholdNode1452 : BoxExpr 1 := .mul ⟨(-11514162373120307404963/2361183241434822606848:ℚ),(138943783827118402046307/4722366482869645213696:ℚ)⟩ thresholdNode1106 thresholdNode1451
def thresholdNode1453 : BoxExpr 1 := .add ⟨(-5431982840852655199137/1180591620717411303424:ℚ),(146988704821350066802503/4722366482869645213696:ℚ)⟩ thresholdNode1388 thresholdNode1452
def thresholdNode1454 : BoxExpr 1 := .add ⟨(-20540125019546643421809/1180591620717411303424:ℚ),(99158446196330191973115/4722366482869645213696:ℚ)⟩ thresholdNode1389 thresholdNode1453
def thresholdNode1455 : BoxExpr 1 := .neg ⟨(-99158446196330191973115/4722366482869645213696:ℚ),(20540125019546643421809/1180591620717411303424:ℚ)⟩ thresholdNode1454
def thresholdNode1456 : BoxExpr 1 := .add ⟨(-119672581923023365272343/4722366482869645213696:ℚ),(17269252596035280474195/1180591620717411303424:ℚ)⟩ thresholdNode1355 thresholdNode1455
def thresholdCell3Out1 : TaylorCertificate1 :=
  { center := (-111/640:ℚ), radius := (19/640:ℚ)
    whole := thresholdNode1280, centerValue := thresholdNode1299, gradient := thresholdNode1339, hessian := thresholdNode1456 }
theorem thresholdCell3Out1_check : thresholdCell3Out1.check = true := by decide +kernel
theorem thresholdCell3Out1_lower_pos : 0 < thresholdCell3Out1.lower := by decide +kernel
theorem thresholdCell3Out1_positive (x : ℝ) (hx : (-(13/64:ℝ)) ≤ x ∧ x ≤ (-(23/160:ℝ))) :
    0 < thresholdNode1280.eval (fun _ => x) := by
  apply thresholdCell3Out1.positive_sound thresholdCell3Out1_check thresholdCell3Out1_lower_pos x
  norm_num [thresholdCell3Out1]
  exact hx
theorem thresholdCell3_public (x : ℝ)
    (hx : (-(13/64:ℝ)) ≤ x ∧ x ≤ (-(23/160:ℝ))) : qc x < fA (43/20) x := by
  have hf := thresholdCell3Out0_positive x hx
  have hg := thresholdCell3Out1_positive x hx
  have hfa : thresholdNode1116.eval (fun _ => x) = thresholdFA 0 x := by
    norm_num [thresholdNode0, thresholdNode1, thresholdNode1096, thresholdNode3, thresholdNode1097, thresholdNode5, thresholdNode1098, thresholdNode1099, thresholdNode1100, thresholdNode9, thresholdNode1101, thresholdNode1102, thresholdNode12, thresholdNode1103, thresholdNode1104, thresholdNode1105, thresholdNode1106, thresholdNode1107, thresholdNode1108, thresholdNode19, thresholdNode1109, thresholdNode1110, thresholdNode22, thresholdNode1111, thresholdNode1112, thresholdNode1113, thresholdNode1114, thresholdNode27, thresholdNode1115, thresholdNode1116, BoxExpr.eval, thresholdFA, ftilde, pow_two, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  have hgap : thresholdNode1280.eval (fun _ => x) =
      (thresholdNode1116.eval (fun _ => x))^2 - (1-x^2)*(thresholdCapacity 1 x+1/4) := by
    norm_num [thresholdNode1262, thresholdNode12, thresholdNode1103, thresholdNode1104, thresholdNode1105, thresholdNode1106, thresholdNode5, thresholdNode1263, thresholdNode1264, thresholdNode1265, thresholdNode180, thresholdNode1266, thresholdNode182, thresholdNode1267, thresholdNode1268, thresholdNode1269, thresholdNode1270, thresholdNode1271, thresholdNode1272, thresholdNode1273, thresholdNode1274, thresholdNode1275, thresholdNode1276, thresholdNode193, thresholdNode1277, thresholdNode1278, thresholdNode1279, thresholdNode1280, BoxExpr.eval, thresholdCapacity, Da, D5, beta5, eta5, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  rw [hfa] at hf
  rw [hgap, hfa] at hg
  refine threshold_positive_to_public 0 1 x ?_ ?_ ?_ hf hg
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdFADomain] <;> constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdCapacityDomain] <;> linarith [hx.1,hx.2]
def thresholdNode1457 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode1458 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode1457 thresholdNode3
def thresholdNode1459 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode1460 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1459
def thresholdNode1461 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode1460 thresholdNode1460
def thresholdNode1462 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode1461 thresholdNode9
def thresholdNode1463 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode1458 thresholdNode1462
def thresholdNode1464 : BoxExpr 1 := .var 0
def thresholdNode1465 : BoxExpr 1 := .mul ⟨(8404797768583914455/1180591620717411303424:ℚ),(97583276149923528049/4722366482869645213696:ℚ)⟩ thresholdNode1464 thresholdNode1464
def thresholdNode1466 : BoxExpr 1 := .neg ⟨(-97583276149923528049/4722366482869645213696:ℚ),(-8404797768583914455/1180591620717411303424:ℚ)⟩ thresholdNode1465
def thresholdNode1467 : BoxExpr 1 := .add ⟨(4624783206719721685647/4722366482869645213696:ℚ),(1172186822948827388969/1180591620717411303424:ℚ)⟩ thresholdNode12 thresholdNode1466
def thresholdNode1468 : BoxExpr 1 := .sqrt ⟨(4673320148026626629985/4722366482869645213696:ℚ),(4705526862894312506767/4722366482869645213696:ℚ)⟩ thresholdNode1467
def thresholdNode1469 : BoxExpr 1 := .mul ⟨(6073797363386505965323/2361183241434822606848:ℚ),(6115655625532165607235/2361183241434822606848:ℚ)⟩ thresholdNode1463 thresholdNode1468
def thresholdNode1470 : BoxExpr 1 := .neg ⟨(398449671992126314905/4722366482869645213696:ℚ),(678840181912511499469/4722366482869645213696:ℚ)⟩ thresholdNode1464
def thresholdNode1471 : BoxExpr 1 := .add ⟨(140195254960192592281/2361183241434822606848:ℚ),(560781019840770369127/4722366482869645213696:ℚ)⟩ thresholdNode19 thresholdNode1470
def thresholdNode1472 : BoxExpr 1 := .mul ⟨(200198824083155021777/4722366482869645213696:ℚ),(400397648166310043557/4722366482869645213696:ℚ)⟩ thresholdNode1471 thresholdNode22
def thresholdNode1473 : BoxExpr 1 := .neg ⟨(-400397648166310043557/4722366482869645213696:ℚ),(-200198824083155021777/4722366482869645213696:ℚ)⟩ thresholdNode1472
def thresholdNode1474 : BoxExpr 1 := .add ⟨(11747197078606701887089/4722366482869645213696:ℚ),(12031112426981176192693/4722366482869645213696:ℚ)⟩ thresholdNode1469 thresholdNode1473
def thresholdNode1475 : BoxExpr 1 := .mul ⟨(16648186526522870333/4722366482869645213696:ℚ),(33296373053045740667/2361183241434822606848:ℚ)⟩ thresholdNode1471 thresholdNode1471
def thresholdNode1476 : BoxExpr 1 := .mul ⟨(13751402070907890895/4722366482869645213696:ℚ),(27502804141815781791/2361183241434822606848:ℚ)⟩ thresholdNode1475 thresholdNode27
def thresholdNode1477 : BoxExpr 1 := .add ⟨(183764820010587652781/73786976294838206464:ℚ),(12086118035264807756275/4722366482869645213696:ℚ)⟩ thresholdNode1474 thresholdNode1476
def thresholdNode1478 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode1479 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode1478 thresholdNode3
def thresholdNode1480 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode1481 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1480
def thresholdNode1482 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode1481 thresholdNode1481
def thresholdNode1483 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode1482 thresholdNode9
def thresholdNode1484 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode1479 thresholdNode1483
def thresholdNode1485 : BoxExpr 1 := .var 0
def thresholdNode1486 : BoxExpr 1 := .mul ⟨(30719593490249437675/2361183241434822606848:ℚ),(7679898372562359419/590295810358705651712:ℚ)⟩ thresholdNode1485 thresholdNode1485
def thresholdNode1487 : BoxExpr 1 := .neg ⟨(-7679898372562359419/590295810358705651712:ℚ),(-30719593490249437675/2361183241434822606848:ℚ)⟩ thresholdNode1486
def thresholdNode1488 : BoxExpr 1 := .add ⟨(582615911986143292293/590295810358705651712:ℚ),(2330463647944573169173/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode1487
def thresholdNode1489 : BoxExpr 1 := .sqrt ⟨(1172886579160554268991/1180591620717411303424:ℚ),(2345773158321108537983/2361183241434822606848:ℚ)⟩ thresholdNode1488
def thresholdNode1490 : BoxExpr 1 := .mul ⟨(6097485459081973478201/2361183241434822606848:ℚ),(12194970918163946956417/4722366482869645213696:ℚ)⟩ thresholdNode1484 thresholdNode1489
def thresholdNode1491 : BoxExpr 1 := .neg ⟨(538644926952318907187/4722366482869645213696:ℚ),(134661231738079726797/1180591620717411303424:ℚ)⟩ thresholdNode1485
def thresholdNode1492 : BoxExpr 1 := .add ⟨(105146441220144444211/1180591620717411303424:ℚ),(210292882440288888423/2361183241434822606848:ℚ)⟩ thresholdNode19 thresholdNode1491
def thresholdNode1493 : BoxExpr 1 := .mul ⟨(150149118062366266333/2361183241434822606848:ℚ),(300298236124732532669/4722366482869645213696:ℚ)⟩ thresholdNode1492 thresholdNode22
def thresholdNode1494 : BoxExpr 1 := .neg ⟨(-300298236124732532669/4722366482869645213696:ℚ),(-150149118062366266333/2361183241434822606848:ℚ)⟩ thresholdNode1493
def thresholdNode1495 : BoxExpr 1 := .add ⟨(11894672682039214423733/4722366482869645213696:ℚ),(11894672682039214423751/4722366482869645213696:ℚ)⟩ thresholdNode1490 thresholdNode1494
def thresholdNode1496 : BoxExpr 1 := .mul ⟨(18729209842338229125/2361183241434822606848:ℚ),(37458419684676458251/4722366482869645213696:ℚ)⟩ thresholdNode1492 thresholdNode1492
def thresholdNode1497 : BoxExpr 1 := .mul ⟨(15470327329771377257/2361183241434822606848:ℚ),(7735163664885688629/1180591620717411303424:ℚ)⟩ thresholdNode1496 thresholdNode27
def thresholdNode1498 : BoxExpr 1 := .add ⟨(11925613336698757178247/4722366482869645213696:ℚ),(11925613336698757178267/4722366482869645213696:ℚ)⟩ thresholdNode1495 thresholdNode1497
def thresholdNode1499 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1
def thresholdNode1500 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode51
def thresholdNode1501 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1499 thresholdNode1500
def thresholdNode1502 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1501 thresholdNode51
def thresholdNode1503 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51
def thresholdNode1504 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1503
def thresholdNode1505 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1504 thresholdNode1481
def thresholdNode1506 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1481 thresholdNode1504
def thresholdNode1507 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1505 thresholdNode1506
def thresholdNode1508 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1507 thresholdNode9
def thresholdNode1509 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1482 thresholdNode51
def thresholdNode1510 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1508 thresholdNode1509
def thresholdNode1511 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1502 thresholdNode1510
def thresholdNode1512 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1511 thresholdNode1489
def thresholdNode1513 : BoxExpr 1 := .mul ⟨(-134661231738079726797/1180591620717411303424:ℚ),(-538644926952318907187/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode1485
def thresholdNode1514 : BoxExpr 1 := .mul ⟨(-134661231738079726797/1180591620717411303424:ℚ),(-538644926952318907187/4722366482869645213696:ℚ)⟩ thresholdNode1485 thresholdNode12
def thresholdNode1515 : BoxExpr 1 := .add ⟨(-134661231738079726797/590295810358705651712:ℚ),(-538644926952318907187/2361183241434822606848:ℚ)⟩ thresholdNode1513 thresholdNode1514
def thresholdNode1516 : BoxExpr 1 := .neg ⟨(538644926952318907187/2361183241434822606848:ℚ),(134661231738079726797/590295810358705651712:ℚ)⟩ thresholdNode1515
def thresholdNode1517 : BoxExpr 1 := .add ⟨(538644926952318907187/2361183241434822606848:ℚ),(134661231738079726797/590295810358705651712:ℚ)⟩ thresholdNode51 thresholdNode1516
def thresholdNode1518 : BoxExpr 1 := .mul ⟨(1172886579160554268991/590295810358705651712:ℚ),(2345773158321108537983/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode1489
def thresholdNode1519 : BoxExpr 1 := .inv ⟨(594173639494501248641/1180591620717411303424:ℚ),(1188347278989002497283/2361183241434822606848:ℚ)⟩ thresholdNode1518
def thresholdNode1520 : BoxExpr 1 := .mul ⟨(67772930754841548673/590295810358705651712:ℚ),(542183446038732389387/4722366482869645213696:ℚ)⟩ thresholdNode1517 thresholdNode1519
def thresholdNode1521 : BoxExpr 1 := .mul ⟨(176165567557597379543/590295810358705651712:ℚ),(704662270230389518177/2361183241434822606848:ℚ)⟩ thresholdNode1484 thresholdNode1520
def thresholdNode1522 : BoxExpr 1 := .add ⟨(176165567557597379543/590295810358705651712:ℚ),(704662270230389518177/2361183241434822606848:ℚ)⟩ thresholdNode1512 thresholdNode1521
def thresholdNode1523 : BoxExpr 1 := .neg ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode12
def thresholdNode1524 : BoxExpr 1 := .add ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode51 thresholdNode1523
def thresholdNode1525 : BoxExpr 1 := .mul ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode1524 thresholdNode22
def thresholdNode1526 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1492 thresholdNode51
def thresholdNode1527 : BoxExpr 1 := .add ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode1525 thresholdNode1526
def thresholdNode1528 : BoxExpr 1 := .neg ⟨(1685884834384463341289/2361183241434822606848:ℚ),(3371769668768926682579/4722366482869645213696:ℚ)⟩ thresholdNode1527
def thresholdNode1529 : BoxExpr 1 := .add ⟨(2390547104614852859461/2361183241434822606848:ℚ),(4781094209229705718933/4722366482869645213696:ℚ)⟩ thresholdNode1522 thresholdNode1528
def thresholdNode1530 : BoxExpr 1 := .mul ⟨(-210292882440288888423/2361183241434822606848:ℚ),(-105146441220144444211/1180591620717411303424:ℚ)⟩ thresholdNode1524 thresholdNode1492
def thresholdNode1531 : BoxExpr 1 := .mul ⟨(-210292882440288888423/2361183241434822606848:ℚ),(-105146441220144444211/1180591620717411303424:ℚ)⟩ thresholdNode1492 thresholdNode1524
def thresholdNode1532 : BoxExpr 1 := .add ⟨(-210292882440288888423/1180591620717411303424:ℚ),(-105146441220144444211/590295810358705651712:ℚ)⟩ thresholdNode1530 thresholdNode1531
def thresholdNode1533 : BoxExpr 1 := .mul ⟨(-347403841791357243675/2361183241434822606848:ℚ),(-347403841791357243673/2361183241434822606848:ℚ)⟩ thresholdNode1532 thresholdNode27
def thresholdNode1534 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1496 thresholdNode51
def thresholdNode1535 : BoxExpr 1 := .add ⟨(-347403841791357243675/2361183241434822606848:ℚ),(-347403841791357243673/2361183241434822606848:ℚ)⟩ thresholdNode1533 thresholdNode1534
def thresholdNode1536 : BoxExpr 1 := .add ⟨(1021571631411747807893/1180591620717411303424:ℚ),(4086286525646991231587/4722366482869645213696:ℚ)⟩ thresholdNode1529 thresholdNode1535
def thresholdNode1537 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1
def thresholdNode1538 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode51
def thresholdNode1539 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1537 thresholdNode1538
def thresholdNode1540 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode51
def thresholdNode1541 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1538 thresholdNode1540
def thresholdNode1542 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1539 thresholdNode1541
def thresholdNode1543 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1542 thresholdNode51
def thresholdNode1544 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51
def thresholdNode1545 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1544
def thresholdNode1546 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1545 thresholdNode1460
def thresholdNode1547 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1545 thresholdNode1545
def thresholdNode1548 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1546 thresholdNode1547
def thresholdNode1549 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1460 thresholdNode1545
def thresholdNode1550 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1547 thresholdNode1549
def thresholdNode1551 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1548 thresholdNode1550
def thresholdNode1552 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1551 thresholdNode9
def thresholdNode1553 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1546 thresholdNode1549
def thresholdNode1554 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1553 thresholdNode51
def thresholdNode1555 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1552 thresholdNode1554
def thresholdNode1556 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1461 thresholdNode51
def thresholdNode1557 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1554 thresholdNode1556
def thresholdNode1558 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1555 thresholdNode1557
def thresholdNode1559 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1543 thresholdNode1558
def thresholdNode1560 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1559 thresholdNode1468
def thresholdNode1561 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1537 thresholdNode1540
def thresholdNode1562 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1561 thresholdNode51
def thresholdNode1563 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1553 thresholdNode9
def thresholdNode1564 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1563 thresholdNode1556
def thresholdNode1565 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1562 thresholdNode1564
def thresholdNode1566 : BoxExpr 1 := .mul ⟨(-678840181912511499469/4722366482869645213696:ℚ),(-398449671992126314905/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode1464
def thresholdNode1567 : BoxExpr 1 := .mul ⟨(-678840181912511499469/4722366482869645213696:ℚ),(-398449671992126314905/4722366482869645213696:ℚ)⟩ thresholdNode1464 thresholdNode12
def thresholdNode1568 : BoxExpr 1 := .add ⟨(-678840181912511499469/2361183241434822606848:ℚ),(-398449671992126314905/2361183241434822606848:ℚ)⟩ thresholdNode1566 thresholdNode1567
def thresholdNode1569 : BoxExpr 1 := .neg ⟨(398449671992126314905/2361183241434822606848:ℚ),(678840181912511499469/2361183241434822606848:ℚ)⟩ thresholdNode1568
def thresholdNode1570 : BoxExpr 1 := .add ⟨(398449671992126314905/2361183241434822606848:ℚ),(678840181912511499469/2361183241434822606848:ℚ)⟩ thresholdNode51 thresholdNode1569
def thresholdNode1571 : BoxExpr 1 := .mul ⟨(4673320148026626629985/2361183241434822606848:ℚ),(4705526862894312506767/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode1468
def thresholdNode1572 : BoxExpr 1 := .inv ⟨(1184816591654398994533/2361183241434822606848:ℚ),(2330042752595940843/4611686018427387904:ℚ)⟩ thresholdNode1571
def thresholdNode1573 : BoxExpr 1 := .mul ⟨(199937799841679830327/2361183241434822606848:ℚ),(171491146591061246045/1180591620717411303424:ℚ)⟩ thresholdNode1570 thresholdNode1572
def thresholdNode1574 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1565 thresholdNode1573
def thresholdNode1575 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1560 thresholdNode1574
def thresholdNode1576 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1464
def thresholdNode1577 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode12
def thresholdNode1578 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1576 thresholdNode1577
def thresholdNode1579 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1464 thresholdNode51
def thresholdNode1580 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1577 thresholdNode1579
def thresholdNode1581 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode1578 thresholdNode1580
def thresholdNode1582 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode1581
def thresholdNode1583 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode1582
def thresholdNode1584 : BoxExpr 1 := .mul ⟨(-2330042752595940843/2305843009213693952:ℚ),(-1184816591654398994533/1180591620717411303424:ℚ)⟩ thresholdNode1583 thresholdNode1572
def thresholdNode1585 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1468
def thresholdNode1586 : BoxExpr 1 := .mul ⟨(199937799841679830327/1180591620717411303424:ℚ),(171491146591061246045/590295810358705651712:ℚ)⟩ thresholdNode5 thresholdNode1573
def thresholdNode1587 : BoxExpr 1 := .add ⟨(199937799841679830327/1180591620717411303424:ℚ),(171491146591061246045/590295810358705651712:ℚ)⟩ thresholdNode1585 thresholdNode1586
def thresholdNode1588 : BoxExpr 1 := .mul ⟨(18499132826878886742581/4722366482869645213696:ℚ),(9377494583590619111755/2361183241434822606848:ℚ)⟩ thresholdNode1571 thresholdNode1571
def thresholdNode1589 : BoxExpr 1 := .inv ⟨(1189056682450875052577/4722366482869645213696:ℚ),(1205502193385414597251/4722366482869645213696:ℚ)⟩ thresholdNode1588
def thresholdNode1590 : BoxExpr 1 := .mul ⟨(201371391092720781987/4722366482869645213696:ℚ),(175109622780549954081/2361183241434822606848:ℚ)⟩ thresholdNode1587 thresholdNode1589
def thresholdNode1591 : BoxExpr 1 := .neg ⟨(-175109622780549954081/2361183241434822606848:ℚ),(-201371391092720781987/4722366482869645213696:ℚ)⟩ thresholdNode1590
def thresholdNode1592 : BoxExpr 1 := .mul ⟨(-100688033098816223597/4722366482869645213696:ℚ),(-4247677780862078995/590295810358705651712:ℚ)⟩ thresholdNode1570 thresholdNode1591
def thresholdNode1593 : BoxExpr 1 := .add ⟨(-4872615590415303070061/4722366482869645213696:ℚ),(-1193311947216123152523/1180591620717411303424:ℚ)⟩ thresholdNode1584 thresholdNode1592
def thresholdNode1594 : BoxExpr 1 := .mul ⟨(-395801041717063063599/147573952589676412928:ℚ),(-12407341639984918866037/4722366482869645213696:ℚ)⟩ thresholdNode1463 thresholdNode1593
def thresholdNode1595 : BoxExpr 1 := .add ⟨(-395801041717063063599/147573952589676412928:ℚ),(-12407341639984918866037/4722366482869645213696:ℚ)⟩ thresholdNode1574 thresholdNode1594
def thresholdNode1596 : BoxExpr 1 := .add ⟨(-395801041717063063599/147573952589676412928:ℚ),(-12407341639984918866037/4722366482869645213696:ℚ)⟩ thresholdNode1575 thresholdNode1595
def thresholdNode1597 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1545 thresholdNode22
def thresholdNode1598 : BoxExpr 1 := .neg ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode12
def thresholdNode1599 : BoxExpr 1 := .add ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode51 thresholdNode1598
def thresholdNode1600 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1599 thresholdNode51
def thresholdNode1601 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1597 thresholdNode1600
def thresholdNode1602 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1471 thresholdNode51
def thresholdNode1603 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1600 thresholdNode1602
def thresholdNode1604 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1601 thresholdNode1603
def thresholdNode1605 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1604
def thresholdNode1606 : BoxExpr 1 := .add ⟨(-395801041717063063599/147573952589676412928:ℚ),(-12407341639984918866037/4722366482869645213696:ℚ)⟩ thresholdNode1596 thresholdNode1605
def thresholdNode1607 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1545 thresholdNode1471
def thresholdNode1608 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1599 thresholdNode1599
def thresholdNode1609 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1607 thresholdNode1608
def thresholdNode1610 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1471 thresholdNode1545
def thresholdNode1611 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1608 thresholdNode1610
def thresholdNode1612 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode1609 thresholdNode1611
def thresholdNode1613 : BoxExpr 1 := .mul ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode1612 thresholdNode27
def thresholdNode1614 : BoxExpr 1 := .mul ⟨(-560781019840770369127/4722366482869645213696:ℚ),(-140195254960192592281/2361183241434822606848:ℚ)⟩ thresholdNode1599 thresholdNode1471
def thresholdNode1615 : BoxExpr 1 := .mul ⟨(-560781019840770369127/4722366482869645213696:ℚ),(-140195254960192592281/2361183241434822606848:ℚ)⟩ thresholdNode1471 thresholdNode1599
def thresholdNode1616 : BoxExpr 1 := .add ⟨(-560781019840770369127/2361183241434822606848:ℚ),(-140195254960192592281/1180591620717411303424:ℚ)⟩ thresholdNode1614 thresholdNode1615
def thresholdNode1617 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1616 thresholdNode51
def thresholdNode1618 : BoxExpr 1 := .add ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode1613 thresholdNode1617
def thresholdNode1619 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1475 thresholdNode51
def thresholdNode1620 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1617 thresholdNode1619
def thresholdNode1621 : BoxExpr 1 := .add ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode1618 thresholdNode1620
def thresholdNode1622 : BoxExpr 1 := .add ⟨(-76004436019458814721/73786976294838206464:ℚ),(-4605992210284264973011/4722366482869645213696:ℚ)⟩ thresholdNode1606 thresholdNode1621
def thresholdCell4Out0 : TaylorCertificate1 :=
  { center := (-73/640:ℚ), radius := (19/640:ℚ)
    whole := thresholdNode1477, centerValue := thresholdNode1498, gradient := thresholdNode1536, hessian := thresholdNode1622 }
theorem thresholdCell4Out0_check : thresholdCell4Out0.check = true := by decide +kernel
theorem thresholdCell4Out0_lower_pos : 0 < thresholdCell4Out0.lower := by decide +kernel
theorem thresholdCell4Out0_positive (x : ℝ) (hx : (-(23/160:ℝ)) ≤ x ∧ x ≤ (-(27/320:ℝ))) :
    0 < thresholdNode1477.eval (fun _ => x) := by
  apply thresholdCell4Out0.positive_sound thresholdCell4Out0_check thresholdCell4Out0_lower_pos x
  norm_num [thresholdCell4Out0]
  exact hx
def thresholdNode1623 : BoxExpr 1 := .mul ⟨(29290380081026659068279/4722366482869645213696:ℚ),(30932425446486772918225/4722366482869645213696:ℚ)⟩ thresholdNode1477 thresholdNode1477
def thresholdNode1624 : BoxExpr 1 := .mul ⟨(-678840181912511499469/2361183241434822606848:ℚ),(-398449671992126314905/2361183241434822606848:ℚ)⟩ thresholdNode1464 thresholdNode5
def thresholdNode1625 : BoxExpr 1 := .neg ⟨(398449671992126314905/2361183241434822606848:ℚ),(678840181912511499469/2361183241434822606848:ℚ)⟩ thresholdNode1624
def thresholdNode1626 : BoxExpr 1 := .add ⟨(2759632913426948921753/2361183241434822606848:ℚ),(3040023423347334106317/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode1625
def thresholdNode1627 : BoxExpr 1 := .mul ⟨(821667085271039499638275/4722366482869645213696:ℚ),(905151976287883085163279/4722366482869645213696:ℚ)⟩ thresholdNode1626 thresholdNode180
def thresholdNode1628 : BoxExpr 1 := .mul ⟨(-678840181912511499469/1180591620717411303424:ℚ),(-398449671992126314905/1180591620717411303424:ℚ)⟩ thresholdNode1464 thresholdNode182
def thresholdNode1629 : BoxExpr 1 := .neg ⟨(398449671992126314905/1180591620717411303424:ℚ),(678840181912511499469/1180591620717411303424:ℚ)⟩ thresholdNode1628
def thresholdNode1630 : BoxExpr 1 := .add ⟨(1579041292709537618329/1180591620717411303424:ℚ),(1859431802629922802893/1180591620717411303424:ℚ)⟩ thresholdNode12 thresholdNode1629
def thresholdNode1631 : BoxExpr 1 := .inv ⟨(374790990703940096325/590295810358705651712:ℚ),(3530741295603473056971/4722366482869645213696:ℚ)⟩ thresholdNode1630
def thresholdNode1632 : BoxExpr 1 := .mul ⟨(521693387473675872786095/4722366482869645213696:ℚ),(338374570574909564547215/2361183241434822606848:ℚ)⟩ thresholdNode1627 thresholdNode1631
def thresholdNode1633 : BoxExpr 1 := .add ⟨(526415753956545517999791/4722366482869645213696:ℚ),(340735753816344387154063/2361183241434822606848:ℚ)⟩ thresholdNode1632 thresholdNode12
def thresholdNode1634 : BoxExpr 1 := .sqrt ⟨(24929541274053481766525/2361183241434822606848:ℚ),(56728812843873747594877/4722366482869645213696:ℚ)⟩ thresholdNode1633
def thresholdNode1635 : BoxExpr 1 := .add ⟨(27290724515488304373373/2361183241434822606848:ℚ),(61451179326743392808573/4722366482869645213696:ℚ)⟩ thresholdNode1634 thresholdNode12
def thresholdNode1636 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode1637 : BoxExpr 1 := .mul ⟨(27290724515488304373373/4722366482869645213696:ℚ),(30725589663371696404287/4722366482869645213696:ℚ)⟩ thresholdNode1635 thresholdNode1636
def thresholdNode1638 : BoxExpr 1 := .add ⟨(28471316136205715676797/4722366482869645213696:ℚ),(31906181284089107707711/4722366482869645213696:ℚ)⟩ thresholdNode1637 thresholdNode193
def thresholdNode1639 : BoxExpr 1 := .mul ⟨(3485372885013737781899/590295810358705651712:ℚ),(31679036692720934274911/4722366482869645213696:ℚ)⟩ thresholdNode1467 thresholdNode1638
def thresholdNode1640 : BoxExpr 1 := .neg ⟨(-31679036692720934274911/4722366482869645213696:ℚ),(-3485372885013737781899/590295810358705651712:ℚ)⟩ thresholdNode1639
def thresholdNode1641 : BoxExpr 1 := .add ⟨(-298582076461784400829/590295810358705651712:ℚ),(3049442366376870663033/4722366482869645213696:ℚ)⟩ thresholdNode1623 thresholdNode1640
def thresholdNode1642 : BoxExpr 1 := .mul ⟨(15058155055558515185271/2361183241434822606848:ℚ),(7529077527779257592661/1180591620717411303424:ℚ)⟩ thresholdNode1498 thresholdNode1498
def thresholdNode1643 : BoxExpr 1 := .mul ⟨(-134661231738079726797/590295810358705651712:ℚ),(-538644926952318907187/2361183241434822606848:ℚ)⟩ thresholdNode1485 thresholdNode5
def thresholdNode1644 : BoxExpr 1 := .neg ⟨(538644926952318907187/2361183241434822606848:ℚ),(134661231738079726797/590295810358705651712:ℚ)⟩ thresholdNode1643
def thresholdNode1645 : BoxExpr 1 := .add ⟨(2899828168387141514035/2361183241434822606848:ℚ),(724957042096785378509/590295810358705651712:ℚ)⟩ thresholdNode12 thresholdNode1644
def thresholdNode1646 : BoxExpr 1 := .mul ⟨(107926191347432661550097/590295810358705651712:ℚ),(215852382694865323100269/1180591620717411303424:ℚ)⟩ thresholdNode1645 thresholdNode180
def thresholdNode1647 : BoxExpr 1 := .mul ⟨(-134661231738079726797/295147905179352825856:ℚ),(-538644926952318907187/1180591620717411303424:ℚ)⟩ thresholdNode1485 thresholdNode182
def thresholdNode1648 : BoxExpr 1 := .neg ⟨(538644926952318907187/1180591620717411303424:ℚ),(134661231738079726797/295147905179352825856:ℚ)⟩ thresholdNode1647
def thresholdNode1649 : BoxExpr 1 := .add ⟨(1719236547669730210611/1180591620717411303424:ℚ),(429809136917432552653/295147905179352825856:ℚ)⟩ thresholdNode12 thresholdNode1648
def thresholdNode1650 : BoxExpr 1 := .inv ⟨(3242826769352546069489/4722366482869645213696:ℚ),(810706692338136517373/1180591620717411303424:ℚ)⟩ thresholdNode1649
def thresholdNode1651 : BoxExpr 1 := .mul ⟨(592899248603921917528097/4722366482869645213696:ℚ),(592899248603921917528853/4722366482869645213696:ℚ)⟩ thresholdNode1646 thresholdNode1650
def thresholdNode1652 : BoxExpr 1 := .add ⟨(597621615086791562741793/4722366482869645213696:ℚ),(597621615086791562742549/4722366482869645213696:ℚ)⟩ thresholdNode1651 thresholdNode12
def thresholdNode1653 : BoxExpr 1 := .sqrt ⟨(6640534010581680026137/590295810358705651712:ℚ),(26562136042326720104565/2361183241434822606848:ℚ)⟩ thresholdNode1652
def thresholdNode1654 : BoxExpr 1 := .add ⟨(7230829820940385677849/590295810358705651712:ℚ),(28923319283761542711413/2361183241434822606848:ℚ)⟩ thresholdNode1653 thresholdNode12
def thresholdNode1655 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode1656 : BoxExpr 1 := .mul ⟨(7230829820940385677849/1180591620717411303424:ℚ),(28923319283761542711413/4722366482869645213696:ℚ)⟩ thresholdNode1654 thresholdNode1655
def thresholdNode1657 : BoxExpr 1 := .add ⟨(7525977726119738503705/1180591620717411303424:ℚ),(30103910904478954014837/4722366482869645213696:ℚ)⟩ thresholdNode1656 thresholdNode193
def thresholdNode1658 : BoxExpr 1 := .mul ⟨(29712251380040554732721/4722366482869645213696:ℚ),(1857015711252534670797/295147905179352825856:ℚ)⟩ thresholdNode1488 thresholdNode1657
def thresholdNode1659 : BoxExpr 1 := .neg ⟨(-1857015711252534670797/295147905179352825856:ℚ),(-29712251380040554732721/4722366482869645213696:ℚ)⟩ thresholdNode1658
def thresholdNode1660 : BoxExpr 1 := .add ⟨(202029365538237818895/2361183241434822606848:ℚ),(404058731076475637923/4722366482869645213696:ℚ)⟩ thresholdNode1642 thresholdNode1659
def thresholdNode1661 : BoxExpr 1 := .mul ⟨(644955676150417639705/295147905179352825856:ℚ),(10319290818406682235337/4722366482869645213696:ℚ)⟩ thresholdNode1536 thresholdNode1498
def thresholdNode1662 : BoxExpr 1 := .mul ⟨(644955676150417639705/295147905179352825856:ℚ),(10319290818406682235337/4722366482869645213696:ℚ)⟩ thresholdNode1498 thresholdNode1536
def thresholdNode1663 : BoxExpr 1 := .add ⟨(644955676150417639705/147573952589676412928:ℚ),(10319290818406682235337/2361183241434822606848:ℚ)⟩ thresholdNode1661 thresholdNode1662
def thresholdNode1664 : BoxExpr 1 := .mul ⟨(1716863668771065346157/1180591620717411303424:ℚ),(6867454675084261384645/4722366482869645213696:ℚ)⟩ thresholdNode1517 thresholdNode1657
def thresholdNode1665 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode1666 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1485 thresholdNode51
def thresholdNode1667 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode1665 thresholdNode1666
def thresholdNode1668 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode1667
def thresholdNode1669 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode1668
def thresholdNode1670 : BoxExpr 1 := .mul ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode1669 thresholdNode180
def thresholdNode1671 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1645 thresholdNode51
def thresholdNode1672 : BoxExpr 1 := .add ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode1670 thresholdNode1671
def thresholdNode1673 : BoxExpr 1 := .mul ⟨(-965535672026743071802445/4722366482869645213696:ℚ),(-965535672026743071801549/4722366482869645213696:ℚ)⟩ thresholdNode1672 thresholdNode1650
def thresholdNode1674 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode12 thresholdNode182
def thresholdNode1675 : BoxExpr 1 := .add ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode1674 thresholdNode1666
def thresholdNode1676 : BoxExpr 1 := .neg ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode1675
def thresholdNode1677 : BoxExpr 1 := .add ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode51 thresholdNode1676
def thresholdNode1678 : BoxExpr 1 := .mul ⟨(10014552890176178476807/4722366482869645213696:ℚ),(2503638222544044619205/1180591620717411303424:ℚ)⟩ thresholdNode1649 thresholdNode1649
def thresholdNode1679 : BoxExpr 1 := .inv ⟨(34794278641121738943/73786976294838206464:ℚ),(2226833833031791292355/4722366482869645213696:ℚ)⟩ thresholdNode1678
def thresholdNode1680 : BoxExpr 1 := .mul ⟨(-2226833833031791292355/1180591620717411303424:ℚ),(-34794278641121738943/18446744073709551616:ℚ)⟩ thresholdNode1677 thresholdNode1679
def thresholdNode1681 : BoxExpr 1 := .neg ⟨(34794278641121738943/18446744073709551616:ℚ),(2226833833031791292355/1180591620717411303424:ℚ)⟩ thresholdNode1680
def thresholdNode1682 : BoxExpr 1 := .mul ⟨(101785278730287024468299/295147905179352825856:ℚ),(1628564459684592391495545/4722366482869645213696:ℚ)⟩ thresholdNode1646 thresholdNode1681
def thresholdNode1683 : BoxExpr 1 := .add ⟨(663028787657849319690339/4722366482869645213696:ℚ),(165757196914462329923499/1180591620717411303424:ℚ)⟩ thresholdNode1673 thresholdNode1682
def thresholdNode1684 : BoxExpr 1 := .add ⟨(663028787657849319690339/4722366482869645213696:ℚ),(165757196914462329923499/1180591620717411303424:ℚ)⟩ thresholdNode1683 thresholdNode51
def thresholdNode1685 : BoxExpr 1 := .mul ⟨(6640534010581680026137/295147905179352825856:ℚ),(26562136042326720104565/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode1653
def thresholdNode1686 : BoxExpr 1 := .inv ⟨(209892242504465965567/4722366482869645213696:ℚ),(409945786141535089/9223372036854775808:ℚ)⟩ thresholdNode1685
def thresholdNode1687 : BoxExpr 1 := .mul ⟨(7367312532357563214121/1180591620717411303424:ℚ),(7367312532357563214197/1180591620717411303424:ℚ)⟩ thresholdNode1684 thresholdNode1686
def thresholdNode1688 : BoxExpr 1 := .add ⟨(7367312532357563214121/1180591620717411303424:ℚ),(7367312532357563214197/1180591620717411303424:ℚ)⟩ thresholdNode1687 thresholdNode51
def thresholdNode1689 : BoxExpr 1 := .mul ⟨(7367312532357563214121/2361183241434822606848:ℚ),(7367312532357563214197/2361183241434822606848:ℚ)⟩ thresholdNode1688 thresholdNode1655
def thresholdNode1690 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode1691 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode1690
def thresholdNode1692 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1691
def thresholdNode1693 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1692
def thresholdNode1694 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1654 thresholdNode1693
def thresholdNode1695 : BoxExpr 1 := .add ⟨(7367312532357563214121/2361183241434822606848:ℚ),(7367312532357563214197/2361183241434822606848:ℚ)⟩ thresholdNode1689 thresholdNode1694
def thresholdNode1696 : BoxExpr 1 := .add ⟨(7367312532357563214121/2361183241434822606848:ℚ),(7367312532357563214197/2361183241434822606848:ℚ)⟩ thresholdNode1695 thresholdNode51
def thresholdNode1697 : BoxExpr 1 := .mul ⟨(7271461925704893647791/2361183241434822606848:ℚ),(14542923851409787295739/4722366482869645213696:ℚ)⟩ thresholdNode1488 thresholdNode1696
def thresholdNode1698 : BoxExpr 1 := .add ⟨(10705189263247024340105/2361183241434822606848:ℚ),(334537164476469510631/73786976294838206464:ℚ)⟩ thresholdNode1664 thresholdNode1697
def thresholdNode1699 : BoxExpr 1 := .neg ⟨(-334537164476469510631/73786976294838206464:ℚ),(-10705189263247024340105/2361183241434822606848:ℚ)⟩ thresholdNode1698
def thresholdNode1700 : BoxExpr 1 := .add ⟨(-24118652802521381557/147573952589676412928:ℚ),(-6029663200630345387/36893488147419103232:ℚ)⟩ thresholdNode1663 thresholdNode1699
def thresholdNode1701 : BoxExpr 1 := .mul ⟨(-12449332267856763206819/4722366482869645213696:ℚ),(-11471120948376201530217/4722366482869645213696:ℚ)⟩ thresholdNode1622 thresholdNode1477
def thresholdNode1702 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1565 thresholdNode1468
def thresholdNode1703 : BoxExpr 1 := .mul ⟨(32481770001154404185/147573952589676412928:ℚ),(1783062047565900199629/4722366482869645213696:ℚ)⟩ thresholdNode1463 thresholdNode1573
def thresholdNode1704 : BoxExpr 1 := .add ⟨(32481770001154404185/147573952589676412928:ℚ),(1783062047565900199629/4722366482869645213696:ℚ)⟩ thresholdNode1702 thresholdNode1703
def thresholdNode1705 : BoxExpr 1 := .mul ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode1599 thresholdNode22
def thresholdNode1706 : BoxExpr 1 := .add ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode1705 thresholdNode1602
def thresholdNode1707 : BoxExpr 1 := .neg ⟨(1685884834384463341289/2361183241434822606848:ℚ),(3371769668768926682579/4722366482869645213696:ℚ)⟩ thresholdNode1706
def thresholdNode1708 : BoxExpr 1 := .add ⟨(2205593154402933808249/2361183241434822606848:ℚ),(161088491135463340069/147573952589676412928:ℚ)⟩ thresholdNode1704 thresholdNode1707
def thresholdNode1709 : BoxExpr 1 := .mul ⟨(-463205122388476324899/2361183241434822606848:ℚ),(-14475160074639885153/147573952589676412928:ℚ)⟩ thresholdNode1616 thresholdNode27
def thresholdNode1710 : BoxExpr 1 := .add ⟨(-463205122388476324899/2361183241434822606848:ℚ),(-14475160074639885153/147573952589676412928:ℚ)⟩ thresholdNode1709 thresholdNode1619
def thresholdNode1711 : BoxExpr 1 := .add ⟨(871194016007228741675/1180591620717411303424:ℚ),(36653332765205863729/36893488147419103232:ℚ)⟩ thresholdNode1708 thresholdNode1710
def thresholdNode1712 : BoxExpr 1 := .mul ⟨(2571520922927079508513/4722366482869645213696:ℚ),(4661086804014619613789/4722366482869645213696:ℚ)⟩ thresholdNode1711 thresholdNode1711
def thresholdNode1713 : BoxExpr 1 := .add ⟨(-4938905672464841849153/2361183241434822606848:ℚ),(-1702508536090395479107/1180591620717411303424:ℚ)⟩ thresholdNode1701 thresholdNode1712
def thresholdNode1714 : BoxExpr 1 := .mul ⟨(-12449332267856763206819/4722366482869645213696:ℚ),(-11471120948376201530217/4722366482869645213696:ℚ)⟩ thresholdNode1477 thresholdNode1622
def thresholdNode1715 : BoxExpr 1 := .add ⟨(-4938905672464841849153/2361183241434822606848:ℚ),(-1702508536090395479107/1180591620717411303424:ℚ)⟩ thresholdNode1712 thresholdNode1714
def thresholdNode1716 : BoxExpr 1 := .add ⟨(-4938905672464841849153/1180591620717411303424:ℚ),(-1702508536090395479107/590295810358705651712:ℚ)⟩ thresholdNode1713 thresholdNode1715
def thresholdNode1717 : BoxExpr 1 := .mul ⟨(-31906181284089107707711/2361183241434822606848:ℚ),(-28471316136205715676797/2361183241434822606848:ℚ)⟩ thresholdNode1583 thresholdNode1638
def thresholdNode1718 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode1719 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode1718 thresholdNode1579
def thresholdNode1720 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode1719
def thresholdNode1721 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode1720
def thresholdNode1722 : BoxExpr 1 := .mul ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode1721 thresholdNode180
def thresholdNode1723 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1626 thresholdNode51
def thresholdNode1724 : BoxExpr 1 := .add ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode1722 thresholdNode1723
def thresholdNode1725 : BoxExpr 1 := .mul ⟨(-1051260801786126802476713/4722366482869645213696:ℚ),(-223184336887134063224047/1180591620717411303424:ℚ)⟩ thresholdNode1724 thresholdNode1631
def thresholdNode1726 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode12 thresholdNode182
def thresholdNode1727 : BoxExpr 1 := .add ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode1726 thresholdNode1579
def thresholdNode1728 : BoxExpr 1 := .neg ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode1727
def thresholdNode1729 : BoxExpr 1 := .add ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode51 thresholdNode1728
def thresholdNode1730 : BoxExpr 1 := .mul ⟨(1055983864499503282257/590295810358705651712:ℚ),(2928605089142128414557/1180591620717411303424:ℚ)⟩ thresholdNode1630 thresholdNode1630
def thresholdNode1731 : BoxExpr 1 := .inv ⟨(118981266890139713119/295147905179352825856:ℚ),(2639806576152129388391/4722366482869645213696:ℚ)⟩ thresholdNode1730
def thresholdNode1732 : BoxExpr 1 := .mul ⟨(-2639806576152129388391/1180591620717411303424:ℚ),(-118981266890139713119/73786976294838206464:ℚ)⟩ thresholdNode1729 thresholdNode1731
def thresholdNode1733 : BoxExpr 1 := .neg ⟨(118981266890139713119/73786976294838206464:ℚ),(2639806576152129388391/1180591620717411303424:ℚ)⟩ thresholdNode1732
def thresholdNode1734 : BoxExpr 1 := .mul ⟨(1324935587234732375329237/4722366482869645213696:ℚ),(252990333140119300596189/590295810358705651712:ℚ)⟩ thresholdNode1627 thresholdNode1733
def thresholdNode1735 : BoxExpr 1 := .add ⟨(68418696362151393213131/1180591620717411303424:ℚ),(282796329393104537968331/1180591620717411303424:ℚ)⟩ thresholdNode1725 thresholdNode1734
def thresholdNode1736 : BoxExpr 1 := .add ⟨(68418696362151393213131/1180591620717411303424:ℚ),(282796329393104537968331/1180591620717411303424:ℚ)⟩ thresholdNode1735 thresholdNode51
def thresholdNode1737 : BoxExpr 1 := .mul ⟨(24929541274053481766525/1180591620717411303424:ℚ),(56728812843873747594877/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode1634
def thresholdNode1738 : BoxExpr 1 := .inv ⟨(98277859523984922569/2361183241434822606848:ℚ),(223637741198041077277/4722366482869645213696:ℚ)⟩ thresholdNode1737
def thresholdNode1739 : BoxExpr 1 := .mul ⟨(711935748134448774321/295147905179352825856:ℚ),(1674052949776030123267/147573952589676412928:ℚ)⟩ thresholdNode1736 thresholdNode1738
def thresholdNode1740 : BoxExpr 1 := .add ⟨(711935748134448774321/295147905179352825856:ℚ),(1674052949776030123267/147573952589676412928:ℚ)⟩ thresholdNode1739 thresholdNode51
def thresholdNode1741 : BoxExpr 1 := .mul ⟨(711935748134448774321/590295810358705651712:ℚ),(1674052949776030123267/295147905179352825856:ℚ)⟩ thresholdNode1740 thresholdNode1636
def thresholdNode1742 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode1743 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode1742
def thresholdNode1744 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1743
def thresholdNode1745 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1744
def thresholdNode1746 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1635 thresholdNode1745
def thresholdNode1747 : BoxExpr 1 := .add ⟨(711935748134448774321/590295810358705651712:ℚ),(1674052949776030123267/295147905179352825856:ℚ)⟩ thresholdNode1741 thresholdNode1746
def thresholdNode1748 : BoxExpr 1 := .add ⟨(711935748134448774321/590295810358705651712:ℚ),(1674052949776030123267/295147905179352825856:ℚ)⟩ thresholdNode1747 thresholdNode51
def thresholdNode1749 : BoxExpr 1 := .mul ⟨(961113259981505845331/4722366482869645213696:ℚ),(7700643568969738567031/4722366482869645213696:ℚ)⟩ thresholdNode1570 thresholdNode1748
def thresholdNode1750 : BoxExpr 1 := .add ⟨(-62851249308196709570091/4722366482869645213696:ℚ),(-49241988703441692786563/4722366482869645213696:ℚ)⟩ thresholdNode1717 thresholdNode1749
def thresholdNode1751 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode5
def thresholdNode1752 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode12 thresholdNode51
def thresholdNode1753 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1751 thresholdNode1752
def thresholdNode1754 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1752 thresholdNode1579
def thresholdNode1755 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1753 thresholdNode1754
def thresholdNode1756 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1755
def thresholdNode1757 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1756
def thresholdNode1758 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1757 thresholdNode180
def thresholdNode1759 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1721 thresholdNode51
def thresholdNode1760 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1758 thresholdNode1759
def thresholdNode1761 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1759 thresholdNode1723
def thresholdNode1762 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1760 thresholdNode1761
def thresholdNode1763 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1762 thresholdNode1631
def thresholdNode1764 : BoxExpr 1 := .mul ⟨(-785989384512992001852185/1180591620717411303424:ℚ),(-2267269454091520642275125/4722366482869645213696:ℚ)⟩ thresholdNode1724 thresholdNode1733
def thresholdNode1765 : BoxExpr 1 := .add ⟨(-785989384512992001852185/1180591620717411303424:ℚ),(-2267269454091520642275125/4722366482869645213696:ℚ)⟩ thresholdNode1763 thresholdNode1764
def thresholdNode1766 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode182
def thresholdNode1767 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1766 thresholdNode1752
def thresholdNode1768 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1767 thresholdNode1754
def thresholdNode1769 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1768
def thresholdNode1770 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1769
def thresholdNode1771 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1770 thresholdNode1731
def thresholdNode1772 : BoxExpr 1 := .mul ⟨(-1859431802629922802893/295147905179352825856:ℚ),(-1579041292709537618329/295147905179352825856:ℚ)⟩ thresholdNode1729 thresholdNode1630
def thresholdNode1773 : BoxExpr 1 := .mul ⟨(-1859431802629922802893/295147905179352825856:ℚ),(-1579041292709537618329/295147905179352825856:ℚ)⟩ thresholdNode1630 thresholdNode1729
def thresholdNode1774 : BoxExpr 1 := .add ⟨(-1859431802629922802893/147573952589676412928:ℚ),(-1579041292709537618329/147573952589676412928:ℚ)⟩ thresholdNode1772 thresholdNode1773
def thresholdNode1775 : BoxExpr 1 := .mul ⟨(15112449080818516348187/4722366482869645213696:ℚ),(29059083997012769193451/4722366482869645213696:ℚ)⟩ thresholdNode1730 thresholdNode1730
def thresholdNode1776 : BoxExpr 1 := .inv ⟨(767427672559228182375/4722366482869645213696:ℚ),(1475653951207409213531/4722366482869645213696:ℚ)⟩ thresholdNode1775
def thresholdNode1777 : BoxExpr 1 := .mul ⟨(-18593239785213356090493/4722366482869645213696:ℚ),(-8211476096383741551409/4722366482869645213696:ℚ)⟩ thresholdNode1774 thresholdNode1776
def thresholdNode1778 : BoxExpr 1 := .neg ⟨(8211476096383741551409/4722366482869645213696:ℚ),(18593239785213356090493/4722366482869645213696:ℚ)⟩ thresholdNode1777
def thresholdNode1779 : BoxExpr 1 := .mul ⟨(-18593239785213356090493/1180591620717411303424:ℚ),(-8211476096383741551409/1180591620717411303424:ℚ)⟩ thresholdNode1729 thresholdNode1778
def thresholdNode1780 : BoxExpr 1 := .add ⟨(-18593239785213356090493/1180591620717411303424:ℚ),(-8211476096383741551409/1180591620717411303424:ℚ)⟩ thresholdNode1771 thresholdNode1779
def thresholdNode1781 : BoxExpr 1 := .neg ⟨(8211476096383741551409/1180591620717411303424:ℚ),(18593239785213356090493/1180591620717411303424:ℚ)⟩ thresholdNode1780
def thresholdNode1782 : BoxExpr 1 := .mul ⟨(2857507842461403157675319/2361183241434822606848:ℚ),(14255316946052385640734551/4722366482869645213696:ℚ)⟩ thresholdNode1627 thresholdNode1781
def thresholdNode1783 : BoxExpr 1 := .add ⟨(1285529073435419153970949/2361183241434822606848:ℚ),(5994023745980432499229713/2361183241434822606848:ℚ)⟩ thresholdNode1764 thresholdNode1782
def thresholdNode1784 : BoxExpr 1 := .add ⟨(-286449695590564849733421/2361183241434822606848:ℚ),(9720778037869344356184301/4722366482869645213696:ℚ)⟩ thresholdNode1765 thresholdNode1783
def thresholdNode1785 : BoxExpr 1 := .add ⟨(-286449695590564849733421/2361183241434822606848:ℚ),(9720778037869344356184301/4722366482869645213696:ℚ)⟩ thresholdNode1784 thresholdNode51
def thresholdNode1786 : BoxExpr 1 := .mul ⟨(-27130873099799065210075/4722366482869645213696:ℚ),(460348185801028727347067/4722366482869645213696:ℚ)⟩ thresholdNode1785 thresholdNode1738
def thresholdNode1787 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1634
def thresholdNode1788 : BoxExpr 1 := .mul ⟨(711935748134448774321/147573952589676412928:ℚ),(1674052949776030123267/73786976294838206464:ℚ)⟩ thresholdNode5 thresholdNode1739
def thresholdNode1789 : BoxExpr 1 := .add ⟨(711935748134448774321/147573952589676412928:ℚ),(1674052949776030123267/73786976294838206464:ℚ)⟩ thresholdNode1787 thresholdNode1788
def thresholdNode1790 : BoxExpr 1 := .mul ⟨(2105663015826182071999097/4722366482869645213696:ℚ),(1362943015265377548616269/2361183241434822606848:ℚ)⟩ thresholdNode1737 thresholdNode1737
def thresholdNode1791 : BoxExpr 1 := .inv ⟨(2045274907750679401/1180591620717411303424:ℚ),(1323855302992336775/590295810358705651712:ℚ)⟩ thresholdNode1790
def thresholdNode1792 : BoxExpr 1 := .mul ⟨(39467786720837832313/4722366482869645213696:ℚ),(120140652800052293663/2361183241434822606848:ℚ)⟩ thresholdNode1789 thresholdNode1791
def thresholdNode1793 : BoxExpr 1 := .neg ⟨(-120140652800052293663/2361183241434822606848:ℚ),(-39467786720837832313/4722366482869645213696:ℚ)⟩ thresholdNode1792
def thresholdNode1794 : BoxExpr 1 := .mul ⟨(-57556457332977459095035/4722366482869645213696:ℚ),(-1143636151719524935225/2361183241434822606848:ℚ)⟩ thresholdNode1736 thresholdNode1793
def thresholdNode1795 : BoxExpr 1 := .add ⟨(-42343665216388262152555/2361183241434822606848:ℚ),(458060913497589677476617/4722366482869645213696:ℚ)⟩ thresholdNode1786 thresholdNode1794
def thresholdNode1796 : BoxExpr 1 := .add ⟨(-42343665216388262152555/2361183241434822606848:ℚ),(458060913497589677476617/4722366482869645213696:ℚ)⟩ thresholdNode1795 thresholdNode51
def thresholdNode1797 : BoxExpr 1 := .mul ⟨(-42343665216388262152555/4722366482869645213696:ℚ),(229030456748794838738309/4722366482869645213696:ℚ)⟩ thresholdNode1796 thresholdNode1636
def thresholdNode1798 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1740 thresholdNode1745
def thresholdNode1799 : BoxExpr 1 := .add ⟨(-42343665216388262152555/4722366482869645213696:ℚ),(229030456748794838738309/4722366482869645213696:ℚ)⟩ thresholdNode1797 thresholdNode1798
def thresholdNode1800 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode5 thresholdNode51
def thresholdNode1801 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1751 thresholdNode1800
def thresholdNode1802 : BoxExpr 1 := .mul ⟨(16/1:ℚ),(16/1:ℚ)⟩ thresholdNode1742 thresholdNode1742
def thresholdNode1803 : BoxExpr 1 := .inv ⟨(1/16:ℚ),(1/16:ℚ)⟩ thresholdNode1802
def thresholdNode1804 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1801 thresholdNode1803
def thresholdNode1805 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1804
def thresholdNode1806 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1805
def thresholdNode1807 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1744 thresholdNode1806
def thresholdNode1808 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1807
def thresholdNode1809 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1635 thresholdNode1808
def thresholdNode1810 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1798 thresholdNode1809
def thresholdNode1811 : BoxExpr 1 := .add ⟨(-42343665216388262152555/4722366482869645213696:ℚ),(229030456748794838738309/4722366482869645213696:ℚ)⟩ thresholdNode1799 thresholdNode1810
def thresholdNode1812 : BoxExpr 1 := .add ⟨(-42343665216388262152555/4722366482869645213696:ℚ),(229030456748794838738309/4722366482869645213696:ℚ)⟩ thresholdNode1811 thresholdNode51
def thresholdNode1813 : BoxExpr 1 := .mul ⟨(-21021107354567436529847/2361183241434822606848:ℚ),(227399956719792187982065/4722366482869645213696:ℚ)⟩ thresholdNode1467 thresholdNode1812
def thresholdNode1814 : BoxExpr 1 := .add ⟨(-41081101449153367214363/4722366482869645213696:ℚ),(29387575036095240818637/590295810358705651712:ℚ)⟩ thresholdNode1749 thresholdNode1813
def thresholdNode1815 : BoxExpr 1 := .add ⟨(-51966175378675038392227/2361183241434822606848:ℚ),(185858611585320233762533/4722366482869645213696:ℚ)⟩ thresholdNode1750 thresholdNode1814
def thresholdNode1816 : BoxExpr 1 := .neg ⟨(-185858611585320233762533/4722366482869645213696:ℚ),(51966175378675038392227/2361183241434822606848:ℚ)⟩ thresholdNode1815
def thresholdNode1817 : BoxExpr 1 := .add ⟨(-205614234275179601159145/4722366482869645213696:ℚ),(45156141234313456475799/2361183241434822606848:ℚ)⟩ thresholdNode1716 thresholdNode1816
def thresholdCell4Out1 : TaylorCertificate1 :=
  { center := (-73/640:ℚ), radius := (19/640:ℚ)
    whole := thresholdNode1641, centerValue := thresholdNode1660, gradient := thresholdNode1700, hessian := thresholdNode1817 }
theorem thresholdCell4Out1_check : thresholdCell4Out1.check = true := by decide +kernel
theorem thresholdCell4Out1_lower_pos : 0 < thresholdCell4Out1.lower := by decide +kernel
theorem thresholdCell4Out1_positive (x : ℝ) (hx : (-(23/160:ℝ)) ≤ x ∧ x ≤ (-(27/320:ℝ))) :
    0 < thresholdNode1641.eval (fun _ => x) := by
  apply thresholdCell4Out1.positive_sound thresholdCell4Out1_check thresholdCell4Out1_lower_pos x
  norm_num [thresholdCell4Out1]
  exact hx
theorem thresholdCell4_public (x : ℝ)
    (hx : (-(23/160:ℝ)) ≤ x ∧ x ≤ (-(27/320:ℝ))) : qc x < fA (43/20) x := by
  have hf := thresholdCell4Out0_positive x hx
  have hg := thresholdCell4Out1_positive x hx
  have hfa : thresholdNode1477.eval (fun _ => x) = thresholdFA 0 x := by
    norm_num [thresholdNode0, thresholdNode1, thresholdNode1457, thresholdNode3, thresholdNode1458, thresholdNode5, thresholdNode1459, thresholdNode1460, thresholdNode1461, thresholdNode9, thresholdNode1462, thresholdNode1463, thresholdNode12, thresholdNode1464, thresholdNode1465, thresholdNode1466, thresholdNode1467, thresholdNode1468, thresholdNode1469, thresholdNode19, thresholdNode1470, thresholdNode1471, thresholdNode22, thresholdNode1472, thresholdNode1473, thresholdNode1474, thresholdNode1475, thresholdNode27, thresholdNode1476, thresholdNode1477, BoxExpr.eval, thresholdFA, ftilde, pow_two, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  have hgap : thresholdNode1641.eval (fun _ => x) =
      (thresholdNode1477.eval (fun _ => x))^2 - (1-x^2)*(thresholdCapacity 1 x+1/4) := by
    norm_num [thresholdNode1623, thresholdNode12, thresholdNode1464, thresholdNode1465, thresholdNode1466, thresholdNode1467, thresholdNode5, thresholdNode1624, thresholdNode1625, thresholdNode1626, thresholdNode180, thresholdNode1627, thresholdNode182, thresholdNode1628, thresholdNode1629, thresholdNode1630, thresholdNode1631, thresholdNode1632, thresholdNode1633, thresholdNode1634, thresholdNode1635, thresholdNode1636, thresholdNode1637, thresholdNode193, thresholdNode1638, thresholdNode1639, thresholdNode1640, thresholdNode1641, BoxExpr.eval, thresholdCapacity, Da, D5, beta5, eta5, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  rw [hfa] at hf
  rw [hgap, hfa] at hg
  refine threshold_positive_to_public 0 1 x ?_ ?_ ?_ hf hg
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdFADomain] <;> constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdCapacityDomain] <;> linarith [hx.1,hx.2]
def thresholdNode1818 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode1819 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode1818 thresholdNode3
def thresholdNode1820 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode1821 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1820
def thresholdNode1822 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode1821 thresholdNode1821
def thresholdNode1823 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode1822 thresholdNode9
def thresholdNode1824 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode1819 thresholdNode1823
def thresholdNode1825 : BoxExpr 1 := .var 0
def thresholdNode1826 : BoxExpr 1 := .mul ⟨(49/16384:ℚ),(33619191074335657821/4722366482869645213696:ℚ)⟩ thresholdNode1825 thresholdNode1825
def thresholdNode1827 : BoxExpr 1 := .neg ⟨(-33619191074335657821/4722366482869645213696:ℚ),(-49/16384:ℚ)⟩ thresholdNode1826
def thresholdNode1828 : BoxExpr 1 := .add ⟨(4688747291795309555875/4722366482869645213696:ℚ),(16335/16384:ℚ)⟩ thresholdNode12 thresholdNode1827
def thresholdNode1829 : BoxExpr 1 := .sqrt ⟨(4705526862894312506765/4722366482869645213696:ℚ),(2357649775444506049563/2361183241434822606848:ℚ)⟩ thresholdNode1828
def thresholdNode1830 : BoxExpr 1 := .mul ⟨(6115655625532165607227/2361183241434822606848:ℚ),(3064178471900838399967/1180591620717411303424:ℚ)⟩ thresholdNode1824 thresholdNode1829
def thresholdNode1831 : BoxExpr 1 := .neg ⟨(7/128:ℚ),(199224835996063157453/2361183241434822606848:ℚ)⟩ thresholdNode1825
def thresholdNode1832 : BoxExpr 1 := .add ⟨(140195254960192592281/4722366482869645213696:ℚ),(70097627480096296141/1180591620717411303424:ℚ)⟩ thresholdNode19 thresholdNode1831
def thresholdNode1833 : BoxExpr 1 := .mul ⟨(12512426505197188861/590295810358705651712:ℚ),(200198824083155021779/4722366482869645213696:ℚ)⟩ thresholdNode1832 thresholdNode22
def thresholdNode1834 : BoxExpr 1 := .neg ⟨(-200198824083155021779/4722366482869645213696:ℚ),(-12512426505197188861/590295810358705651712:ℚ)⟩ thresholdNode1833
def thresholdNode1835 : BoxExpr 1 := .add ⟨(12031112426981176192675/4722366482869645213696:ℚ),(3039153618890444022245/1180591620717411303424:ℚ)⟩ thresholdNode1830 thresholdNode1834
def thresholdNode1836 : BoxExpr 1 := .mul ⟨(4162046631630717583/4722366482869645213696:ℚ),(8324093263261435167/2361183241434822606848:ℚ)⟩ thresholdNode1832 thresholdNode1832
def thresholdNode1837 : BoxExpr 1 := .mul ⟨(3437850517726972723/4722366482869645213696:ℚ),(859462629431743181/295147905179352825856:ℚ)⟩ thresholdNode1836 thresholdNode27
def thresholdNode1838 : BoxExpr 1 := .add ⟨(6017275138749451582699/2361183241434822606848:ℚ),(3042591469408170994969/1180591620717411303424:ℚ)⟩ thresholdNode1835 thresholdNode1837
def thresholdNode1839 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode1840 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode1839 thresholdNode3
def thresholdNode1841 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode1842 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1841
def thresholdNode1843 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode1842 thresholdNode1842
def thresholdNode1844 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode1843 thresholdNode9
def thresholdNode1845 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode1840 thresholdNode1844
def thresholdNode1846 : BoxExpr 1 := .var 0
def thresholdNode1847 : BoxExpr 1 := .mul ⟨(11415364047488543621/2361183241434822606848:ℚ),(22830728094977087243/4722366482869645213696:ℚ)⟩ thresholdNode1846 thresholdNode1846
def thresholdNode1848 : BoxExpr 1 := .neg ⟨(-22830728094977087243/4722366482869645213696:ℚ),(-11415364047488543621/2361183241434822606848:ℚ)⟩ thresholdNode1847
def thresholdNode1849 : BoxExpr 1 := .add ⟨(4699535754774668126453/4722366482869645213696:ℚ),(2349767877387334063227/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode1848
def thresholdNode1850 : BoxExpr 1 := .sqrt ⟨(2355468644102240697389/2361183241434822606848:ℚ),(4710937288204481394779/4722366482869645213696:ℚ)⟩ thresholdNode1849
def thresholdNode1851 : BoxExpr 1 := .mul ⟨(12245374840094318713511/4722366482869645213696:ℚ),(3061343710023579678381/1180591620717411303424:ℚ)⟩ thresholdNode1845 thresholdNode1850
def thresholdNode1852 : BoxExpr 1 := .neg ⟨(82088011128007504691/1180591620717411303424:ℚ),(328352044512030018765/4722366482869645213696:ℚ)⟩ thresholdNode1846
def thresholdNode1853 : BoxExpr 1 := .add ⟨(210292882440288888421/4722366482869645213696:ℚ),(210292882440288888423/4722366482869645213696:ℚ)⟩ thresholdNode19 thresholdNode1852
def thresholdNode1854 : BoxExpr 1 := .mul ⟨(37537279515591566583/1180591620717411303424:ℚ),(150149118062366266335/4722366482869645213696:ℚ)⟩ thresholdNode1853 thresholdNode22
def thresholdNode1855 : BoxExpr 1 := .neg ⟨(-150149118062366266335/4722366482869645213696:ℚ),(-37537279515591566583/1180591620717411303424:ℚ)⟩ thresholdNode1854
def thresholdNode1856 : BoxExpr 1 := .add ⟨(1511903215253994055897/590295810358705651712:ℚ),(1511903215253994055899/590295810358705651712:ℚ)⟩ thresholdNode1851 thresholdNode1855
def thresholdNode1857 : BoxExpr 1 := .mul ⟨(4682302460584557281/2361183241434822606848:ℚ),(9364604921169114563/4722366482869645213696:ℚ)⟩ thresholdNode1853 thresholdNode1853
def thresholdNode1858 : BoxExpr 1 := .mul ⟨(1933790916221422157/1180591620717411303424:ℚ),(3867581832442844315/2361183241434822606848:ℚ)⟩ thresholdNode1857 thresholdNode27
def thresholdNode1859 : BoxExpr 1 := .add ⟨(3025740221424209533951/1180591620717411303424:ℚ),(6051480442848419067911/2361183241434822606848:ℚ)⟩ thresholdNode1856 thresholdNode1858
def thresholdNode1860 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1
def thresholdNode1861 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode51
def thresholdNode1862 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1860 thresholdNode1861
def thresholdNode1863 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1862 thresholdNode51
def thresholdNode1864 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51
def thresholdNode1865 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1864
def thresholdNode1866 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1865 thresholdNode1842
def thresholdNode1867 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1842 thresholdNode1865
def thresholdNode1868 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1866 thresholdNode1867
def thresholdNode1869 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1868 thresholdNode9
def thresholdNode1870 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1843 thresholdNode51
def thresholdNode1871 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1869 thresholdNode1870
def thresholdNode1872 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1863 thresholdNode1871
def thresholdNode1873 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1872 thresholdNode1850
def thresholdNode1874 : BoxExpr 1 := .mul ⟨(-328352044512030018765/4722366482869645213696:ℚ),(-82088011128007504691/1180591620717411303424:ℚ)⟩ thresholdNode12 thresholdNode1846
def thresholdNode1875 : BoxExpr 1 := .mul ⟨(-328352044512030018765/4722366482869645213696:ℚ),(-82088011128007504691/1180591620717411303424:ℚ)⟩ thresholdNode1846 thresholdNode12
def thresholdNode1876 : BoxExpr 1 := .add ⟨(-328352044512030018765/2361183241434822606848:ℚ),(-82088011128007504691/590295810358705651712:ℚ)⟩ thresholdNode1874 thresholdNode1875
def thresholdNode1877 : BoxExpr 1 := .neg ⟨(82088011128007504691/590295810358705651712:ℚ),(328352044512030018765/2361183241434822606848:ℚ)⟩ thresholdNode1876
def thresholdNode1878 : BoxExpr 1 := .add ⟨(82088011128007504691/590295810358705651712:ℚ),(328352044512030018765/2361183241434822606848:ℚ)⟩ thresholdNode51 thresholdNode1877
def thresholdNode1879 : BoxExpr 1 := .mul ⟨(2355468644102240697389/1180591620717411303424:ℚ),(4710937288204481394779/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode1850
def thresholdNode1880 : BoxExpr 1 := .inv ⟨(2366911702939511124401/4722366482869645213696:ℚ),(1183455851469755562201/2361183241434822606848:ℚ)⟩ thresholdNode1879
def thresholdNode1881 : BoxExpr 1 := .mul ⟨(41143582336253220717/590295810358705651712:ℚ),(164574329345012882869/2361183241434822606848:ℚ)⟩ thresholdNode1878 thresholdNode1880
def thresholdNode1882 : BoxExpr 1 := .mul ⟨(855572565965918474165/4722366482869645213696:ℚ),(213893141491479618543/1180591620717411303424:ℚ)⟩ thresholdNode1845 thresholdNode1881
def thresholdNode1883 : BoxExpr 1 := .add ⟨(855572565965918474165/4722366482869645213696:ℚ),(213893141491479618543/1180591620717411303424:ℚ)⟩ thresholdNode1873 thresholdNode1882
def thresholdNode1884 : BoxExpr 1 := .neg ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode12
def thresholdNode1885 : BoxExpr 1 := .add ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode51 thresholdNode1884
def thresholdNode1886 : BoxExpr 1 := .mul ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode1885 thresholdNode22
def thresholdNode1887 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1853 thresholdNode51
def thresholdNode1888 : BoxExpr 1 := .add ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode1886 thresholdNode1887
def thresholdNode1889 : BoxExpr 1 := .neg ⟨(1685884834384463341289/2361183241434822606848:ℚ),(3371769668768926682579/4722366482869645213696:ℚ)⟩ thresholdNode1888
def thresholdNode1890 : BoxExpr 1 := .add ⟨(4227342234734845156743/4722366482869645213696:ℚ),(4227342234734845156751/4722366482869645213696:ℚ)⟩ thresholdNode1883 thresholdNode1889
def thresholdNode1891 : BoxExpr 1 := .mul ⟨(-210292882440288888423/4722366482869645213696:ℚ),(-210292882440288888421/4722366482869645213696:ℚ)⟩ thresholdNode1885 thresholdNode1853
def thresholdNode1892 : BoxExpr 1 := .mul ⟨(-210292882440288888423/4722366482869645213696:ℚ),(-210292882440288888421/4722366482869645213696:ℚ)⟩ thresholdNode1853 thresholdNode1885
def thresholdNode1893 : BoxExpr 1 := .add ⟨(-210292882440288888423/2361183241434822606848:ℚ),(-210292882440288888421/2361183241434822606848:ℚ)⟩ thresholdNode1891 thresholdNode1892
def thresholdNode1894 : BoxExpr 1 := .mul ⟨(-347403841791357243675/4722366482869645213696:ℚ),(-347403841791357243671/4722366482869645213696:ℚ)⟩ thresholdNode1893 thresholdNode27
def thresholdNode1895 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1857 thresholdNode51
def thresholdNode1896 : BoxExpr 1 := .add ⟨(-347403841791357243675/4722366482869645213696:ℚ),(-347403841791357243671/4722366482869645213696:ℚ)⟩ thresholdNode1894 thresholdNode1895
def thresholdNode1897 : BoxExpr 1 := .add ⟨(969984598235871978267/1180591620717411303424:ℚ),(484992299117935989135/590295810358705651712:ℚ)⟩ thresholdNode1890 thresholdNode1896
def thresholdNode1898 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1
def thresholdNode1899 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode51
def thresholdNode1900 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1898 thresholdNode1899
def thresholdNode1901 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode51
def thresholdNode1902 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1899 thresholdNode1901
def thresholdNode1903 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1900 thresholdNode1902
def thresholdNode1904 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1903 thresholdNode51
def thresholdNode1905 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51
def thresholdNode1906 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1905
def thresholdNode1907 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1906 thresholdNode1821
def thresholdNode1908 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1906 thresholdNode1906
def thresholdNode1909 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1907 thresholdNode1908
def thresholdNode1910 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1821 thresholdNode1906
def thresholdNode1911 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1908 thresholdNode1910
def thresholdNode1912 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1909 thresholdNode1911
def thresholdNode1913 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1912 thresholdNode9
def thresholdNode1914 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1907 thresholdNode1910
def thresholdNode1915 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1914 thresholdNode51
def thresholdNode1916 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1913 thresholdNode1915
def thresholdNode1917 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1822 thresholdNode51
def thresholdNode1918 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1915 thresholdNode1917
def thresholdNode1919 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1916 thresholdNode1918
def thresholdNode1920 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1904 thresholdNode1919
def thresholdNode1921 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1920 thresholdNode1829
def thresholdNode1922 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1898 thresholdNode1901
def thresholdNode1923 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1922 thresholdNode51
def thresholdNode1924 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1914 thresholdNode9
def thresholdNode1925 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1924 thresholdNode1917
def thresholdNode1926 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1923 thresholdNode1925
def thresholdNode1927 : BoxExpr 1 := .mul ⟨(-199224835996063157453/2361183241434822606848:ℚ),(-7/128:ℚ)⟩ thresholdNode12 thresholdNode1825
def thresholdNode1928 : BoxExpr 1 := .mul ⟨(-199224835996063157453/2361183241434822606848:ℚ),(-7/128:ℚ)⟩ thresholdNode1825 thresholdNode12
def thresholdNode1929 : BoxExpr 1 := .add ⟨(-199224835996063157453/1180591620717411303424:ℚ),(-7/64:ℚ)⟩ thresholdNode1927 thresholdNode1928
def thresholdNode1930 : BoxExpr 1 := .neg ⟨(7/64:ℚ),(199224835996063157453/1180591620717411303424:ℚ)⟩ thresholdNode1929
def thresholdNode1931 : BoxExpr 1 := .add ⟨(7/64:ℚ),(199224835996063157453/1180591620717411303424:ℚ)⟩ thresholdNode51 thresholdNode1930
def thresholdNode1932 : BoxExpr 1 := .mul ⟨(4705526862894312506765/2361183241434822606848:ℚ),(2357649775444506049563/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode1829
def thresholdNode1933 : BoxExpr 1 := .inv ⟨(295590250389369353505/590295810358705651712:ℚ),(592408295827199497267/1180591620717411303424:ℚ)⟩ thresholdNode1932
def thresholdNode1934 : BoxExpr 1 := .mul ⟨(64660367272674546079/1180591620717411303424:ℚ),(24992224980209978791/295147905179352825856:ℚ)⟩ thresholdNode1931 thresholdNode1933
def thresholdNode1935 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1926 thresholdNode1934
def thresholdNode1936 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1921 thresholdNode1935
def thresholdNode1937 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1825
def thresholdNode1938 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode12
def thresholdNode1939 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1937 thresholdNode1938
def thresholdNode1940 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1825 thresholdNode51
def thresholdNode1941 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1938 thresholdNode1940
def thresholdNode1942 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode1939 thresholdNode1941
def thresholdNode1943 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode1942
def thresholdNode1944 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode1943
def thresholdNode1945 : BoxExpr 1 := .mul ⟨(-592408295827199497267/590295810358705651712:ℚ),(-295590250389369353505/295147905179352825856:ℚ)⟩ thresholdNode1944 thresholdNode1933
def thresholdNode1946 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1829
def thresholdNode1947 : BoxExpr 1 := .mul ⟨(64660367272674546079/590295810358705651712:ℚ),(24992224980209978791/147573952589676412928:ℚ)⟩ thresholdNode5 thresholdNode1934
def thresholdNode1948 : BoxExpr 1 := .add ⟨(64660367272674546079/590295810358705651712:ℚ),(24992224980209978791/147573952589676412928:ℚ)⟩ thresholdNode1946 thresholdNode1947
def thresholdNode1949 : BoxExpr 1 := .mul ⟨(18754989167181238223493/4722366482869645213696:ℚ),(18832972777752845352961/4722366482869645213696:ℚ)⟩ thresholdNode1932 thresholdNode1932
def thresholdNode1950 : BoxExpr 1 := .inv ⟨(296033258552709929527/1180591620717411303424:ℚ),(1189056682450875052579/4722366482869645213696:ℚ)⟩ thresholdNode1949
def thresholdNode1951 : BoxExpr 1 := .mul ⟨(129708657165044354203/4722366482869645213696:ℚ),(100685695546360390995/2361183241434822606848:ℚ)⟩ thresholdNode1948 thresholdNode1950
def thresholdNode1952 : BoxExpr 1 := .neg ⟨(-100685695546360390995/2361183241434822606848:ℚ),(-129708657165044354203/4722366482869645213696:ℚ)⟩ thresholdNode1951
def thresholdNode1953 : BoxExpr 1 := .mul ⟨(-33981422246896631961/4722366482869645213696:ℚ),(-443340136794585195/147573952589676412928:ℚ)⟩ thresholdNode1931 thresholdNode1952
def thresholdNode1954 : BoxExpr 1 := .add ⟨(-4773247788864492610097/4722366482869645213696:ℚ),(-296476930662958523895/295147905179352825856:ℚ)⟩ thresholdNode1945 thresholdNode1953
def thresholdNode1955 : BoxExpr 1 := .mul ⟨(-3101835409996229716515/1180591620717411303424:ℚ),(-6165178477750089912689/2361183241434822606848:ℚ)⟩ thresholdNode1824 thresholdNode1954
def thresholdNode1956 : BoxExpr 1 := .add ⟨(-3101835409996229716515/1180591620717411303424:ℚ),(-6165178477750089912689/2361183241434822606848:ℚ)⟩ thresholdNode1935 thresholdNode1955
def thresholdNode1957 : BoxExpr 1 := .add ⟨(-3101835409996229716515/1180591620717411303424:ℚ),(-6165178477750089912689/2361183241434822606848:ℚ)⟩ thresholdNode1936 thresholdNode1956
def thresholdNode1958 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1906 thresholdNode22
def thresholdNode1959 : BoxExpr 1 := .neg ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode12
def thresholdNode1960 : BoxExpr 1 := .add ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode51 thresholdNode1959
def thresholdNode1961 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1960 thresholdNode51
def thresholdNode1962 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1958 thresholdNode1961
def thresholdNode1963 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1832 thresholdNode51
def thresholdNode1964 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1961 thresholdNode1963
def thresholdNode1965 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1962 thresholdNode1964
def thresholdNode1966 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1965
def thresholdNode1967 : BoxExpr 1 := .add ⟨(-3101835409996229716515/1180591620717411303424:ℚ),(-6165178477750089912689/2361183241434822606848:ℚ)⟩ thresholdNode1957 thresholdNode1966
def thresholdNode1968 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1906 thresholdNode1832
def thresholdNode1969 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1960 thresholdNode1960
def thresholdNode1970 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1968 thresholdNode1969
def thresholdNode1971 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1832 thresholdNode1906
def thresholdNode1972 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode1969 thresholdNode1971
def thresholdNode1973 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode1970 thresholdNode1972
def thresholdNode1974 : BoxExpr 1 := .mul ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode1973 thresholdNode27
def thresholdNode1975 : BoxExpr 1 := .mul ⟨(-70097627480096296141/1180591620717411303424:ℚ),(-140195254960192592281/4722366482869645213696:ℚ)⟩ thresholdNode1960 thresholdNode1832
def thresholdNode1976 : BoxExpr 1 := .mul ⟨(-70097627480096296141/1180591620717411303424:ℚ),(-140195254960192592281/4722366482869645213696:ℚ)⟩ thresholdNode1832 thresholdNode1960
def thresholdNode1977 : BoxExpr 1 := .add ⟨(-70097627480096296141/590295810358705651712:ℚ),(-140195254960192592281/2361183241434822606848:ℚ)⟩ thresholdNode1975 thresholdNode1976
def thresholdNode1978 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1977 thresholdNode51
def thresholdNode1979 : BoxExpr 1 := .add ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode1974 thresholdNode1978
def thresholdNode1980 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1836 thresholdNode51
def thresholdNode1981 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1978 thresholdNode1980
def thresholdNode1982 : BoxExpr 1 := .add ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode1979 thresholdNode1981
def thresholdNode1983 : BoxExpr 1 := .add ⟨(-1151498052571066243259/1180591620717411303424:ℚ),(-70765742590617592693/73786976294838206464:ℚ)⟩ thresholdNode1967 thresholdNode1982
def thresholdCell5Out0 : TaylorCertificate1 :=
  { center := (-89/1280:ℚ), radius := (19/1280:ℚ)
    whole := thresholdNode1838, centerValue := thresholdNode1859, gradient := thresholdNode1897, hessian := thresholdNode1983 }
theorem thresholdCell5Out0_check : thresholdCell5Out0.check = true := by decide +kernel
theorem thresholdCell5Out0_lower_pos : 0 < thresholdCell5Out0.lower := by decide +kernel
theorem thresholdCell5Out0_positive (x : ℝ) (hx : (-(27/320:ℝ)) ≤ x ∧ x ≤ (-(7/128:ℝ))) :
    0 < thresholdNode1838.eval (fun _ => x) := by
  apply thresholdCell5Out0.positive_sound thresholdCell5Out0_check thresholdCell5Out0_lower_pos x
  norm_num [thresholdCell5Out0]
  exact hx
def thresholdNode1984 : BoxExpr 1 := .mul ⟨(15334515110911054429555/2361183241434822606848:ℚ),(7841291338396881129761/1180591620717411303424:ℚ)⟩ thresholdNode1838 thresholdNode1838
def thresholdNode1985 : BoxExpr 1 := .mul ⟨(-199224835996063157453/1180591620717411303424:ℚ),(-7/64:ℚ)⟩ thresholdNode1825 thresholdNode5
def thresholdNode1986 : BoxExpr 1 := .neg ⟨(7/64:ℚ),(199224835996063157453/1180591620717411303424:ℚ)⟩ thresholdNode1985
def thresholdNode1987 : BoxExpr 1 := .add ⟨(71/64:ℚ),(1379816456713474460877/1180591620717411303424:ℚ)⟩ thresholdNode12 thresholdNode1986
def thresholdNode1988 : BoxExpr 1 := .mul ⟨(779924639762617706876073/4722366482869645213696:ℚ),(821667085271039499638575/4722366482869645213696:ℚ)⟩ thresholdNode1987 thresholdNode180
def thresholdNode1989 : BoxExpr 1 := .mul ⟨(-199224835996063157453/590295810358705651712:ℚ),(-7/32:ℚ)⟩ thresholdNode1825 thresholdNode182
def thresholdNode1990 : BoxExpr 1 := .neg ⟨(7/32:ℚ),(199224835996063157453/590295810358705651712:ℚ)⟩ thresholdNode1989
def thresholdNode1991 : BoxExpr 1 := .add ⟨(39/32:ℚ),(789520646354768809165/590295810358705651712:ℚ)⟩ thresholdNode12 thresholdNode1990
def thresholdNode1992 : BoxExpr 1 := .inv ⟨(441342661950434132121/590295810358705651712:ℚ),(3874762242354580688161/4722366482869645213696:ℚ)⟩ thresholdNode1991
def thresholdNode1993 : BoxExpr 1 := .mul ⟨(583121225990742210748305/4722366482869645213696:ℚ),(337094188829144410108149/2361183241434822606848:ℚ)⟩ thresholdNode1988 thresholdNode1992
def thresholdNode1994 : BoxExpr 1 := .add ⟨(587843592473611855962001/4722366482869645213696:ℚ),(339455372070579232714997/2361183241434822606848:ℚ)⟩ thresholdNode1993 thresholdNode12
def thresholdNode1995 : BoxExpr 1 := .sqrt ⟨(52687881702219415234759/4722366482869645213696:ℚ),(14155531919960426051245/1180591620717411303424:ℚ)⟩ thresholdNode1994
def thresholdNode1996 : BoxExpr 1 := .add ⟨(57410248185089060448455/4722366482869645213696:ℚ),(15336123540677837354669/1180591620717411303424:ℚ)⟩ thresholdNode1995 thresholdNode12
def thresholdNode1997 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode1998 : BoxExpr 1 := .mul ⟨(28705124092544530224227/4722366482869645213696:ℚ),(15336123540677837354669/2361183241434822606848:ℚ)⟩ thresholdNode1996 thresholdNode1997
def thresholdNode1999 : BoxExpr 1 := .add ⟨(29885715713261941527651/4722366482869645213696:ℚ),(15926419351036543006381/2361183241434822606848:ℚ)⟩ thresholdNode1998 thresholdNode193
def thresholdNode2000 : BoxExpr 1 := .mul ⟨(29672955100420457588449/4722366482869645213696:ℚ),(31757575695700919190581/4722366482869645213696:ℚ)⟩ thresholdNode1828 thresholdNode1999
def thresholdNode2001 : BoxExpr 1 := .neg ⟨(-31757575695700919190581/4722366482869645213696:ℚ),(-29672955100420457588449/4722366482869645213696:ℚ)⟩ thresholdNode2000
def thresholdNode2002 : BoxExpr 1 := .add ⟨(-1088545473878810331471/4722366482869645213696:ℚ),(1692210253167066930595/4722366482869645213696:ℚ)⟩ thresholdNode1984 thresholdNode2001
def thresholdNode2003 : BoxExpr 1 := .mul ⟨(15509349256571774254143/2361183241434822606848:ℚ),(7754674628285887127095/1180591620717411303424:ℚ)⟩ thresholdNode1859 thresholdNode1859
def thresholdNode2004 : BoxExpr 1 := .mul ⟨(-328352044512030018765/2361183241434822606848:ℚ),(-82088011128007504691/590295810358705651712:ℚ)⟩ thresholdNode1846 thresholdNode5
def thresholdNode2005 : BoxExpr 1 := .neg ⟨(82088011128007504691/590295810358705651712:ℚ),(328352044512030018765/2361183241434822606848:ℚ)⟩ thresholdNode2004
def thresholdNode2006 : BoxExpr 1 := .add ⟨(672383821486713156403/590295810358705651712:ℚ),(2689535285946852625613/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode2005
def thresholdNode2007 : BoxExpr 1 := .mul ⟨(800795862516828603257025/4722366482869645213696:ℚ),(800795862516828603257325/4722366482869645213696:ℚ)⟩ thresholdNode2006 thresholdNode180
def thresholdNode2008 : BoxExpr 1 := .mul ⟨(-328352044512030018765/1180591620717411303424:ℚ),(-82088011128007504691/295147905179352825856:ℚ)⟩ thresholdNode1846 thresholdNode182
def thresholdNode2009 : BoxExpr 1 := .neg ⟨(82088011128007504691/295147905179352825856:ℚ),(328352044512030018765/1180591620717411303424:ℚ)⟩ thresholdNode2008
def thresholdNode2010 : BoxExpr 1 := .add ⟨(377235916307360330547/295147905179352825856:ℚ),(1508943665229441322189/1180591620717411303424:ℚ)⟩ thresholdNode12 thresholdNode2009
def thresholdNode2011 : BoxExpr 1 := .inv ⟨(1847380531195949227851/2361183241434822606848:ℚ),(1847380531195949227853/2361183241434822606848:ℚ)⟩ thresholdNode2010
def thresholdNode2012 : BoxExpr 1 := .mul ⟨(19579360941731750690873/147573952589676412928:ℚ),(313269775067708011054425/2361183241434822606848:ℚ)⟩ thresholdNode2007 thresholdNode2011
def thresholdNode2013 : BoxExpr 1 := .add ⟨(19726934894321427103801/147573952589676412928:ℚ),(315630958309142833661273/2361183241434822606848:ℚ)⟩ thresholdNode2012 thresholdNode12
def thresholdNode2014 : BoxExpr 1 := .sqrt ⟨(54598993735693013484627/4722366482869645213696:ℚ),(54598993735693013484667/4722366482869645213696:ℚ)⟩ thresholdNode2013
def thresholdNode2015 : BoxExpr 1 := .add ⟨(59321360218562658698323/4722366482869645213696:ℚ),(59321360218562658698363/4722366482869645213696:ℚ)⟩ thresholdNode2014 thresholdNode12
def thresholdNode2016 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode2017 : BoxExpr 1 := .mul ⟨(29660680109281329349161/4722366482869645213696:ℚ),(14830340054640664674591/2361183241434822606848:ℚ)⟩ thresholdNode2015 thresholdNode2016
def thresholdNode2018 : BoxExpr 1 := .add ⟨(30841271729998740652585/4722366482869645213696:ℚ),(15420635864999370326303/2361183241434822606848:ℚ)⟩ thresholdNode2017 thresholdNode193
def thresholdNode2019 : BoxExpr 1 := .mul ⟨(15346083340166203814843/2361183241434822606848:ℚ),(15346083340166203814857/2361183241434822606848:ℚ)⟩ thresholdNode1849 thresholdNode2018
def thresholdNode2020 : BoxExpr 1 := .neg ⟨(-15346083340166203814857/2361183241434822606848:ℚ),(-15346083340166203814843/2361183241434822606848:ℚ)⟩ thresholdNode2019
def thresholdNode2021 : BoxExpr 1 := .add ⟨(81632958202785219643/1180591620717411303424:ℚ),(163265916405570439347/2361183241434822606848:ℚ)⟩ thresholdNode2003 thresholdNode2020
def thresholdNode2022 : BoxExpr 1 := .mul ⟨(4971950268901304826339/2361183241434822606848:ℚ),(2485975134450652413181/1180591620717411303424:ℚ)⟩ thresholdNode1897 thresholdNode1859
def thresholdNode2023 : BoxExpr 1 := .mul ⟨(4971950268901304826339/2361183241434822606848:ℚ),(2485975134450652413181/1180591620717411303424:ℚ)⟩ thresholdNode1859 thresholdNode1897
def thresholdNode2024 : BoxExpr 1 := .add ⟨(4971950268901304826339/1180591620717411303424:ℚ),(2485975134450652413181/590295810358705651712:ℚ)⟩ thresholdNode2022 thresholdNode2023
def thresholdNode2025 : BoxExpr 1 := .mul ⟨(4288864349952949871989/4722366482869645213696:ℚ),(2144432174976474936003/2361183241434822606848:ℚ)⟩ thresholdNode1878 thresholdNode2018
def thresholdNode2026 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode2027 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1846 thresholdNode51
def thresholdNode2028 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode2026 thresholdNode2027
def thresholdNode2029 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode2028
def thresholdNode2030 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode2029
def thresholdNode2031 : BoxExpr 1 := .mul ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode2030 thresholdNode180
def thresholdNode2032 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2006 thresholdNode51
def thresholdNode2033 : BoxExpr 1 := .add ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode2031 thresholdNode2032
def thresholdNode2034 : BoxExpr 1 := .mul ⟨(-275024219538179872530613/1180591620717411303424:ℚ),(-550048439076359745060629/2361183241434822606848:ℚ)⟩ thresholdNode2033 thresholdNode2011
def thresholdNode2035 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode12 thresholdNode182
def thresholdNode2036 : BoxExpr 1 := .add ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode2035 thresholdNode2027
def thresholdNode2037 : BoxExpr 1 := .neg ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode2036
def thresholdNode2038 : BoxExpr 1 := .add ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode51 thresholdNode2037
def thresholdNode2039 : BoxExpr 1 := .mul ⟨(3857237244242759379841/2361183241434822606848:ℚ),(7714474488485518759693/4722366482869645213696:ℚ)⟩ thresholdNode2010 thresholdNode2010
def thresholdNode2040 : BoxExpr 1 := .inv ⟨(2890766601382414439669/4722366482869645213696:ℚ),(1445383300691207219837/2361183241434822606848:ℚ)⟩ thresholdNode2039
def thresholdNode2041 : BoxExpr 1 := .mul ⟨(-1445383300691207219837/590295810358705651712:ℚ),(-2890766601382414439669/1180591620717411303424:ℚ)⟩ thresholdNode2038 thresholdNode2040
def thresholdNode2042 : BoxExpr 1 := .neg ⟨(2890766601382414439669/1180591620717411303424:ℚ),(1445383300691207219837/590295810358705651712:ℚ)⟩ thresholdNode2041
def thresholdNode2043 : BoxExpr 1 := .mul ⟨(245101046507742209137575/590295810358705651712:ℚ),(1960808372061937673104727/4722366482869645213696:ℚ)⟩ thresholdNode2007 thresholdNode2042
def thresholdNode2044 : BoxExpr 1 := .add ⟨(215177873477304545744537/1180591620717411303424:ℚ),(860711493909218182983469/4722366482869645213696:ℚ)⟩ thresholdNode2034 thresholdNode2043
def thresholdNode2045 : BoxExpr 1 := .add ⟨(215177873477304545744537/1180591620717411303424:ℚ),(860711493909218182983469/4722366482869645213696:ℚ)⟩ thresholdNode2044 thresholdNode51
def thresholdNode2046 : BoxExpr 1 := .mul ⟨(54598993735693013484627/2361183241434822606848:ℚ),(54598993735693013484667/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode2014
def thresholdNode2047 : BoxExpr 1 := .inv ⟨(51055760538568203379/1180591620717411303424:ℚ),(204223042154272813517/4722366482869645213696:ℚ)⟩ thresholdNode2046
def thresholdNode2048 : BoxExpr 1 := .mul ⟨(37222252940537290313531/4722366482869645213696:ℚ),(4652781617567161289243/590295810358705651712:ℚ)⟩ thresholdNode2045 thresholdNode2047
def thresholdNode2049 : BoxExpr 1 := .add ⟨(37222252940537290313531/4722366482869645213696:ℚ),(4652781617567161289243/590295810358705651712:ℚ)⟩ thresholdNode2048 thresholdNode51
def thresholdNode2050 : BoxExpr 1 := .mul ⟨(18611126470268645156765/4722366482869645213696:ℚ),(4652781617567161289243/1180591620717411303424:ℚ)⟩ thresholdNode2049 thresholdNode2016
def thresholdNode2051 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode2052 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode2051
def thresholdNode2053 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode2052
def thresholdNode2054 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2053
def thresholdNode2055 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2015 thresholdNode2054
def thresholdNode2056 : BoxExpr 1 := .add ⟨(18611126470268645156765/4722366482869645213696:ℚ),(4652781617567161289243/1180591620717411303424:ℚ)⟩ thresholdNode2050 thresholdNode2055
def thresholdNode2057 : BoxExpr 1 := .add ⟨(18611126470268645156765/4722366482869645213696:ℚ),(4652781617567161289243/1180591620717411303424:ℚ)⟩ thresholdNode2056 thresholdNode51
def thresholdNode2058 : BoxExpr 1 := .mul ⟨(4630287304095024152611/1180591620717411303424:ℚ),(18521149216380096610655/4722366482869645213696:ℚ)⟩ thresholdNode1849 thresholdNode2057
def thresholdNode2059 : BoxExpr 1 := .add ⟨(22810013566333046482433/4722366482869645213696:ℚ),(22810013566333046482661/4722366482869645213696:ℚ)⟩ thresholdNode2025 thresholdNode2058
def thresholdNode2060 : BoxExpr 1 := .neg ⟨(-22810013566333046482661/4722366482869645213696:ℚ),(-22810013566333046482433/4722366482869645213696:ℚ)⟩ thresholdNode2059
def thresholdNode2061 : BoxExpr 1 := .add ⟨(-2922212490727827177305/4722366482869645213696:ℚ),(-2922212490727827176985/4722366482869645213696:ℚ)⟩ thresholdNode2024 thresholdNode2060
def thresholdNode2062 : BoxExpr 1 := .mul ⟨(-2967612246530980123301/1180591620717411303424:ℚ),(-11541791382375825107177/4722366482869645213696:ℚ)⟩ thresholdNode1983 thresholdNode1838
def thresholdNode2063 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1926 thresholdNode1829
def thresholdNode2064 : BoxExpr 1 := .mul ⟨(672299702680906325401/4722366482869645213696:ℚ),(1039416640036940933927/4722366482869645213696:ℚ)⟩ thresholdNode1824 thresholdNode1934
def thresholdNode2065 : BoxExpr 1 := .add ⟨(672299702680906325401/4722366482869645213696:ℚ),(1039416640036940933927/4722366482869645213696:ℚ)⟩ thresholdNode2063 thresholdNode2064
def thresholdNode2066 : BoxExpr 1 := .mul ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode1960 thresholdNode22
def thresholdNode2067 : BoxExpr 1 := .add ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode2066 thresholdNode1963
def thresholdNode2068 : BoxExpr 1 := .neg ⟨(1685884834384463341289/2361183241434822606848:ℚ),(3371769668768926682579/4722366482869645213696:ℚ)⟩ thresholdNode2067
def thresholdNode2069 : BoxExpr 1 := .add ⟨(4044069371449833007979/4722366482869645213696:ℚ),(2205593154402933808253/2361183241434822606848:ℚ)⟩ thresholdNode2065 thresholdNode2068
def thresholdNode2070 : BoxExpr 1 := .mul ⟨(-115801280597119081225/1180591620717411303424:ℚ),(-14475160074639885153/295147905179352825856:ℚ)⟩ thresholdNode1977 thresholdNode27
def thresholdNode2071 : BoxExpr 1 := .add ⟨(-115801280597119081225/1180591620717411303424:ℚ),(-14475160074639885153/295147905179352825856:ℚ)⟩ thresholdNode2070 thresholdNode1980
def thresholdNode2072 : BoxExpr 1 := .add ⟨(3580864249061356683079/4722366482869645213696:ℚ),(2089791873805814727029/2361183241434822606848:ℚ)⟩ thresholdNode2069 thresholdNode2071
def thresholdNode2073 : BoxExpr 1 := .mul ⟨(2715288789364318549997/4722366482869645213696:ℚ),(1849593881231758679919/2361183241434822606848:ℚ)⟩ thresholdNode2072 thresholdNode2072
def thresholdNode2074 : BoxExpr 1 := .add ⟨(-9155160196759601943207/4722366482869645213696:ℚ),(-7842603619912307747339/4722366482869645213696:ℚ)⟩ thresholdNode2062 thresholdNode2073
def thresholdNode2075 : BoxExpr 1 := .mul ⟨(-2967612246530980123301/1180591620717411303424:ℚ),(-11541791382375825107177/4722366482869645213696:ℚ)⟩ thresholdNode1838 thresholdNode1983
def thresholdNode2076 : BoxExpr 1 := .add ⟨(-9155160196759601943207/4722366482869645213696:ℚ),(-7842603619912307747339/4722366482869645213696:ℚ)⟩ thresholdNode2073 thresholdNode2075
def thresholdNode2077 : BoxExpr 1 := .add ⟨(-9155160196759601943207/2361183241434822606848:ℚ),(-7842603619912307747339/2361183241434822606848:ℚ)⟩ thresholdNode2074 thresholdNode2076
def thresholdNode2078 : BoxExpr 1 := .mul ⟨(-15926419351036543006381/1180591620717411303424:ℚ),(-29885715713261941527651/2361183241434822606848:ℚ)⟩ thresholdNode1944 thresholdNode1999
def thresholdNode2079 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode2080 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode2079 thresholdNode1940
def thresholdNode2081 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode2080
def thresholdNode2082 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode2081
def thresholdNode2083 : BoxExpr 1 := .mul ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode2082 thresholdNode180
def thresholdNode2084 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1987 thresholdNode51
def thresholdNode2085 : BoxExpr 1 := .add ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode2083 thresholdNode2084
def thresholdNode2086 : BoxExpr 1 := .mul ⟨(-288422835361834789397305/1180591620717411303424:ℚ),(-525630400893063401237909/2361183241434822606848:ℚ)⟩ thresholdNode2085 thresholdNode1992
def thresholdNode2087 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode12 thresholdNode182
def thresholdNode2088 : BoxExpr 1 := .add ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode2087 thresholdNode1940
def thresholdNode2089 : BoxExpr 1 := .neg ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode2088
def thresholdNode2090 : BoxExpr 1 := .add ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode51 thresholdNode2089
def thresholdNode2091 : BoxExpr 1 := .mul ⟨(1521/1024:ℚ),(2111967728999006564517/1180591620717411303424:ℚ)⟩ thresholdNode1991 thresholdNode1991
def thresholdNode2092 : BoxExpr 1 := .inv ⟨(1319903288076064694193/2361183241434822606848:ℚ),(3179292096290938000543/4722366482869645213696:ℚ)⟩ thresholdNode2091
def thresholdNode2093 : BoxExpr 1 := .mul ⟨(-3179292096290938000543/1180591620717411303424:ℚ),(-1319903288076064694193/590295810358705651712:ℚ)⟩ thresholdNode2090 thresholdNode2092
def thresholdNode2094 : BoxExpr 1 := .neg ⟨(1319903288076064694193/590295810358705651712:ℚ),(3179292096290938000543/1180591620717411303424:ℚ)⟩ thresholdNode2093
def thresholdNode2095 : BoxExpr 1 := .mul ⟨(1743913946888201004106229/4722366482869645213696:ℚ),(1106360414618730371637225/2361183241434822606848:ℚ)⟩ thresholdNode1988 thresholdNode2094
def thresholdNode2096 : BoxExpr 1 := .add ⟨(590222605440861846517009/4722366482869645213696:ℚ),(145182503431416742599829/590295810358705651712:ℚ)⟩ thresholdNode2086 thresholdNode2095
def thresholdNode2097 : BoxExpr 1 := .add ⟨(590222605440861846517009/4722366482869645213696:ℚ),(145182503431416742599829/590295810358705651712:ℚ)⟩ thresholdNode2096 thresholdNode51
def thresholdNode2098 : BoxExpr 1 := .mul ⟨(52687881702219415234759/2361183241434822606848:ℚ),(14155531919960426051245/590295810358705651712:ℚ)⟩ thresholdNode5 thresholdNode1995
def thresholdNode2099 : BoxExpr 1 := .inv ⟨(98463030763457210817/2361183241434822606848:ℚ),(211630686962987452957/4722366482869645213696:ℚ)⟩ thresholdNode2098
def thresholdNode2100 : BoxExpr 1 := .mul ⟨(24612704993406857229031/4722366482869645213696:ℚ),(52050298167500582895297/4722366482869645213696:ℚ)⟩ thresholdNode2097 thresholdNode2099
def thresholdNode2101 : BoxExpr 1 := .add ⟨(24612704993406857229031/4722366482869645213696:ℚ),(52050298167500582895297/4722366482869645213696:ℚ)⟩ thresholdNode2100 thresholdNode51
def thresholdNode2102 : BoxExpr 1 := .mul ⟨(12306352496703428614515/4722366482869645213696:ℚ),(26025149083750291447649/4722366482869645213696:ℚ)⟩ thresholdNode2101 thresholdNode1997
def thresholdNode2103 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode2104 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode2103
def thresholdNode2105 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode2104
def thresholdNode2106 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2105
def thresholdNode2107 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1996 thresholdNode2106
def thresholdNode2108 : BoxExpr 1 := .add ⟨(12306352496703428614515/4722366482869645213696:ℚ),(26025149083750291447649/4722366482869645213696:ℚ)⟩ thresholdNode2102 thresholdNode2107
def thresholdNode2109 : BoxExpr 1 := .add ⟨(12306352496703428614515/4722366482869645213696:ℚ),(26025149083750291447649/4722366482869645213696:ℚ)⟩ thresholdNode2108 thresholdNode51
def thresholdNode2110 : BoxExpr 1 := .mul ⟨(168250913040867188089/590295810358705651712:ℚ),(1097935976970715420449/1180591620717411303424:ℚ)⟩ thresholdNode1931 thresholdNode2109
def thresholdNode2111 : BoxExpr 1 := .add ⟨(-15589917524954808630203/1180591620717411303424:ℚ),(-27689843759320510686753/2361183241434822606848:ℚ)⟩ thresholdNode2078 thresholdNode2110
def thresholdNode2112 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode5
def thresholdNode2113 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode12 thresholdNode51
def thresholdNode2114 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2112 thresholdNode2113
def thresholdNode2115 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2113 thresholdNode1940
def thresholdNode2116 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2114 thresholdNode2115
def thresholdNode2117 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2116
def thresholdNode2118 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode2117
def thresholdNode2119 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2118 thresholdNode180
def thresholdNode2120 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2082 thresholdNode51
def thresholdNode2121 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2119 thresholdNode2120
def thresholdNode2122 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2120 thresholdNode2084
def thresholdNode2123 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2121 thresholdNode2122
def thresholdNode2124 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2123 thresholdNode1992
def thresholdNode2125 : BoxExpr 1 := .mul ⟨(-1893237073144351438095511/2361183241434822606848:ℚ),(-785989384512992001850695/1180591620717411303424:ℚ)⟩ thresholdNode2085 thresholdNode2094
def thresholdNode2126 : BoxExpr 1 := .add ⟨(-1893237073144351438095511/2361183241434822606848:ℚ),(-785989384512992001850695/1180591620717411303424:ℚ)⟩ thresholdNode2124 thresholdNode2125
def thresholdNode2127 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode182
def thresholdNode2128 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2127 thresholdNode2113
def thresholdNode2129 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2128 thresholdNode2115
def thresholdNode2130 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2129
def thresholdNode2131 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode2130
def thresholdNode2132 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2131 thresholdNode2092
def thresholdNode2133 : BoxExpr 1 := .mul ⟨(-789520646354768809165/147573952589676412928:ℚ),(-39/8:ℚ)⟩ thresholdNode2090 thresholdNode1991
def thresholdNode2134 : BoxExpr 1 := .mul ⟨(-789520646354768809165/147573952589676412928:ℚ),(-39/8:ℚ)⟩ thresholdNode1991 thresholdNode2090
def thresholdNode2135 : BoxExpr 1 := .add ⟨(-789520646354768809165/73786976294838206464:ℚ),(-39/4:ℚ)⟩ thresholdNode2133 thresholdNode2134
def thresholdNode2136 : BoxExpr 1 := .mul ⟨(2313441/1048576:ℚ),(15112449080818516348231/4722366482869645213696:ℚ)⟩ thresholdNode2091 thresholdNode2091
def thresholdNode2137 : BoxExpr 1 := .inv ⟨(737826975603704606763/2361183241434822606848:ℚ),(2140430707825062795895/4722366482869645213696:ℚ)⟩ thresholdNode2136
def thresholdNode2138 : BoxExpr 1 := .mul ⟨(-22902608573728171916083/4722366482869645213696:ℚ),(-7193813012136119915939/2361183241434822606848:ℚ)⟩ thresholdNode2135 thresholdNode2137
def thresholdNode2139 : BoxExpr 1 := .neg ⟨(7193813012136119915939/2361183241434822606848:ℚ),(22902608573728171916083/4722366482869645213696:ℚ)⟩ thresholdNode2138
def thresholdNode2140 : BoxExpr 1 := .mul ⟨(-22902608573728171916083/1180591620717411303424:ℚ),(-7193813012136119915939/590295810358705651712:ℚ)⟩ thresholdNode2090 thresholdNode2139
def thresholdNode2141 : BoxExpr 1 := .add ⟨(-22902608573728171916083/1180591620717411303424:ℚ),(-7193813012136119915939/590295810358705651712:ℚ)⟩ thresholdNode2132 thresholdNode2140
def thresholdNode2142 : BoxExpr 1 := .neg ⟨(7193813012136119915939/590295810358705651712:ℚ),(22902608573728171916083/1180591620717411303424:ℚ)⟩ thresholdNode2141
def thresholdNode2143 : BoxExpr 1 := .mul ⟨(4752390177562395958430981/2361183241434822606848:ℚ),(498116773130116080537441/147573952589676412928:ℚ)⟩ thresholdNode1988 thresholdNode2142
def thresholdNode2144 : BoxExpr 1 := .add ⟨(1429576552209022260167735/1180591620717411303424:ℚ),(3198944800527936642448833/1180591620717411303424:ℚ)⟩ thresholdNode2125 thresholdNode2143
def thresholdNode2145 : BoxExpr 1 := .add ⟨(965916031273693082239959/2361183241434822606848:ℚ),(1206477708007472320299069/590295810358705651712:ℚ)⟩ thresholdNode2126 thresholdNode2144
def thresholdNode2146 : BoxExpr 1 := .add ⟨(965916031273693082239959/2361183241434822606848:ℚ),(1206477708007472320299069/590295810358705651712:ℚ)⟩ thresholdNode2145 thresholdNode51
def thresholdNode2147 : BoxExpr 1 := .mul ⟨(80558779372349229766057/4722366482869645213696:ℚ),(216270979456890190436441/2361183241434822606848:ℚ)⟩ thresholdNode2146 thresholdNode2099
def thresholdNode2148 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1995
def thresholdNode2149 : BoxExpr 1 := .mul ⟨(24612704993406857229031/2361183241434822606848:ℚ),(52050298167500582895297/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode2100
def thresholdNode2150 : BoxExpr 1 := .add ⟨(24612704993406857229031/2361183241434822606848:ℚ),(52050298167500582895297/2361183241434822606848:ℚ)⟩ thresholdNode2148 thresholdNode2149
def thresholdNode2151 : BoxExpr 1 := .mul ⟨(1175687184947223711923977/2361183241434822606848:ℚ),(1357821488282316930860013/2361183241434822606848:ℚ)⟩ thresholdNode2098 thresholdNode2098
def thresholdNode2152 : BoxExpr 1 := .inv ⟨(256623677511422457/147573952589676412928:ℚ),(4742066062311399975/2361183241434822606848:ℚ)⟩ thresholdNode2151
def thresholdNode2153 : BoxExpr 1 := .mul ⟨(10700063863020889711/590295810358705651712:ℚ),(52267428495575970429/1180591620717411303424:ℚ)⟩ thresholdNode2150 thresholdNode2152
def thresholdNode2154 : BoxExpr 1 := .neg ⟨(-52267428495575970429/1180591620717411303424:ℚ),(-10700063863020889711/590295810358705651712:ℚ)⟩ thresholdNode2153
def thresholdNode2155 : BoxExpr 1 := .mul ⟨(-51420430121630630138773/4722366482869645213696:ℚ),(-5349368452893224172521/2361183241434822606848:ℚ)⟩ thresholdNode2097 thresholdNode2154
def thresholdNode2156 : BoxExpr 1 := .add ⟨(7284587312679649906821/1180591620717411303424:ℚ),(13182600687749810391495/147573952589676412928:ℚ)⟩ thresholdNode2147 thresholdNode2155
def thresholdNode2157 : BoxExpr 1 := .add ⟨(7284587312679649906821/1180591620717411303424:ℚ),(13182600687749810391495/147573952589676412928:ℚ)⟩ thresholdNode2156 thresholdNode51
def thresholdNode2158 : BoxExpr 1 := .mul ⟨(7284587312679649906821/2361183241434822606848:ℚ),(13182600687749810391495/295147905179352825856:ℚ)⟩ thresholdNode2157 thresholdNode1997
def thresholdNode2159 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2101 thresholdNode2106
def thresholdNode2160 : BoxExpr 1 := .add ⟨(7284587312679649906821/2361183241434822606848:ℚ),(13182600687749810391495/295147905179352825856:ℚ)⟩ thresholdNode2158 thresholdNode2159
def thresholdNode2161 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode5 thresholdNode51
def thresholdNode2162 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2112 thresholdNode2161
def thresholdNode2163 : BoxExpr 1 := .mul ⟨(16/1:ℚ),(16/1:ℚ)⟩ thresholdNode2103 thresholdNode2103
def thresholdNode2164 : BoxExpr 1 := .inv ⟨(1/16:ℚ),(1/16:ℚ)⟩ thresholdNode2163
def thresholdNode2165 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2162 thresholdNode2164
def thresholdNode2166 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2165
def thresholdNode2167 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode2166
def thresholdNode2168 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2105 thresholdNode2167
def thresholdNode2169 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2168
def thresholdNode2170 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode1996 thresholdNode2169
def thresholdNode2171 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2159 thresholdNode2170
def thresholdNode2172 : BoxExpr 1 := .add ⟨(7284587312679649906821/2361183241434822606848:ℚ),(13182600687749810391495/295147905179352825856:ℚ)⟩ thresholdNode2160 thresholdNode2171
def thresholdNode2173 : BoxExpr 1 := .add ⟨(7284587312679649906821/2361183241434822606848:ℚ),(13182600687749810391495/295147905179352825856:ℚ)⟩ thresholdNode2172 thresholdNode51
def thresholdNode2174 : BoxExpr 1 := .mul ⟨(7232727311205592633557/2361183241434822606848:ℚ),(210290802963274563227609/4722366482869645213696:ℚ)⟩ thresholdNode1828 thresholdNode2173
def thresholdNode2175 : BoxExpr 1 := .add ⟨(7905730963369061385913/2361183241434822606848:ℚ),(214682546871157424909405/4722366482869645213696:ℚ)⟩ thresholdNode2110 thresholdNode2174
def thresholdNode2176 : BoxExpr 1 := .add ⟨(-23274104086540555874493/2361183241434822606848:ℚ),(159302859352516403535899/4722366482869645213696:ℚ)⟩ thresholdNode2111 thresholdNode2175
def thresholdNode2177 : BoxExpr 1 := .neg ⟨(-159302859352516403535899/4722366482869645213696:ℚ),(23274104086540555874493/2361183241434822606848:ℚ)⟩ thresholdNode2176
def thresholdNode2178 : BoxExpr 1 := .add ⟨(-177613179746035607422313/4722366482869645213696:ℚ),(7715750233314124063577/1180591620717411303424:ℚ)⟩ thresholdNode2077 thresholdNode2177
def thresholdCell5Out1 : TaylorCertificate1 :=
  { center := (-89/1280:ℚ), radius := (19/1280:ℚ)
    whole := thresholdNode2002, centerValue := thresholdNode2021, gradient := thresholdNode2061, hessian := thresholdNode2178 }
theorem thresholdCell5Out1_check : thresholdCell5Out1.check = true := by decide +kernel
theorem thresholdCell5Out1_lower_pos : 0 < thresholdCell5Out1.lower := by decide +kernel
theorem thresholdCell5Out1_positive (x : ℝ) (hx : (-(27/320:ℝ)) ≤ x ∧ x ≤ (-(7/128:ℝ))) :
    0 < thresholdNode2002.eval (fun _ => x) := by
  apply thresholdCell5Out1.positive_sound thresholdCell5Out1_check thresholdCell5Out1_lower_pos x
  norm_num [thresholdCell5Out1]
  exact hx
theorem thresholdCell5_public (x : ℝ)
    (hx : (-(27/320:ℝ)) ≤ x ∧ x ≤ (-(7/128:ℝ))) : qc x < fA (43/20) x := by
  have hf := thresholdCell5Out0_positive x hx
  have hg := thresholdCell5Out1_positive x hx
  have hfa : thresholdNode1838.eval (fun _ => x) = thresholdFA 0 x := by
    norm_num [thresholdNode0, thresholdNode1, thresholdNode1818, thresholdNode3, thresholdNode1819, thresholdNode5, thresholdNode1820, thresholdNode1821, thresholdNode1822, thresholdNode9, thresholdNode1823, thresholdNode1824, thresholdNode12, thresholdNode1825, thresholdNode1826, thresholdNode1827, thresholdNode1828, thresholdNode1829, thresholdNode1830, thresholdNode19, thresholdNode1831, thresholdNode1832, thresholdNode22, thresholdNode1833, thresholdNode1834, thresholdNode1835, thresholdNode1836, thresholdNode27, thresholdNode1837, thresholdNode1838, BoxExpr.eval, thresholdFA, ftilde, pow_two, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  have hgap : thresholdNode2002.eval (fun _ => x) =
      (thresholdNode1838.eval (fun _ => x))^2 - (1-x^2)*(thresholdCapacity 1 x+1/4) := by
    norm_num [thresholdNode1984, thresholdNode12, thresholdNode1825, thresholdNode1826, thresholdNode1827, thresholdNode1828, thresholdNode5, thresholdNode1985, thresholdNode1986, thresholdNode1987, thresholdNode180, thresholdNode1988, thresholdNode182, thresholdNode1989, thresholdNode1990, thresholdNode1991, thresholdNode1992, thresholdNode1993, thresholdNode1994, thresholdNode1995, thresholdNode1996, thresholdNode1997, thresholdNode1998, thresholdNode193, thresholdNode1999, thresholdNode2000, thresholdNode2001, thresholdNode2002, BoxExpr.eval, thresholdCapacity, Da, D5, beta5, eta5, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  rw [hfa] at hf
  rw [hgap, hfa] at hg
  refine threshold_positive_to_public 0 1 x ?_ ?_ ?_ hf hg
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdFADomain] <;> constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdCapacityDomain] <;> linarith [hx.1,hx.2]
def thresholdNode2179 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode2180 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode2179 thresholdNode3
def thresholdNode2181 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode2182 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode2181
def thresholdNode2183 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode2182 thresholdNode2182
def thresholdNode2184 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode2183 thresholdNode9
def thresholdNode2185 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode2180 thresholdNode2184
def thresholdNode2186 : BoxExpr 1 := .var 0
def thresholdNode2187 : BoxExpr 1 := .mul ⟨(1475739525896764129/2361183241434822606848:ℚ),(49/16384:ℚ)⟩ thresholdNode2186 thresholdNode2186
def thresholdNode2188 : BoxExpr 1 := .neg ⟨(-49/16384:ℚ),(-1475739525896764129/2361183241434822606848:ℚ)⟩ thresholdNode2187
def thresholdNode2189 : BoxExpr 1 := .add ⟨(16335/16384:ℚ),(2359707501908925842719/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode2188
def thresholdNode2190 : BoxExpr 1 := .sqrt ⟨(4715299550889012099125/4722366482869645213696:ℚ),(2360445256343680887171/2361183241434822606848:ℚ)⟩ thresholdNode2189
def thresholdNode2191 : BoxExpr 1 := .mul ⟨(12256713887603353599855/4722366482869645213696:ℚ),(12271246754153893828141/4722366482869645213696:ℚ)⟩ thresholdNode2185 thresholdNode2190
def thresholdNode2192 : BoxExpr 1 := .neg ⟨(59029581035870565171/2361183241434822606848:ℚ),(7/128:ℚ)⟩ thresholdNode2186
def thresholdNode2193 : BoxExpr 1 := .add ⟨(-1/4722366482869645213696:ℚ),(70097627480096296141/2361183241434822606848:ℚ)⟩ thresholdNode19 thresholdNode2192
def thresholdNode2194 : BoxExpr 1 := .mul ⟨(-1/4722366482869645213696:ℚ),(50049706020788755445/2361183241434822606848:ℚ)⟩ thresholdNode2193 thresholdNode22
def thresholdNode2195 : BoxExpr 1 := .neg ⟨(-50049706020788755445/2361183241434822606848:ℚ),(1/4722366482869645213696:ℚ)⟩ thresholdNode2194
def thresholdNode2196 : BoxExpr 1 := .add ⟨(12156614475561776088965/4722366482869645213696:ℚ),(6135623377076946914071/2361183241434822606848:ℚ)⟩ thresholdNode2191 thresholdNode2195
def thresholdNode2197 : BoxExpr 1 := .mul ⟨(-1/4722366482869645213696:ℚ),(260127914476919849/295147905179352825856:ℚ)⟩ thresholdNode2193 thresholdNode2193
def thresholdNode2198 : BoxExpr 1 := .mul ⟨(-1/4722366482869645213696:ℚ),(3437850517726972725/4722366482869645213696:ℚ)⟩ thresholdNode2197 thresholdNode27
def thresholdNode2199 : BoxExpr 1 := .add ⟨(3039153618890444022241/1180591620717411303424:ℚ),(12274684604671620800867/4722366482869645213696:ℚ)⟩ thresholdNode2196 thresholdNode2198
def thresholdNode2200 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode2201 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode2200 thresholdNode3
def thresholdNode2202 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode2203 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode2202
def thresholdNode2204 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode2203 thresholdNode2203
def thresholdNode2205 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode2204 thresholdNode9
def thresholdNode2206 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode2201 thresholdNode2205
def thresholdNode2207 : BoxExpr 1 := .var 0
def thresholdNode2208 : BoxExpr 1 := .mul ⟨(7496872083706022461/4722366482869645213696:ℚ),(3748436041853011231/2361183241434822606848:ℚ)⟩ thresholdNode2207 thresholdNode2207
def thresholdNode2209 : BoxExpr 1 := .neg ⟨(-3748436041853011231/2361183241434822606848:ℚ),(-7496872083706022461/4722366482869645213696:ℚ)⟩ thresholdNode2208
def thresholdNode2210 : BoxExpr 1 := .add ⟨(2357434805392969595617/2361183241434822606848:ℚ),(4714869610785939191235/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode2209
def thresholdNode2211 : BoxExpr 1 := .sqrt ⟨(2359308278981159803099/2361183241434822606848:ℚ),(589827069745289950775/590295810358705651712:ℚ)⟩ thresholdNode2210
def thresholdNode2212 : BoxExpr 1 := .mul ⟨(6132667974969677734183/2361183241434822606848:ℚ),(12265335949939355468381/4722366482869645213696:ℚ)⟩ thresholdNode2206 thresholdNode2211
def thresholdNode2213 : BoxExpr 1 := .neg ⟨(188156789551837426483/4722366482869645213696:ℚ),(47039197387959356621/1180591620717411303424:ℚ)⟩ thresholdNode2207
def thresholdNode2214 : BoxExpr 1 := .add ⟨(17524406870024074035/1180591620717411303424:ℚ),(35048813740048148071/2361183241434822606848:ℚ)⟩ thresholdNode19 thresholdNode2213
def thresholdNode2215 : BoxExpr 1 := .mul ⟨(50049706020788755443/4722366482869645213696:ℚ),(25024853010394377723/2361183241434822606848:ℚ)⟩ thresholdNode2214 thresholdNode22
def thresholdNode2216 : BoxExpr 1 := .neg ⟨(-25024853010394377723/2361183241434822606848:ℚ),(-50049706020788755443/4722366482869645213696:ℚ)⟩ thresholdNode2215
def thresholdNode2217 : BoxExpr 1 := .add ⟨(1526910780489820839115/590295810358705651712:ℚ),(6107643121959283356469/2361183241434822606848:ℚ)⟩ thresholdNode2212 thresholdNode2216
def thresholdNode2218 : BoxExpr 1 := .mul ⟨(1040511657907679395/4722366482869645213696:ℚ),(260127914476919849/1180591620717411303424:ℚ)⟩ thresholdNode2214 thresholdNode2214
def thresholdNode2219 : BoxExpr 1 := .mul ⟨(214865657357935795/1180591620717411303424:ℚ),(429731314715871591/2361183241434822606848:ℚ)⟩ thresholdNode2218 thresholdNode27
def thresholdNode2220 : BoxExpr 1 := .add ⟨(3054036426636999614025/1180591620717411303424:ℚ),(1527018213318499807015/590295810358705651712:ℚ)⟩ thresholdNode2217 thresholdNode2219
def thresholdNode2221 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1
def thresholdNode2222 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode51
def thresholdNode2223 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2221 thresholdNode2222
def thresholdNode2224 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2223 thresholdNode51
def thresholdNode2225 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51
def thresholdNode2226 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode2225
def thresholdNode2227 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2226 thresholdNode2203
def thresholdNode2228 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2203 thresholdNode2226
def thresholdNode2229 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2227 thresholdNode2228
def thresholdNode2230 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2229 thresholdNode9
def thresholdNode2231 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2204 thresholdNode51
def thresholdNode2232 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2230 thresholdNode2231
def thresholdNode2233 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2224 thresholdNode2232
def thresholdNode2234 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2233 thresholdNode2211
def thresholdNode2235 : BoxExpr 1 := .mul ⟨(-47039197387959356621/1180591620717411303424:ℚ),(-188156789551837426483/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode2207
def thresholdNode2236 : BoxExpr 1 := .mul ⟨(-47039197387959356621/1180591620717411303424:ℚ),(-188156789551837426483/4722366482869645213696:ℚ)⟩ thresholdNode2207 thresholdNode12
def thresholdNode2237 : BoxExpr 1 := .add ⟨(-47039197387959356621/590295810358705651712:ℚ),(-188156789551837426483/2361183241434822606848:ℚ)⟩ thresholdNode2235 thresholdNode2236
def thresholdNode2238 : BoxExpr 1 := .neg ⟨(188156789551837426483/2361183241434822606848:ℚ),(47039197387959356621/590295810358705651712:ℚ)⟩ thresholdNode2237
def thresholdNode2239 : BoxExpr 1 := .add ⟨(188156789551837426483/2361183241434822606848:ℚ),(47039197387959356621/590295810358705651712:ℚ)⟩ thresholdNode51 thresholdNode2238
def thresholdNode2240 : BoxExpr 1 := .mul ⟨(2359308278981159803099/1180591620717411303424:ℚ),(589827069745289950775/295147905179352825856:ℚ)⟩ thresholdNode5 thresholdNode2211
def thresholdNode2241 : BoxExpr 1 := .inv ⟨(295382461742146515357/590295810358705651712:ℚ),(1181529846968586061429/2361183241434822606848:ℚ)⟩ thresholdNode2240
def thresholdNode2242 : BoxExpr 1 := .mul ⟨(188306319360618403539/4722366482869645213696:ℚ),(94153159680309201771/2361183241434822606848:ℚ)⟩ thresholdNode2239 thresholdNode2241
def thresholdNode2243 : BoxExpr 1 := .mul ⟨(244737015615011723619/2361183241434822606848:ℚ),(30592126951876465453/295147905179352825856:ℚ)⟩ thresholdNode2206 thresholdNode2242
def thresholdNode2244 : BoxExpr 1 := .add ⟨(244737015615011723619/2361183241434822606848:ℚ),(30592126951876465453/295147905179352825856:ℚ)⟩ thresholdNode2234 thresholdNode2243
def thresholdNode2245 : BoxExpr 1 := .neg ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode12
def thresholdNode2246 : BoxExpr 1 := .add ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode51 thresholdNode2245
def thresholdNode2247 : BoxExpr 1 := .mul ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode2246 thresholdNode22
def thresholdNode2248 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2214 thresholdNode51
def thresholdNode2249 : BoxExpr 1 := .add ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode2247 thresholdNode2248
def thresholdNode2250 : BoxExpr 1 := .neg ⟨(1685884834384463341289/2361183241434822606848:ℚ),(3371769668768926682579/4722366482869645213696:ℚ)⟩ thresholdNode2249
def thresholdNode2251 : BoxExpr 1 := .add ⟨(482655462499868766227/590295810358705651712:ℚ),(3861243699998950129827/4722366482869645213696:ℚ)⟩ thresholdNode2244 thresholdNode2250
def thresholdNode2252 : BoxExpr 1 := .mul ⟨(-35048813740048148071/2361183241434822606848:ℚ),(-17524406870024074035/1180591620717411303424:ℚ)⟩ thresholdNode2246 thresholdNode2214
def thresholdNode2253 : BoxExpr 1 := .mul ⟨(-35048813740048148071/2361183241434822606848:ℚ),(-17524406870024074035/1180591620717411303424:ℚ)⟩ thresholdNode2214 thresholdNode2246
def thresholdNode2254 : BoxExpr 1 := .add ⟨(-35048813740048148071/1180591620717411303424:ℚ),(-17524406870024074035/590295810358705651712:ℚ)⟩ thresholdNode2252 thresholdNode2253
def thresholdNode2255 : BoxExpr 1 := .mul ⟨(-115801280597119081227/4722366482869645213696:ℚ),(-115801280597119081223/4722366482869645213696:ℚ)⟩ thresholdNode2254 thresholdNode27
def thresholdNode2256 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2218 thresholdNode51
def thresholdNode2257 : BoxExpr 1 := .add ⟨(-115801280597119081227/4722366482869645213696:ℚ),(-115801280597119081223/4722366482869645213696:ℚ)⟩ thresholdNode2255 thresholdNode2256
def thresholdNode2258 : BoxExpr 1 := .add ⟨(3745442419401831048589/4722366482869645213696:ℚ),(936360604850457762151/1180591620717411303424:ℚ)⟩ thresholdNode2251 thresholdNode2257
def thresholdNode2259 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode1
def thresholdNode2260 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode51
def thresholdNode2261 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2259 thresholdNode2260
def thresholdNode2262 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode51
def thresholdNode2263 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2260 thresholdNode2262
def thresholdNode2264 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2261 thresholdNode2263
def thresholdNode2265 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2264 thresholdNode51
def thresholdNode2266 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51
def thresholdNode2267 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode2266
def thresholdNode2268 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2267 thresholdNode2182
def thresholdNode2269 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2267 thresholdNode2267
def thresholdNode2270 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2268 thresholdNode2269
def thresholdNode2271 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2182 thresholdNode2267
def thresholdNode2272 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2269 thresholdNode2271
def thresholdNode2273 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2270 thresholdNode2272
def thresholdNode2274 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2273 thresholdNode9
def thresholdNode2275 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2268 thresholdNode2271
def thresholdNode2276 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2275 thresholdNode51
def thresholdNode2277 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2274 thresholdNode2276
def thresholdNode2278 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2183 thresholdNode51
def thresholdNode2279 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2276 thresholdNode2278
def thresholdNode2280 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2277 thresholdNode2279
def thresholdNode2281 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2265 thresholdNode2280
def thresholdNode2282 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2281 thresholdNode2190
def thresholdNode2283 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2259 thresholdNode2262
def thresholdNode2284 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2283 thresholdNode51
def thresholdNode2285 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2275 thresholdNode9
def thresholdNode2286 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2285 thresholdNode2278
def thresholdNode2287 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2284 thresholdNode2286
def thresholdNode2288 : BoxExpr 1 := .mul ⟨(-7/128:ℚ),(-59029581035870565171/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode2186
def thresholdNode2289 : BoxExpr 1 := .mul ⟨(-7/128:ℚ),(-59029581035870565171/2361183241434822606848:ℚ)⟩ thresholdNode2186 thresholdNode12
def thresholdNode2290 : BoxExpr 1 := .add ⟨(-7/64:ℚ),(-59029581035870565171/1180591620717411303424:ℚ)⟩ thresholdNode2288 thresholdNode2289
def thresholdNode2291 : BoxExpr 1 := .neg ⟨(59029581035870565171/1180591620717411303424:ℚ),(7/64:ℚ)⟩ thresholdNode2290
def thresholdNode2292 : BoxExpr 1 := .add ⟨(59029581035870565171/1180591620717411303424:ℚ),(7/64:ℚ)⟩ thresholdNode51 thresholdNode2291
def thresholdNode2293 : BoxExpr 1 := .mul ⟨(4715299550889012099125/2361183241434822606848:ℚ),(2360445256343680887171/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode2190
def thresholdNode2294 : BoxExpr 1 := .inv ⟨(1180960728627232463875/2361183241434822606848:ℚ),(2364722003114954828041/4722366482869645213696:ℚ)⟩ thresholdNode2293
def thresholdNode2295 : BoxExpr 1 := .mul ⟨(118096072862723246387/4722366482869645213696:ℚ),(258641469090698184317/4722366482869645213696:ℚ)⟩ thresholdNode2292 thresholdNode2294
def thresholdNode2296 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2287 thresholdNode2295
def thresholdNode2297 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2282 thresholdNode2296
def thresholdNode2298 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode2186
def thresholdNode2299 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode12
def thresholdNode2300 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode2298 thresholdNode2299
def thresholdNode2301 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2186 thresholdNode51
def thresholdNode2302 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode2299 thresholdNode2301
def thresholdNode2303 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode2300 thresholdNode2302
def thresholdNode2304 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode2303
def thresholdNode2305 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode2304
def thresholdNode2306 : BoxExpr 1 := .mul ⟨(-2364722003114954828041/2361183241434822606848:ℚ),(-1180960728627232463875/1180591620717411303424:ℚ)⟩ thresholdNode2305 thresholdNode2294
def thresholdNode2307 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode2190
def thresholdNode2308 : BoxExpr 1 := .mul ⟨(118096072862723246387/2361183241434822606848:ℚ),(258641469090698184317/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode2295
def thresholdNode2309 : BoxExpr 1 := .add ⟨(118096072862723246387/2361183241434822606848:ℚ),(258641469090698184317/2361183241434822606848:ℚ)⟩ thresholdNode2307 thresholdNode2308
def thresholdNode2310 : BoxExpr 1 := .mul ⟨(2354121597219105669119/590295810358705651712:ℚ),(18877660015271406741755/4722366482869645213696:ℚ)⟩ thresholdNode2293 thresholdNode2293
def thresholdNode2311 : BoxExpr 1 := .inv ⟨(1153642531188840001/4611686018427387904:ℚ),(1184133034210839718109/4722366482869645213696:ℚ)⟩ thresholdNode2310
def thresholdNode2312 : BoxExpr 1 := .mul ⟨(29542482267097747689/2361183241434822606848:ℚ),(129708657165044354205/4722366482869645213696:ℚ)⟩ thresholdNode2309 thresholdNode2311
def thresholdNode2313 : BoxExpr 1 := .neg ⟨(-129708657165044354205/4722366482869645213696:ℚ),(-29542482267097747689/2361183241434822606848:ℚ)⟩ thresholdNode2312
def thresholdNode2314 : BoxExpr 1 := .mul ⟨(-7093442188713363121/2361183241434822606848:ℚ),(-184640514169360923/295147905179352825856:ℚ)⟩ thresholdNode2292 thresholdNode2313
def thresholdNode2315 : BoxExpr 1 := .add ⟨(-1185907722651834095581/1180591620717411303424:ℚ),(-1181699290683909907567/1180591620717411303424:ℚ)⟩ thresholdNode2306 thresholdNode2314
def thresholdNode2316 : BoxExpr 1 := .mul ⟨(-12330356955500179825399/4722366482869645213696:ℚ),(-3071650051239221218233/1180591620717411303424:ℚ)⟩ thresholdNode2185 thresholdNode2315
def thresholdNode2317 : BoxExpr 1 := .add ⟨(-12330356955500179825399/4722366482869645213696:ℚ),(-3071650051239221218233/1180591620717411303424:ℚ)⟩ thresholdNode2296 thresholdNode2316
def thresholdNode2318 : BoxExpr 1 := .add ⟨(-12330356955500179825399/4722366482869645213696:ℚ),(-3071650051239221218233/1180591620717411303424:ℚ)⟩ thresholdNode2297 thresholdNode2317
def thresholdNode2319 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2267 thresholdNode22
def thresholdNode2320 : BoxExpr 1 := .neg ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode12
def thresholdNode2321 : BoxExpr 1 := .add ⟨(-1/1:ℚ),(-1/1:ℚ)⟩ thresholdNode51 thresholdNode2320
def thresholdNode2322 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2321 thresholdNode51
def thresholdNode2323 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2319 thresholdNode2322
def thresholdNode2324 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2193 thresholdNode51
def thresholdNode2325 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2322 thresholdNode2324
def thresholdNode2326 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2323 thresholdNode2325
def thresholdNode2327 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2326
def thresholdNode2328 : BoxExpr 1 := .add ⟨(-12330356955500179825399/4722366482869645213696:ℚ),(-3071650051239221218233/1180591620717411303424:ℚ)⟩ thresholdNode2318 thresholdNode2327
def thresholdNode2329 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2267 thresholdNode2193
def thresholdNode2330 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode2321 thresholdNode2321
def thresholdNode2331 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode2329 thresholdNode2330
def thresholdNode2332 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2193 thresholdNode2267
def thresholdNode2333 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode2330 thresholdNode2332
def thresholdNode2334 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode2331 thresholdNode2333
def thresholdNode2335 : BoxExpr 1 := .mul ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode2334 thresholdNode27
def thresholdNode2336 : BoxExpr 1 := .mul ⟨(-70097627480096296141/2361183241434822606848:ℚ),(1/4722366482869645213696:ℚ)⟩ thresholdNode2321 thresholdNode2193
def thresholdNode2337 : BoxExpr 1 := .mul ⟨(-70097627480096296141/2361183241434822606848:ℚ),(1/4722366482869645213696:ℚ)⟩ thresholdNode2193 thresholdNode2321
def thresholdNode2338 : BoxExpr 1 := .add ⟨(-70097627480096296141/1180591620717411303424:ℚ),(1/2361183241434822606848:ℚ)⟩ thresholdNode2336 thresholdNode2337
def thresholdNode2339 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2338 thresholdNode51
def thresholdNode2340 : BoxExpr 1 := .add ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode2335 thresholdNode2339
def thresholdNode2341 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2197 thresholdNode51
def thresholdNode2342 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2339 thresholdNode2341
def thresholdNode2343 : BoxExpr 1 := .add ⟨(243792169678145434157/147573952589676412928:ℚ),(3900674714850326946513/2361183241434822606848:ℚ)⟩ thresholdNode2340 thresholdNode2342
def thresholdNode2344 : BoxExpr 1 := .add ⟨(-4529007525799525932375/4722366482869645213696:ℚ),(-2242625387628115489953/2361183241434822606848:ℚ)⟩ thresholdNode2328 thresholdNode2343
def thresholdCell6Out0 : TaylorCertificate1 :=
  { center := (-51/1280:ℚ), radius := (19/1280:ℚ)
    whole := thresholdNode2199, centerValue := thresholdNode2220, gradient := thresholdNode2258, hessian := thresholdNode2344 }
theorem thresholdCell6Out0_check : thresholdCell6Out0.check = true := by decide +kernel
theorem thresholdCell6Out0_lower_pos : 0 < thresholdCell6Out0.lower := by decide +kernel
theorem thresholdCell6Out0_positive (x : ℝ) (hx : (-(7/128:ℝ)) ≤ x ∧ x ≤ (-(1/40:ℝ))) :
    0 < thresholdNode2199.eval (fun _ => x) := by
  apply thresholdCell6Out0.positive_sound thresholdCell6Out0_check thresholdCell6Out0_lower_pos x
  norm_num [thresholdCell6Out0]
  exact hx
def thresholdNode2345 : BoxExpr 1 := .mul ⟨(15647162925994945641949/2361183241434822606848:ℚ),(31905165067283384494377/4722366482869645213696:ℚ)⟩ thresholdNode2199 thresholdNode2199
def thresholdNode2346 : BoxExpr 1 := .mul ⟨(-7/64:ℚ),(-59029581035870565171/1180591620717411303424:ℚ)⟩ thresholdNode2186 thresholdNode5
def thresholdNode2347 : BoxExpr 1 := .neg ⟨(59029581035870565171/1180591620717411303424:ℚ),(7/64:ℚ)⟩ thresholdNode2346
def thresholdNode2348 : BoxExpr 1 := .add ⟨(1239621201753281868595/1180591620717411303424:ℚ),(71/64:ℚ)⟩ thresholdNode12 thresholdNode2347
def thresholdNode2349 : BoxExpr 1 := .mul ⟨(184545548563548978528393/1180591620717411303424:ℚ),(779924639762617706876075/4722366482869645213696:ℚ)⟩ thresholdNode2348 thresholdNode180
def thresholdNode2350 : BoxExpr 1 := .mul ⟨(-7/32:ℚ),(-59029581035870565171/590295810358705651712:ℚ)⟩ thresholdNode2186 thresholdNode182
def thresholdNode2351 : BoxExpr 1 := .neg ⟨(59029581035870565171/590295810358705651712:ℚ),(7/32:ℚ)⟩ thresholdNode2350
def thresholdNode2352 : BoxExpr 1 := .add ⟨(649325391394576216883/590295810358705651712:ℚ),(39/32:ℚ)⟩ thresholdNode12 thresholdNode2351
def thresholdNode2353 : BoxExpr 1 := .inv ⟨(121086320073580646505/147573952589676412928:ℚ),(4293060438972404739725/4722366482869645213696:ℚ)⟩ thresholdNode2352
def thresholdNode2354 : BoxExpr 1 := .mul ⟨(151421988564963264433521/1180591620717411303424:ℚ),(22156949993256184854441/147573952589676412928:ℚ)⟩ thresholdNode2349 thresholdNode2353
def thresholdNode2355 : BoxExpr 1 := .add ⟨(152602580185680675736945/1180591620717411303424:ℚ),(22304523945845861267369/147573952589676412928:ℚ)⟩ thresholdNode2354 thresholdNode12
def thresholdNode2356 : BoxExpr 1 := .sqrt ⟨(26844837676325887273867/2361183241434822606848:ℚ),(14514140436017966329723/1180591620717411303424:ℚ)⟩ thresholdNode2355
def thresholdNode2357 : BoxExpr 1 := .add ⟨(29206020917760709880715/2361183241434822606848:ℚ),(15694732056735377633147/1180591620717411303424:ℚ)⟩ thresholdNode2356 thresholdNode12
def thresholdNode2358 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode2359 : BoxExpr 1 := .mul ⟨(29206020917760709880715/4722366482869645213696:ℚ),(15694732056735377633147/2361183241434822606848:ℚ)⟩ thresholdNode2357 thresholdNode2358
def thresholdNode2360 : BoxExpr 1 := .add ⟨(30386612538478121184139/4722366482869645213696:ℚ),(16285027867094083284859/2361183241434822606848:ℚ)⟩ thresholdNode2359 thresholdNode193
def thresholdNode2361 : BoxExpr 1 := .mul ⟨(15147867303956302171109/2361183241434822606848:ℚ),(2034356215584643685351/295147905179352825856:ℚ)⟩ thresholdNode2189 thresholdNode2360
def thresholdNode2362 : BoxExpr 1 := .neg ⟨(-2034356215584643685351/295147905179352825856:ℚ),(-15147867303956302171109/2361183241434822606848:ℚ)⟩ thresholdNode2361
def thresholdNode2363 : BoxExpr 1 := .add ⟨(-627686798682203840859/2361183241434822606848:ℚ),(1609430459370780152159/4722366482869645213696:ℚ)⟩ thresholdNode2345 thresholdNode2362
def thresholdNode2364 : BoxExpr 1 := .mul ⟨(31601574436240236395809/4722366482869645213696:ℚ),(15800787218120118197957/2361183241434822606848:ℚ)⟩ thresholdNode2220 thresholdNode2220
def thresholdNode2365 : BoxExpr 1 := .mul ⟨(-47039197387959356621/590295810358705651712:ℚ),(-188156789551837426483/2361183241434822606848:ℚ)⟩ thresholdNode2207 thresholdNode5
def thresholdNode2366 : BoxExpr 1 := .neg ⟨(188156789551837426483/2361183241434822606848:ℚ),(47039197387959356621/590295810358705651712:ℚ)⟩ thresholdNode2365
def thresholdNode2367 : BoxExpr 1 := .add ⟨(2549340030986660033331/2361183241434822606848:ℚ),(637335007746665008333/590295810358705651712:ℚ)⟩ thresholdNode12 thresholdNode2366
def thresholdNode2368 : BoxExpr 1 := .mul ⟨(379526708504203405247411/2361183241434822606848:ℚ),(379526708504203405247561/2361183241434822606848:ℚ)⟩ thresholdNode2367 thresholdNode180
def thresholdNode2369 : BoxExpr 1 := .mul ⟨(-47039197387959356621/295147905179352825856:ℚ),(-188156789551837426483/1180591620717411303424:ℚ)⟩ thresholdNode2207 thresholdNode182
def thresholdNode2370 : BoxExpr 1 := .neg ⟨(188156789551837426483/1180591620717411303424:ℚ),(47039197387959356621/295147905179352825856:ℚ)⟩ thresholdNode2369
def thresholdNode2371 : BoxExpr 1 := .add ⟨(1368748410269248729907/1180591620717411303424:ℚ),(342187102567312182477/295147905179352825856:ℚ)⟩ thresholdNode12 thresholdNode2370
def thresholdNode2372 : BoxExpr 1 := .inv ⟨(4073200200857915009115/4722366482869645213696:ℚ),(4073200200857915009119/4722366482869645213696:ℚ)⟩ thresholdNode2371
def thresholdNode2373 : BoxExpr 1 := .mul ⟨(654709146745795631693189/4722366482869645213696:ℚ),(163677286686448907923523/1180591620717411303424:ℚ)⟩ thresholdNode2368 thresholdNode2372
def thresholdNode2374 : BoxExpr 1 := .add ⟨(659431513228665276906885/4722366482869645213696:ℚ),(164857878307166319226947/1180591620717411303424:ℚ)⟩ thresholdNode2373 thresholdNode12
def thresholdNode2375 : BoxExpr 1 := .sqrt ⟨(27901959052273820422303/2361183241434822606848:ℚ),(55803918104547640844645/4722366482869645213696:ℚ)⟩ thresholdNode2374
def thresholdNode2376 : BoxExpr 1 := .add ⟨(30263142293708643029151/2361183241434822606848:ℚ),(60526284587417286058341/4722366482869645213696:ℚ)⟩ thresholdNode2375 thresholdNode12
def thresholdNode2377 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode2378 : BoxExpr 1 := .mul ⟨(30263142293708643029151/4722366482869645213696:ℚ),(30263142293708643029171/4722366482869645213696:ℚ)⟩ thresholdNode2376 thresholdNode2377
def thresholdNode2379 : BoxExpr 1 := .add ⟨(31443733914426054332575/4722366482869645213696:ℚ),(31443733914426054332595/4722366482869645213696:ℚ)⟩ thresholdNode2378 thresholdNode193
def thresholdNode2380 : BoxExpr 1 := .mul ⟨(15696908109583808975575/2361183241434822606848:ℚ),(15696908109583808975589/2361183241434822606848:ℚ)⟩ thresholdNode2210 thresholdNode2379
def thresholdNode2381 : BoxExpr 1 := .neg ⟨(-15696908109583808975589/2361183241434822606848:ℚ),(-15696908109583808975575/2361183241434822606848:ℚ)⟩ thresholdNode2380
def thresholdNode2382 : BoxExpr 1 := .add ⟨(207758217072618444631/4722366482869645213696:ℚ),(51939554268154611191/1180591620717411303424:ℚ)⟩ thresholdNode2364 thresholdNode2381
def thresholdNode2383 : BoxExpr 1 := .mul ⟨(2422242666726202379367/1180591620717411303424:ℚ),(9688970666904809517523/4722366482869645213696:ℚ)⟩ thresholdNode2258 thresholdNode2220
def thresholdNode2384 : BoxExpr 1 := .mul ⟨(2422242666726202379367/1180591620717411303424:ℚ),(9688970666904809517523/4722366482869645213696:ℚ)⟩ thresholdNode2220 thresholdNode2258
def thresholdNode2385 : BoxExpr 1 := .add ⟨(2422242666726202379367/590295810358705651712:ℚ),(9688970666904809517523/2361183241434822606848:ℚ)⟩ thresholdNode2383 thresholdNode2384
def thresholdNode2386 : BoxExpr 1 := .mul ⟨(156604534144114137789/295147905179352825856:ℚ),(78302267072057068895/147573952589676412928:ℚ)⟩ thresholdNode2239 thresholdNode2379
def thresholdNode2387 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode2388 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2207 thresholdNode51
def thresholdNode2389 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode2387 thresholdNode2388
def thresholdNode2390 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode2389
def thresholdNode2391 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode2390
def thresholdNode2392 : BoxExpr 1 := .mul ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode2391 thresholdNode180
def thresholdNode2393 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2367 thresholdNode51
def thresholdNode2394 : BoxExpr 1 := .add ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode2392 thresholdNode2393
def thresholdNode2395 : BoxExpr 1 := .mul ⟨(-1212775264594237928463349/4722366482869645213696:ℚ),(-303193816148559482115539/1180591620717411303424:ℚ)⟩ thresholdNode2394 thresholdNode2372
def thresholdNode2396 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode12 thresholdNode182
def thresholdNode2397 : BoxExpr 1 := .add ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode2396 thresholdNode2388
def thresholdNode2398 : BoxExpr 1 := .neg ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode2397
def thresholdNode2399 : BoxExpr 1 := .add ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode51 thresholdNode2398
def thresholdNode2400 : BoxExpr 1 := .mul ⟨(3173785376311820492471/2361183241434822606848:ℚ),(6347570752623640984953/4722366482869645213696:ℚ)⟩ thresholdNode2371 thresholdNode2371
def thresholdNode2401 : BoxExpr 1 := .inv ⟨(1756636205221742321989/2361183241434822606848:ℚ),(3513272410443484643985/4722366482869645213696:ℚ)⟩ thresholdNode2400
def thresholdNode2402 : BoxExpr 1 := .mul ⟨(-3513272410443484643985/1180591620717411303424:ℚ),(-1756636205221742321989/590295810358705651712:ℚ)⟩ thresholdNode2399 thresholdNode2401
def thresholdNode2403 : BoxExpr 1 := .neg ⟨(1756636205221742321989/590295810358705651712:ℚ),(3513272410443484643985/1180591620717411303424:ℚ)⟩ thresholdNode2402
def thresholdNode2404 : BoxExpr 1 := .mul ⟨(141177174500441106564465/295147905179352825856:ℚ),(2258834792007057705036835/4722366482869645213696:ℚ)⟩ thresholdNode2368 thresholdNode2403
def thresholdNode2405 : BoxExpr 1 := .add ⟨(1046059527412819776568091/4722366482869645213696:ℚ),(1046059527412819776574679/4722366482869645213696:ℚ)⟩ thresholdNode2395 thresholdNode2404
def thresholdNode2406 : BoxExpr 1 := .add ⟨(1046059527412819776568091/4722366482869645213696:ℚ),(1046059527412819776574679/4722366482869645213696:ℚ)⟩ thresholdNode2405 thresholdNode51
def thresholdNode2407 : BoxExpr 1 := .mul ⟨(27901959052273820422303/1180591620717411303424:ℚ),(55803918104547640844645/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode2375
def thresholdNode2408 : BoxExpr 1 := .inv ⟨(199813435651154248065/4722366482869645213696:ℚ),(99906717825577124033/2361183241434822606848:ℚ)⟩ thresholdNode2407
def thresholdNode2409 : BoxExpr 1 := .mul ⟨(11065254508845577198679/1180591620717411303424:ℚ),(22130509017691154397609/2361183241434822606848:ℚ)⟩ thresholdNode2406 thresholdNode2408
def thresholdNode2410 : BoxExpr 1 := .add ⟨(11065254508845577198679/1180591620717411303424:ℚ),(22130509017691154397609/2361183241434822606848:ℚ)⟩ thresholdNode2409 thresholdNode51
def thresholdNode2411 : BoxExpr 1 := .mul ⟨(11065254508845577198679/2361183241434822606848:ℚ),(22130509017691154397609/4722366482869645213696:ℚ)⟩ thresholdNode2410 thresholdNode2377
def thresholdNode2412 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode2413 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode2412
def thresholdNode2414 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode2413
def thresholdNode2415 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2414
def thresholdNode2416 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2376 thresholdNode2415
def thresholdNode2417 : BoxExpr 1 := .add ⟨(11065254508845577198679/2361183241434822606848:ℚ),(22130509017691154397609/4722366482869645213696:ℚ)⟩ thresholdNode2411 thresholdNode2416
def thresholdNode2418 : BoxExpr 1 := .add ⟨(11065254508845577198679/2361183241434822606848:ℚ),(22130509017691154397609/4722366482869645213696:ℚ)⟩ thresholdNode2417 thresholdNode51
def thresholdNode2419 : BoxExpr 1 := .mul ⟨(1380961018395621210939/295147905179352825856:ℚ),(1380961018395621210955/295147905179352825856:ℚ)⟩ thresholdNode2210 thresholdNode2418
def thresholdNode2420 : BoxExpr 1 := .add ⟨(192195694067466918591/36893488147419103232:ℚ),(1537565552539735348745/295147905179352825856:ℚ)⟩ thresholdNode2386 thresholdNode2419
def thresholdNode2421 : BoxExpr 1 := .neg ⟨(-1537565552539735348745/295147905179352825856:ℚ),(-192195694067466918591/36893488147419103232:ℚ)⟩ thresholdNode2420
def thresholdNode2422 : BoxExpr 1 := .add ⟨(-652888438353268318123/590295810358705651712:ℚ),(-2611553753413073272301/2361183241434822606848:ℚ)⟩ thresholdNode2385 thresholdNode2421
def thresholdNode2423 : BoxExpr 1 := .mul ⟨(-11772093325038089409117/4722366482869645213696:ℚ),(-11546216224173908645653/4722366482869645213696:ℚ)⟩ thresholdNode2344 thresholdNode2199
def thresholdNode2424 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2287 thresholdNode2190
def thresholdNode2425 : BoxExpr 1 := .mul ⟨(306973026995719670495/4722366482869645213696:ℚ),(672299702680906325405/4722366482869645213696:ℚ)⟩ thresholdNode2185 thresholdNode2295
def thresholdNode2426 : BoxExpr 1 := .add ⟨(306973026995719670495/4722366482869645213696:ℚ),(672299702680906325405/4722366482869645213696:ℚ)⟩ thresholdNode2424 thresholdNode2425
def thresholdNode2427 : BoxExpr 1 := .mul ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode2321 thresholdNode22
def thresholdNode2428 : BoxExpr 1 := .add ⟨(-3371769668768926682579/4722366482869645213696:ℚ),(-1685884834384463341289/2361183241434822606848:ℚ)⟩ thresholdNode2427 thresholdNode2324
def thresholdNode2429 : BoxExpr 1 := .neg ⟨(1685884834384463341289/2361183241434822606848:ℚ),(3371769668768926682579/4722366482869645213696:ℚ)⟩ thresholdNode2428
def thresholdNode2430 : BoxExpr 1 := .add ⟨(3678742695764646353073/4722366482869645213696:ℚ),(252754335715614562999/295147905179352825856:ℚ)⟩ thresholdNode2426 thresholdNode2429
def thresholdNode2431 : BoxExpr 1 := .mul ⟨(-115801280597119081225/2361183241434822606848:ℚ),(1/2361183241434822606848:ℚ)⟩ thresholdNode2338 thresholdNode27
def thresholdNode2432 : BoxExpr 1 := .add ⟨(-115801280597119081225/2361183241434822606848:ℚ),(1/2361183241434822606848:ℚ)⟩ thresholdNode2431 thresholdNode2341
def thresholdNode2433 : BoxExpr 1 := .add ⟨(3447140134570408190623/4722366482869645213696:ℚ),(2022034685724916503993/2361183241434822606848:ℚ)⟩ thresholdNode2430 thresholdNode2432
def thresholdNode2434 : BoxExpr 1 := .mul ⟨(314534438148510498751/590295810358705651712:ℚ),(1731599732933104934417/2361183241434822606848:ℚ)⟩ thresholdNode2433 thresholdNode2433
def thresholdNode2435 : BoxExpr 1 := .add ⟨(-9255817819850005419109/4722366482869645213696:ℚ),(-8083016758307698776819/4722366482869645213696:ℚ)⟩ thresholdNode2423 thresholdNode2434
def thresholdNode2436 : BoxExpr 1 := .mul ⟨(-11772093325038089409117/4722366482869645213696:ℚ),(-11546216224173908645653/4722366482869645213696:ℚ)⟩ thresholdNode2199 thresholdNode2344
def thresholdNode2437 : BoxExpr 1 := .add ⟨(-9255817819850005419109/4722366482869645213696:ℚ),(-8083016758307698776819/4722366482869645213696:ℚ)⟩ thresholdNode2434 thresholdNode2436
def thresholdNode2438 : BoxExpr 1 := .add ⟨(-9255817819850005419109/2361183241434822606848:ℚ),(-8083016758307698776819/2361183241434822606848:ℚ)⟩ thresholdNode2435 thresholdNode2437
def thresholdNode2439 : BoxExpr 1 := .mul ⟨(-16285027867094083284859/1180591620717411303424:ℚ),(-30386612538478121184139/2361183241434822606848:ℚ)⟩ thresholdNode2305 thresholdNode2360
def thresholdNode2440 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode2441 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode2440 thresholdNode2301
def thresholdNode2442 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode2441
def thresholdNode2443 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode51 thresholdNode2442
def thresholdNode2444 : BoxExpr 1 := .mul ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode2443 thresholdNode180
def thresholdNode2445 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2348 thresholdNode51
def thresholdNode2446 : BoxExpr 1 := .add ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode2444 thresholdNode2445
def thresholdNode2447 : BoxExpr 1 := .mul ⟨(-639118782904065726505565/2361183241434822606848:ℚ),(-144211417680917394698615/590295810358705651712:ℚ)⟩ thresholdNode2446 thresholdNode2353
def thresholdNode2448 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode12 thresholdNode182
def thresholdNode2449 : BoxExpr 1 := .add ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode2448 thresholdNode2301
def thresholdNode2450 : BoxExpr 1 := .neg ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode2449
def thresholdNode2451 : BoxExpr 1 := .add ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode51 thresholdNode2450
def thresholdNode2452 : BoxExpr 1 := .mul ⟨(714257930534033838571/590295810358705651712:ℚ),(1521/1024:ℚ)⟩ thresholdNode2352 thresholdNode2352
def thresholdNode2453 : BoxExpr 1 := .inv ⟨(1589646048145469000271/2361183241434822606848:ℚ),(3902782217247640672479/4722366482869645213696:ℚ)⟩ thresholdNode2452
def thresholdNode2454 : BoxExpr 1 := .mul ⟨(-3902782217247640672479/1180591620717411303424:ℚ),(-1589646048145469000271/590295810358705651712:ℚ)⟩ thresholdNode2451 thresholdNode2453
def thresholdNode2455 : BoxExpr 1 := .neg ⟨(1589646048145469000271/590295810358705651712:ℚ),(3902782217247640672479/1180591620717411303424:ℚ)⟩ thresholdNode2454
def thresholdNode2456 : BoxExpr 1 := .mul ⟨(1987898926801569009999335/4722366482869645213696:ℚ),(322282908992817234246557/590295810358705651712:ℚ)⟩ thresholdNode2349 thresholdNode2455
def thresholdNode2457 : BoxExpr 1 := .add ⟨(709661360993437556988205/4722366482869645213696:ℚ),(89035745655949919773971/295147905179352825856:ℚ)⟩ thresholdNode2447 thresholdNode2456
def thresholdNode2458 : BoxExpr 1 := .add ⟨(709661360993437556988205/4722366482869645213696:ℚ),(89035745655949919773971/295147905179352825856:ℚ)⟩ thresholdNode2457 thresholdNode51
def thresholdNode2459 : BoxExpr 1 := .mul ⟨(26844837676325887273867/1180591620717411303424:ℚ),(14514140436017966329723/590295810358705651712:ℚ)⟩ thresholdNode5 thresholdNode2356
def thresholdNode2460 : BoxExpr 1 := .inv ⟨(96030252776757591183/2361183241434822606848:ℚ),(103840938933099602483/2361183241434822606848:ℚ)⟩ thresholdNode2459
def thresholdNode2461 : BoxExpr 1 := .mul ⟨(28862207170624115107987/4722366482869645213696:ℚ),(62650320502218898130209/4722366482869645213696:ℚ)⟩ thresholdNode2458 thresholdNode2460
def thresholdNode2462 : BoxExpr 1 := .add ⟨(28862207170624115107987/4722366482869645213696:ℚ),(62650320502218898130209/4722366482869645213696:ℚ)⟩ thresholdNode2461 thresholdNode51
def thresholdNode2463 : BoxExpr 1 := .mul ⟨(14431103585312057553993/4722366482869645213696:ℚ),(31325160251109449065105/4722366482869645213696:ℚ)⟩ thresholdNode2462 thresholdNode2358
def thresholdNode2464 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode2465 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode2464
def thresholdNode2466 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode2465
def thresholdNode2467 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2466
def thresholdNode2468 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2357 thresholdNode2467
def thresholdNode2469 : BoxExpr 1 := .add ⟨(14431103585312057553993/4722366482869645213696:ℚ),(31325160251109449065105/4722366482869645213696:ℚ)⟩ thresholdNode2463 thresholdNode2468
def thresholdNode2470 : BoxExpr 1 := .add ⟨(14431103585312057553993/4722366482869645213696:ℚ),(31325160251109449065105/4722366482869645213696:ℚ)⟩ thresholdNode2469 thresholdNode51
def thresholdNode2471 : BoxExpr 1 := .mul ⟨(721555179265602877697/4722366482869645213696:ℚ),(428273675308136998937/590295810358705651712:ℚ)⟩ thresholdNode2292 thresholdNode2470
def thresholdNode2472 : BoxExpr 1 := .add ⟨(-64418556289110730261739/4722366482869645213696:ℚ),(-28673517837245573188391/2361183241434822606848:ℚ)⟩ thresholdNode2439 thresholdNode2471
def thresholdNode2473 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode5
def thresholdNode2474 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode12 thresholdNode51
def thresholdNode2475 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2473 thresholdNode2474
def thresholdNode2476 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2474 thresholdNode2301
def thresholdNode2477 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2475 thresholdNode2476
def thresholdNode2478 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2477
def thresholdNode2479 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode2478
def thresholdNode2480 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2479 thresholdNode180
def thresholdNode2481 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2443 thresholdNode51
def thresholdNode2482 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2480 thresholdNode2481
def thresholdNode2483 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2481 thresholdNode2445
def thresholdNode2484 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2482 thresholdNode2483
def thresholdNode2485 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2484 thresholdNode2353
def thresholdNode2486 : BoxExpr 1 := .mul ⟨(-2324068301469329914566719/2361183241434822606848:ℚ),(-3786474146288702876189825/4722366482869645213696:ℚ)⟩ thresholdNode2446 thresholdNode2455
def thresholdNode2487 : BoxExpr 1 := .add ⟨(-2324068301469329914566719/2361183241434822606848:ℚ),(-3786474146288702876189825/4722366482869645213696:ℚ)⟩ thresholdNode2485 thresholdNode2486
def thresholdNode2488 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode182
def thresholdNode2489 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2488 thresholdNode2474
def thresholdNode2490 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2489 thresholdNode2476
def thresholdNode2491 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2490
def thresholdNode2492 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode2491
def thresholdNode2493 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2492 thresholdNode2453
def thresholdNode2494 : BoxExpr 1 := .mul ⟨(-39/8:ℚ),(-649325391394576216883/147573952589676412928:ℚ)⟩ thresholdNode2451 thresholdNode2352
def thresholdNode2495 : BoxExpr 1 := .mul ⟨(-39/8:ℚ),(-649325391394576216883/147573952589676412928:ℚ)⟩ thresholdNode2352 thresholdNode2451
def thresholdNode2496 : BoxExpr 1 := .add ⟨(-39/4:ℚ),(-649325391394576216883/73786976294838206464:ℚ)⟩ thresholdNode2494 thresholdNode2495
def thresholdNode2497 : BoxExpr 1 := .mul ⟨(3457008383784723778681/2361183241434822606848:ℚ),(2313441/1048576:ℚ)⟩ thresholdNode2452 thresholdNode2452
def thresholdNode2498 : BoxExpr 1 := .inv ⟨(1070215353912531397947/2361183241434822606848:ℚ),(806359962241248072827/1180591620717411303424:ℚ)⟩ thresholdNode2497
def thresholdNode2499 : BoxExpr 1 := .mul ⟨(-31448038527408674840253/4722366482869645213696:ℚ),(-18835790228860552603861/4722366482869645213696:ℚ)⟩ thresholdNode2496 thresholdNode2498
def thresholdNode2500 : BoxExpr 1 := .neg ⟨(18835790228860552603861/4722366482869645213696:ℚ),(31448038527408674840253/4722366482869645213696:ℚ)⟩ thresholdNode2499
def thresholdNode2501 : BoxExpr 1 := .mul ⟨(-31448038527408674840253/1180591620717411303424:ℚ),(-18835790228860552603861/1180591620717411303424:ℚ)⟩ thresholdNode2451 thresholdNode2500
def thresholdNode2502 : BoxExpr 1 := .add ⟨(-31448038527408674840253/1180591620717411303424:ℚ),(-18835790228860552603861/1180591620717411303424:ℚ)⟩ thresholdNode2493 thresholdNode2501
def thresholdNode2503 : BoxExpr 1 := .neg ⟨(18835790228860552603861/1180591620717411303424:ℚ),(31448038527408674840253/1180591620717411303424:ℚ)⟩ thresholdNode2502
def thresholdNode2504 : BoxExpr 1 := .mul ⟨(11777353589213871573240519/4722366482869645213696:ℚ),(10387630951008158789774855/2361183241434822606848:ℚ)⟩ thresholdNode2349 thresholdNode2503
def thresholdNode2505 : BoxExpr 1 := .add ⟨(7129216986275211744107081/4722366482869645213696:ℚ),(16988787755727614703359885/4722366482869645213696:ℚ)⟩ thresholdNode2486 thresholdNode2504
def thresholdNode2506 : BoxExpr 1 := .add ⟨(2481080383336551914973643/4722366482869645213696:ℚ),(3300578402359727956792515/1180591620717411303424:ℚ)⟩ thresholdNode2487 thresholdNode2505
def thresholdNode2507 : BoxExpr 1 := .add ⟨(2481080383336551914973643/4722366482869645213696:ℚ),(3300578402359727956792515/1180591620717411303424:ℚ)⟩ thresholdNode2506 thresholdNode51
def thresholdNode2508 : BoxExpr 1 := .mul ⟨(100906516779477374167883/4722366482869645213696:ℚ),(145153986488178587264853/1180591620717411303424:ℚ)⟩ thresholdNode2507 thresholdNode2460
def thresholdNode2509 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode2356
def thresholdNode2510 : BoxExpr 1 := .mul ⟨(28862207170624115107987/2361183241434822606848:ℚ),(62650320502218898130209/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode2461
def thresholdNode2511 : BoxExpr 1 := .add ⟨(28862207170624115107987/2361183241434822606848:ℚ),(62650320502218898130209/2361183241434822606848:ℚ)⟩ thresholdNode2509 thresholdNode2510
def thresholdNode2512 : BoxExpr 1 := .mul ⟨(2441641282970890811791041/4722366482869645213696:ℚ),(2854979065068270242223265/4722366482869645213696:ℚ)⟩ thresholdNode2459 thresholdNode2459
def thresholdNode2513 : BoxExpr 1 := .inv ⟨(7811176436068665965/4722366482869645213696:ℚ),(4566752977611022005/2361183241434822606848:ℚ)⟩ thresholdNode2512
def thresholdNode2514 : BoxExpr 1 := .mul ⟨(95480854085307281229/4722366482869645213696:ℚ),(121171678962083920393/2361183241434822606848:ℚ)⟩ thresholdNode2511 thresholdNode2513
def thresholdNode2515 : BoxExpr 1 := .neg ⟨(-121171678962083920393/2361183241434822606848:ℚ),(-95480854085307281229/4722366482869645213696:ℚ)⟩ thresholdNode2514
def thresholdNode2516 : BoxExpr 1 := .mul ⟨(-36553235172774123795159/2361183241434822606848:ℚ),(-3587135449185837189937/1180591620717411303424:ℚ)⟩ thresholdNode2458 thresholdNode2515
def thresholdNode2517 : BoxExpr 1 := .add ⟨(27800046433929126577565/4722366482869645213696:ℚ),(35391712759748187518729/295147905179352825856:ℚ)⟩ thresholdNode2508 thresholdNode2516
def thresholdNode2518 : BoxExpr 1 := .add ⟨(27800046433929126577565/4722366482869645213696:ℚ),(35391712759748187518729/295147905179352825856:ℚ)⟩ thresholdNode2517 thresholdNode51
def thresholdNode2519 : BoxExpr 1 := .mul ⟨(6950011608482281644391/2361183241434822606848:ℚ),(35391712759748187518729/590295810358705651712:ℚ)⟩ thresholdNode2518 thresholdNode2358
def thresholdNode2520 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2462 thresholdNode2467
def thresholdNode2521 : BoxExpr 1 := .add ⟨(6950011608482281644391/2361183241434822606848:ℚ),(35391712759748187518729/590295810358705651712:ℚ)⟩ thresholdNode2519 thresholdNode2520
def thresholdNode2522 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode5 thresholdNode51
def thresholdNode2523 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2473 thresholdNode2522
def thresholdNode2524 : BoxExpr 1 := .mul ⟨(16/1:ℚ),(16/1:ℚ)⟩ thresholdNode2464 thresholdNode2464
def thresholdNode2525 : BoxExpr 1 := .inv ⟨(1/16:ℚ),(1/16:ℚ)⟩ thresholdNode2524
def thresholdNode2526 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2523 thresholdNode2525
def thresholdNode2527 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2526
def thresholdNode2528 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode51 thresholdNode2527
def thresholdNode2529 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2466 thresholdNode2528
def thresholdNode2530 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2529
def thresholdNode2531 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2357 thresholdNode2530
def thresholdNode2532 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode2520 thresholdNode2531
def thresholdNode2533 : BoxExpr 1 := .add ⟨(6950011608482281644391/2361183241434822606848:ℚ),(35391712759748187518729/590295810358705651712:ℚ)⟩ thresholdNode2521 thresholdNode2532
def thresholdNode2534 : BoxExpr 1 := .add ⟨(6950011608482281644391/2361183241434822606848:ℚ),(35391712759748187518729/590295810358705651712:ℚ)⟩ thresholdNode2533 thresholdNode51
def thresholdNode2535 : BoxExpr 1 := .mul ⟨(216538314103237286875/73786976294838206464:ℚ),(17684796469636672450767/295147905179352825856:ℚ)⟩ thresholdNode2189 thresholdNode2534
def thresholdNode2536 : BoxExpr 1 := .add ⟨(14580007281872789237697/4722366482869645213696:ℚ),(35797866614581481900471/590295810358705651712:ℚ)⟩ thresholdNode2471 thresholdNode2535
def thresholdNode2537 : BoxExpr 1 := .add ⟨(-24919274503618970512021/2361183241434822606848:ℚ),(114517948621080354413493/2361183241434822606848:ℚ)⟩ thresholdNode2472 thresholdNode2536
def thresholdNode2538 : BoxExpr 1 := .neg ⟨(-114517948621080354413493/2361183241434822606848:ℚ),(24919274503618970512021/2361183241434822606848:ℚ)⟩ thresholdNode2537
def thresholdNode2539 : BoxExpr 1 := .add ⟨(-61886883220465179916301/1180591620717411303424:ℚ),(8418128872655635867601/1180591620717411303424:ℚ)⟩ thresholdNode2438 thresholdNode2538
def thresholdCell6Out1 : TaylorCertificate1 :=
  { center := (-51/1280:ℚ), radius := (19/1280:ℚ)
    whole := thresholdNode2363, centerValue := thresholdNode2382, gradient := thresholdNode2422, hessian := thresholdNode2539 }
theorem thresholdCell6Out1_check : thresholdCell6Out1.check = true := by decide +kernel
theorem thresholdCell6Out1_lower_pos : 0 < thresholdCell6Out1.lower := by decide +kernel
theorem thresholdCell6Out1_positive (x : ℝ) (hx : (-(7/128:ℝ)) ≤ x ∧ x ≤ (-(1/40:ℝ))) :
    0 < thresholdNode2363.eval (fun _ => x) := by
  apply thresholdCell6Out1.positive_sound thresholdCell6Out1_check thresholdCell6Out1_lower_pos x
  norm_num [thresholdCell6Out1]
  exact hx
theorem thresholdCell6_public (x : ℝ)
    (hx : (-(7/128:ℝ)) ≤ x ∧ x ≤ (-(1/40:ℝ))) : qc x < fA (43/20) x := by
  have hf := thresholdCell6Out0_positive x hx
  have hg := thresholdCell6Out1_positive x hx
  have hfa : thresholdNode2199.eval (fun _ => x) = thresholdFA 0 x := by
    norm_num [thresholdNode0, thresholdNode1, thresholdNode2179, thresholdNode3, thresholdNode2180, thresholdNode5, thresholdNode2181, thresholdNode2182, thresholdNode2183, thresholdNode9, thresholdNode2184, thresholdNode2185, thresholdNode12, thresholdNode2186, thresholdNode2187, thresholdNode2188, thresholdNode2189, thresholdNode2190, thresholdNode2191, thresholdNode19, thresholdNode2192, thresholdNode2193, thresholdNode22, thresholdNode2194, thresholdNode2195, thresholdNode2196, thresholdNode2197, thresholdNode27, thresholdNode2198, thresholdNode2199, BoxExpr.eval, thresholdFA, ftilde, pow_two, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  have hgap : thresholdNode2363.eval (fun _ => x) =
      (thresholdNode2199.eval (fun _ => x))^2 - (1-x^2)*(thresholdCapacity 1 x+1/4) := by
    norm_num [thresholdNode2345, thresholdNode12, thresholdNode2186, thresholdNode2187, thresholdNode2188, thresholdNode2189, thresholdNode5, thresholdNode2346, thresholdNode2347, thresholdNode2348, thresholdNode180, thresholdNode2349, thresholdNode182, thresholdNode2350, thresholdNode2351, thresholdNode2352, thresholdNode2353, thresholdNode2354, thresholdNode2355, thresholdNode2356, thresholdNode2357, thresholdNode2358, thresholdNode2359, thresholdNode193, thresholdNode2360, thresholdNode2361, thresholdNode2362, thresholdNode2363, BoxExpr.eval, thresholdCapacity, Da, D5, beta5, eta5, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  rw [hfa] at hf
  rw [hgap, hfa] at hg
  refine threshold_positive_to_public 0 1 x ?_ ?_ ?_ hf hg
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdFADomain] <;> constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdCapacityDomain] <;> linarith [hx.1,hx.2]
theorem threshold_fgt_low_domain (x : ℝ)
    (hx : x ∈ Set.Icc (-(1/2:ℝ)) (-(1/40:ℝ))) : qc x < fA (43/20) x := by
  have hlo := hx.1
  by_cases h0 : x ≤ (-(61/160:ℝ))
  · exact thresholdCell0_public x ⟨hlo, h0⟩
  have hlo : (-(61/160:ℝ)) ≤ x := (lt_of_not_ge h0).le
  by_cases h1 : x ≤ (-(21/80:ℝ))
  · exact thresholdCell1_public x ⟨hlo, h1⟩
  have hlo : (-(21/80:ℝ)) ≤ x := (lt_of_not_ge h1).le
  by_cases h2 : x ≤ (-(13/64:ℝ))
  · exact thresholdCell2_public x ⟨hlo, h2⟩
  have hlo : (-(13/64:ℝ)) ≤ x := (lt_of_not_ge h2).le
  by_cases h3 : x ≤ (-(23/160:ℝ))
  · exact thresholdCell3_public x ⟨hlo, h3⟩
  have hlo : (-(23/160:ℝ)) ≤ x := (lt_of_not_ge h3).le
  by_cases h4 : x ≤ (-(27/320:ℝ))
  · exact thresholdCell4_public x ⟨hlo, h4⟩
  have hlo : (-(27/320:ℝ)) ≤ x := (lt_of_not_ge h4).le
  by_cases h5 : x ≤ (-(7/128:ℝ))
  · exact thresholdCell5_public x ⟨hlo, h5⟩
  have hlo : (-(7/128:ℝ)) ≤ x := (lt_of_not_ge h5).le
  exact thresholdCell6_public x ⟨hlo,hx.2⟩
#print axioms threshold_fgt_low_domain
end GaussLocalMaxColoring.Certificate.ThresholdBranch0

open GaussLocalMaxColoring.Main

theorem solution (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (-(1/2):ℝ) (-(1/40):ℝ)) : qc ρ < fA (43/20) ρ  := by exact GaussLocalMaxColoring.Certificate.ThresholdBranch0.threshold_fgt_low_domain ρ hρ

#print axioms solution
