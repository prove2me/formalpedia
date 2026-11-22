-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_61_branch_1
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T09:47:57.826336+00:00
-- url     : https://prove2.me/submissions/447badc9-fa2f-4d74-894f-db1e7623eb16

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
namespace GaussLocalMaxColoring.Certificate.ThresholdBranch1
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
def thresholdNode14 : BoxExpr 1 := .mul ⟨(967100340934050235/2361183241434822606848:ℚ),(2951479051793528259/4722366482869645213696:ℚ)⟩ thresholdNode13 thresholdNode13
def thresholdNode15 : BoxExpr 1 := .neg ⟨(-2951479051793528259/4722366482869645213696:ℚ),(-967100340934050235/2361183241434822606848:ℚ)⟩ thresholdNode14
def thresholdNode16 : BoxExpr 1 := .add ⟨(4719415003817851685437/4722366482869645213696:ℚ),(2360216141093888556613/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode15
def thresholdNode17 : BoxExpr 1 := .sqrt ⟨(4720890512687361774341/4722366482869645213696:ℚ),(4721399283481479244671/4722366482869645213696:ℚ)⟩ thresholdNode16
def thresholdNode18 : BoxExpr 1 := .mul ⟨(383476461067309182129/147573952589676412928:ℚ),(767035576719848942165/295147905179352825856:ℚ)⟩ thresholdNode11 thresholdNode17
def thresholdNode19 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode20 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode19 thresholdNode3
def thresholdNode21 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode22 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode21
def thresholdNode23 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode22 thresholdNode22
def thresholdNode24 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode23 thresholdNode9
def thresholdNode25 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode20 thresholdNode24
def thresholdNode26 : BoxExpr 1 := .var 0
def thresholdNode27 : BoxExpr 1 := .mul ⟨(2416069756009716299/4722366482869645213696:ℚ),(604017439002429075/1180591620717411303424:ℚ)⟩ thresholdNode26 thresholdNode26
def thresholdNode28 : BoxExpr 1 := .neg ⟨(-604017439002429075/1180591620717411303424:ℚ),(-2416069756009716299/4722366482869645213696:ℚ)⟩ thresholdNode27
def thresholdNode29 : BoxExpr 1 := .add ⟨(1179987603278408874349/1180591620717411303424:ℚ),(4719950413113635497397/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode28
def thresholdNode30 : BoxExpr 1 := .sqrt ⟨(590144786679699155775/590295810358705651712:ℚ),(2360579146718796623101/2361183241434822606848:ℚ)⟩ thresholdNode29
def thresholdNode31 : BoxExpr 1 := .mul ⟨(12271942810047008004505/4722366482869645213696:ℚ),(1533992851255876000565/590295810358705651712:ℚ)⟩ thresholdNode25 thresholdNode30
def thresholdNode32 : BoxExpr 1 := .lit (0/1:ℚ)
def thresholdNode33 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode1
def thresholdNode34 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode32
def thresholdNode35 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode33 thresholdNode34
def thresholdNode36 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode35 thresholdNode32
def thresholdNode37 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32
def thresholdNode38 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode37
def thresholdNode39 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode38 thresholdNode22
def thresholdNode40 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode22 thresholdNode38
def thresholdNode41 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode39 thresholdNode40
def thresholdNode42 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode41 thresholdNode9
def thresholdNode43 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode23 thresholdNode32
def thresholdNode44 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode42 thresholdNode43
def thresholdNode45 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode36 thresholdNode44
def thresholdNode46 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode45 thresholdNode30
def thresholdNode47 : BoxExpr 1 := .mul ⟨(-53407786969821464925/2361183241434822606848:ℚ),(-106815573939642929849/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode26
def thresholdNode48 : BoxExpr 1 := .mul ⟨(-53407786969821464925/2361183241434822606848:ℚ),(-106815573939642929849/4722366482869645213696:ℚ)⟩ thresholdNode26 thresholdNode12
def thresholdNode49 : BoxExpr 1 := .add ⟨(-53407786969821464925/1180591620717411303424:ℚ),(-106815573939642929849/2361183241434822606848:ℚ)⟩ thresholdNode47 thresholdNode48
def thresholdNode50 : BoxExpr 1 := .neg ⟨(106815573939642929849/2361183241434822606848:ℚ),(53407786969821464925/1180591620717411303424:ℚ)⟩ thresholdNode49
def thresholdNode51 : BoxExpr 1 := .add ⟨(106815573939642929849/2361183241434822606848:ℚ),(53407786969821464925/1180591620717411303424:ℚ)⟩ thresholdNode32 thresholdNode50
def thresholdNode52 : BoxExpr 1 := .mul ⟨(590144786679699155775/295147905179352825856:ℚ),(2360579146718796623101/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode30
def thresholdNode53 : BoxExpr 1 := .inv ⟨(2361787490744447554547/4722366482869645213696:ℚ),(2361787490744447554549/4722366482869645213696:ℚ)⟩ thresholdNode52
def thresholdNode54 : BoxExpr 1 := .mul ⟨(106842909063693277055/4722366482869645213696:ℚ),(53421454531846638529/2361183241434822606848:ℚ)⟩ thresholdNode51 thresholdNode53
def thresholdNode55 : BoxExpr 1 := .mul ⟨(8678816114834722491/147573952589676412928:ℚ),(277722115674711119721/4722366482869645213696:ℚ)⟩ thresholdNode25 thresholdNode54
def thresholdNode56 : BoxExpr 1 := .add ⟨(8678816114834722491/147573952589676412928:ℚ),(277722115674711119721/4722366482869645213696:ℚ)⟩ thresholdNode46 thresholdNode55
def thresholdNode57 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode1
def thresholdNode58 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode32
def thresholdNode59 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode57 thresholdNode58
def thresholdNode60 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode32
def thresholdNode61 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode58 thresholdNode60
def thresholdNode62 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode59 thresholdNode61
def thresholdNode63 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode62 thresholdNode32
def thresholdNode64 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32
def thresholdNode65 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode64
def thresholdNode66 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode65 thresholdNode7
def thresholdNode67 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode65 thresholdNode65
def thresholdNode68 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66 thresholdNode67
def thresholdNode69 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode7 thresholdNode65
def thresholdNode70 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode67 thresholdNode69
def thresholdNode71 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode68 thresholdNode70
def thresholdNode72 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode71 thresholdNode9
def thresholdNode73 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode66 thresholdNode69
def thresholdNode74 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode73 thresholdNode32
def thresholdNode75 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode72 thresholdNode74
def thresholdNode76 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode8 thresholdNode32
def thresholdNode77 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode74 thresholdNode76
def thresholdNode78 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode75 thresholdNode77
def thresholdNode79 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode63 thresholdNode78
def thresholdNode80 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode79 thresholdNode17
def thresholdNode81 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode57 thresholdNode60
def thresholdNode82 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode81 thresholdNode32
def thresholdNode83 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode73 thresholdNode9
def thresholdNode84 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode83 thresholdNode76
def thresholdNode85 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode82 thresholdNode84
def thresholdNode86 : BoxExpr 1 := .mul ⟨(-118059162071741130343/4722366482869645213696:ℚ),(-23892996451886182339/1180591620717411303424:ℚ)⟩ thresholdNode12 thresholdNode13
def thresholdNode87 : BoxExpr 1 := .mul ⟨(-118059162071741130343/4722366482869645213696:ℚ),(-23892996451886182339/1180591620717411303424:ℚ)⟩ thresholdNode13 thresholdNode12
def thresholdNode88 : BoxExpr 1 := .add ⟨(-118059162071741130343/2361183241434822606848:ℚ),(-23892996451886182339/590295810358705651712:ℚ)⟩ thresholdNode86 thresholdNode87
def thresholdNode89 : BoxExpr 1 := .neg ⟨(23892996451886182339/590295810358705651712:ℚ),(118059162071741130343/2361183241434822606848:ℚ)⟩ thresholdNode88
def thresholdNode90 : BoxExpr 1 := .add ⟨(23892996451886182339/590295810358705651712:ℚ),(118059162071741130343/2361183241434822606848:ℚ)⟩ thresholdNode32 thresholdNode89
def thresholdNode91 : BoxExpr 1 := .mul ⟨(4720890512687361774341/2361183241434822606848:ℚ),(4721399283481479244671/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode17
def thresholdNode92 : BoxExpr 1 := .inv ⟨(590416735049106942701/1180591620717411303424:ℚ),(2361921457254464927751/4722366482869645213696:ℚ)⟩ thresholdNode91
def thresholdNode93 : BoxExpr 1 := .mul ⟨(95591564148762823147/4722366482869645213696:ℚ),(118096072862723246389/4722366482869645213696:ℚ)⟩ thresholdNode90 thresholdNode92
def thresholdNode94 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode85 thresholdNode93
def thresholdNode95 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode80 thresholdNode94
def thresholdNode96 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode13
def thresholdNode97 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode12
def thresholdNode98 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode96 thresholdNode97
def thresholdNode99 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode13 thresholdNode32
def thresholdNode100 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode97 thresholdNode99
def thresholdNode101 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode98 thresholdNode100
def thresholdNode102 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode101
def thresholdNode103 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode32 thresholdNode102
def thresholdNode104 : BoxExpr 1 := .mul ⟨(-2361921457254464927751/2361183241434822606848:ℚ),(-590416735049106942701/590295810358705651712:ℚ)⟩ thresholdNode103 thresholdNode92
def thresholdNode105 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode17
def thresholdNode106 : BoxExpr 1 := .mul ⟨(95591564148762823147/2361183241434822606848:ℚ),(118096072862723246389/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode93
def thresholdNode107 : BoxExpr 1 := .add ⟨(95591564148762823147/2361183241434822606848:ℚ),(118096072862723246389/2361183241434822606848:ℚ)⟩ thresholdNode105 thresholdNode106
def thresholdNode108 : BoxExpr 1 := .mul ⟨(9438830007635703370873/2361183241434822606848:ℚ),(4720432282187777113227/1180591620717411303424:ℚ)⟩ thresholdNode91 thresholdNode91
def thresholdNode109 : BoxExpr 1 := .inv ⟨(1181075369022924765703/4722366482869645213696:ℚ),(1181329951937372161025/4722366482869645213696:ℚ)⟩ thresholdNode108
def thresholdNode110 : BoxExpr 1 := .mul ⟨(2988460402004634013/295147905179352825856:ℚ),(14771241133548873845/1180591620717411303424:ℚ)⟩ thresholdNode107 thresholdNode109
def thresholdNode111 : BoxExpr 1 := .neg ⟨(-14771241133548873845/1180591620717411303424:ℚ),(-2988460402004634013/295147905179352825856:ℚ)⟩ thresholdNode110
def thresholdNode112 : BoxExpr 1 := .mul ⟨(-1477124113354887385/2361183241434822606848:ℚ),(-1935389613917384913/4722366482869645213696:ℚ)⟩ thresholdNode90 thresholdNode111
def thresholdNode113 : BoxExpr 1 := .add ⟨(-73856205667744369223/73786976294838206464:ℚ),(-4725269270006772926521/4722366482869645213696:ℚ)⟩ thresholdNode104 thresholdNode112
def thresholdNode114 : BoxExpr 1 := .mul ⟨(-1535825025619610609119/590295810358705651712:ℚ),(-12282628676992105206547/4722366482869645213696:ℚ)⟩ thresholdNode11 thresholdNode113
def thresholdNode115 : BoxExpr 1 := .add ⟨(-1535825025619610609119/590295810358705651712:ℚ),(-12282628676992105206547/4722366482869645213696:ℚ)⟩ thresholdNode94 thresholdNode114
def thresholdNode116 : BoxExpr 1 := .add ⟨(-1535825025619610609119/590295810358705651712:ℚ),(-12282628676992105206547/4722366482869645213696:ℚ)⟩ thresholdNode95 thresholdNode115
def thresholdCell0Out0 : TaylorCertificate1 :=
  { center := (-6956533366137/307551593775760:ℚ), radius := (732256478257/307551593775760:ℚ)
    whole := thresholdNode18, centerValue := thresholdNode31, gradient := thresholdNode56, hessian := thresholdNode116 }
theorem thresholdCell0Out0_check : thresholdCell0Out0.check = true := by decide +kernel
theorem thresholdCell0Out0_lower_pos : 0 < thresholdCell0Out0.lower := by decide +kernel
theorem thresholdCell0Out0_positive (x : ℝ) (hx : (-(1/40:ℝ)) ≤ x ∧ x ≤ (-(155606922197/7688789844394:ℝ))) :
    0 < thresholdNode18.eval (fun _ => x) := by
  apply thresholdCell0Out0.positive_sound thresholdCell0Out0_check thresholdCell0Out0_lower_pos x
  norm_num [thresholdCell0Out0]
  exact hx
def thresholdNode117 : BoxExpr 1 := .mul ⟨(31887295797048612167869/4722366482869645213696:ℚ),(15947084580429108911565/2361183241434822606848:ℚ)⟩ thresholdNode18 thresholdNode18
def thresholdNode118 : BoxExpr 1 := .mul ⟨(-118059162071741130343/2361183241434822606848:ℚ),(-23892996451886182339/590295810358705651712:ℚ)⟩ thresholdNode13 thresholdNode5
def thresholdNode119 : BoxExpr 1 := .neg ⟨(23892996451886182339/590295810358705651712:ℚ),(118059162071741130343/2361183241434822606848:ℚ)⟩ thresholdNode118
def thresholdNode120 : BoxExpr 1 := .add ⟨(614188806810591834051/590295810358705651712:ℚ),(2479242403506563737191/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode119
def thresholdNode121 : BoxExpr 1 := .lit (7033791386230630914920427/47247072600500000000000:ℚ)
def thresholdNode122 : BoxExpr 1 := .mul ⟨(365743374231223119679975/2361183241434822606848:ℚ),(46136387140887244632117/295147905179352825856:ℚ)⟩ thresholdNode120 thresholdNode121
def thresholdNode123 : BoxExpr 1 := .lit (4/1:ℚ)
def thresholdNode124 : BoxExpr 1 := .mul ⟨(-118059162071741130343/1180591620717411303424:ℚ),(-23892996451886182339/295147905179352825856:ℚ)⟩ thresholdNode13 thresholdNode123
def thresholdNode125 : BoxExpr 1 := .neg ⟨(23892996451886182339/295147905179352825856:ℚ),(118059162071741130343/1180591620717411303424:ℚ)⟩ thresholdNode124
def thresholdNode126 : BoxExpr 1 := .add ⟨(319040901631239008195/295147905179352825856:ℚ),(1298650782789152433767/1180591620717411303424:ℚ)⟩ thresholdNode12 thresholdNode125
def thresholdNode127 : BoxExpr 1 := .inv ⟨(4293060438972404739721/4722366482869645213696:ℚ),(4368708111661410368345/4722366482869645213696:ℚ)⟩ thresholdNode126
def thresholdNode128 : BoxExpr 1 := .mul ⟨(664987953147678399417727/4722366482869645213696:ℚ),(682899675749571400657243/4722366482869645213696:ℚ)⟩ thresholdNode122 thresholdNode127
def thresholdNode129 : BoxExpr 1 := .add ⟨(669710319630548044631423/4722366482869645213696:ℚ),(687622042232441045870939/4722366482869645213696:ℚ)⟩ thresholdNode128 thresholdNode12
def thresholdNode130 : BoxExpr 1 := .sqrt ⟨(56237154681360054413813/4722366482869645213696:ℚ),(28492118581815108971041/2361183241434822606848:ℚ)⟩ thresholdNode129
def thresholdNode131 : BoxExpr 1 := .add ⟨(60959521164229699627509/4722366482869645213696:ℚ),(30853301823249931577889/2361183241434822606848:ℚ)⟩ thresholdNode130 thresholdNode12
def thresholdNode132 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode133 : BoxExpr 1 := .mul ⟨(15239880291057424906877/2361183241434822606848:ℚ),(30853301823249931577889/4722366482869645213696:ℚ)⟩ thresholdNode131 thresholdNode132
def thresholdNode134 : BoxExpr 1 := .lit (1/4:ℚ)
def thresholdNode135 : BoxExpr 1 := .add ⟨(15830176101416130558589/2361183241434822606848:ℚ),(32033893443967342881313/4722366482869645213696:ℚ)⟩ thresholdNode133 thresholdNode134
def thresholdNode136 : BoxExpr 1 := .mul ⟨(3955070560338186369247/590295810358705651712:ℚ),(8005193227039559295929/1180591620717411303424:ℚ)⟩ thresholdNode16 thresholdNode135
def thresholdNode137 : BoxExpr 1 := .neg ⟨(-8005193227039559295929/1180591620717411303424:ℚ),(-3955070560338186369247/590295810358705651712:ℚ)⟩ thresholdNode136
def thresholdNode138 : BoxExpr 1 := .add ⟨(-133477111109625015847/4722366482869645213696:ℚ),(126802339076363434577/2361183241434822606848:ℚ)⟩ thresholdNode117 thresholdNode137
def thresholdNode139 : BoxExpr 1 := .mul ⟨(31890913354430901414889/4722366482869645213696:ℚ),(3986364169303862676871/590295810358705651712:ℚ)⟩ thresholdNode31 thresholdNode31
def thresholdNode140 : BoxExpr 1 := .mul ⟨(-53407786969821464925/1180591620717411303424:ℚ),(-106815573939642929849/2361183241434822606848:ℚ)⟩ thresholdNode26 thresholdNode5
def thresholdNode141 : BoxExpr 1 := .neg ⟨(106815573939642929849/2361183241434822606848:ℚ),(53407786969821464925/1180591620717411303424:ℚ)⟩ thresholdNode140
def thresholdNode142 : BoxExpr 1 := .add ⟨(2467998815374465536697/2361183241434822606848:ℚ),(1233999407687232768349/1180591620717411303424:ℚ)⟩ thresholdNode12 thresholdNode141
def thresholdNode143 : BoxExpr 1 := .mul ⟨(734834471358321076736761/4722366482869645213696:ℚ),(734834471358321076737061/4722366482869645213696:ℚ)⟩ thresholdNode142 thresholdNode121
def thresholdNode144 : BoxExpr 1 := .mul ⟨(-53407786969821464925/590295810358705651712:ℚ),(-106815573939642929849/1180591620717411303424:ℚ)⟩ thresholdNode26 thresholdNode123
def thresholdNode145 : BoxExpr 1 := .neg ⟨(106815573939642929849/1180591620717411303424:ℚ),(53407786969821464925/590295810358705651712:ℚ)⟩ thresholdNode144
def thresholdNode146 : BoxExpr 1 := .add ⟨(1287407194657054233273/1180591620717411303424:ℚ),(643703597328527116637/590295810358705651712:ℚ)⟩ thresholdNode12 thresholdNode145
def thresholdNode147 : BoxExpr 1 := .inv ⟨(2165276970165527514703/2361183241434822606848:ℚ),(4330553940331055029411/4722366482869645213696:ℚ)⟩ thresholdNode146
def thresholdNode148 : BoxExpr 1 := .mul ⟨(5264574986819740423639/36893488147419103232:ℚ),(673865598312926774226847/4722366482869645213696:ℚ)⟩ thresholdNode143 thresholdNode147
def thresholdNode149 : BoxExpr 1 := .add ⟨(5301468474967159526871/36893488147419103232:ℚ),(678587964795796419440543/4722366482869645213696:ℚ)⟩ thresholdNode148 thresholdNode12
def thresholdNode150 : BoxExpr 1 := .sqrt ⟨(1769020810935210807323/147573952589676412928:ℚ),(56608665949926745834381/4722366482869645213696:ℚ)⟩ thresholdNode149
def thresholdNode151 : BoxExpr 1 := .add ⟨(1916594763524887220251/147573952589676412928:ℚ),(61331032432796391048077/4722366482869645213696:ℚ)⟩ thresholdNode150 thresholdNode12
def thresholdNode152 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode153 : BoxExpr 1 := .mul ⟨(1916594763524887220251/295147905179352825856:ℚ),(30665516216398195524039/4722366482869645213696:ℚ)⟩ thresholdNode151 thresholdNode152
def thresholdNode154 : BoxExpr 1 := .add ⟨(1990381739819725426715/295147905179352825856:ℚ),(31846107837115606827463/4722366482869645213696:ℚ)⟩ thresholdNode153 thresholdNode134
def thresholdNode155 : BoxExpr 1 := .mul ⟨(15914907323172736714983/2361183241434822606848:ℚ),(7957453661586368357499/1180591620717411303424:ℚ)⟩ thresholdNode29 thresholdNode154
def thresholdNode156 : BoxExpr 1 := .neg ⟨(-7957453661586368357499/1180591620717411303424:ℚ),(-15914907323172736714983/2361183241434822606848:ℚ)⟩ thresholdNode155
def thresholdNode157 : BoxExpr 1 := .add ⟨(61098708085427984893/4722366482869645213696:ℚ),(30549354042713992501/2361183241434822606848:ℚ)⟩ thresholdNode139 thresholdNode156
def thresholdNode158 : BoxExpr 1 := .mul ⟨(721712288321650202165/4722366482869645213696:ℚ),(721712288321650202191/4722366482869645213696:ℚ)⟩ thresholdNode56 thresholdNode31
def thresholdNode159 : BoxExpr 1 := .mul ⟨(721712288321650202165/4722366482869645213696:ℚ),(721712288321650202191/4722366482869645213696:ℚ)⟩ thresholdNode31 thresholdNode56
def thresholdNode160 : BoxExpr 1 := .add ⟨(721712288321650202165/2361183241434822606848:ℚ),(721712288321650202191/2361183241434822606848:ℚ)⟩ thresholdNode158 thresholdNode159
def thresholdNode161 : BoxExpr 1 := .mul ⟨(1440659168958938544085/4722366482869645213696:ℚ),(1440659168958938544101/4722366482869645213696:ℚ)⟩ thresholdNode51 thresholdNode154
def thresholdNode162 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode163 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode26 thresholdNode32
def thresholdNode164 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode162 thresholdNode163
def thresholdNode165 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode164
def thresholdNode166 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode32 thresholdNode165
def thresholdNode167 : BoxExpr 1 := .mul ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode166 thresholdNode121
def thresholdNode168 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode142 thresholdNode32
def thresholdNode169 : BoxExpr 1 := .add ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode167 thresholdNode168
def thresholdNode170 : BoxExpr 1 := .mul ⟨(-10073445866115332020267/36893488147419103232:ℚ),(-1289401070862762498592685/4722366482869645213696:ℚ)⟩ thresholdNode169 thresholdNode147
def thresholdNode171 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode12 thresholdNode123
def thresholdNode172 : BoxExpr 1 := .add ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode171 thresholdNode163
def thresholdNode173 : BoxExpr 1 := .neg ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode172
def thresholdNode174 : BoxExpr 1 := .add ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode32 thresholdNode173
def thresholdNode175 : BoxExpr 1 := .mul ⟨(1403887047620736028319/1180591620717411303424:ℚ),(2807774095241472056643/2361183241434822606848:ℚ)⟩ thresholdNode146 thresholdNode146
def thresholdNode176 : BoxExpr 1 := .inv ⟨(1985624950768406759875/2361183241434822606848:ℚ),(1985624950768406759879/2361183241434822606848:ℚ)⟩ thresholdNode175
def thresholdNode177 : BoxExpr 1 := .mul ⟨(-1985624950768406759879/590295810358705651712:ℚ),(-1985624950768406759875/590295810358705651712:ℚ)⟩ thresholdNode174 thresholdNode176
def thresholdNode178 : BoxExpr 1 := .neg ⟨(1985624950768406759875/590295810358705651712:ℚ),(1985624950768406759879/590295810358705651712:ℚ)⟩ thresholdNode177
def thresholdNode179 : BoxExpr 1 := .mul ⟨(2471821136807896846610023/4722366482869645213696:ℚ),(2471821136807896846616013/4722366482869645213696:ℚ)⟩ thresholdNode143 thresholdNode178
def thresholdNode180 : BoxExpr 1 := .add ⟨(1182420065945134348015847/4722366482869645213696:ℚ),(36950627060785448375729/147573952589676412928:ℚ)⟩ thresholdNode170 thresholdNode179
def thresholdNode181 : BoxExpr 1 := .add ⟨(1182420065945134348015847/4722366482869645213696:ℚ),(36950627060785448375729/147573952589676412928:ℚ)⟩ thresholdNode180 thresholdNode32
def thresholdNode182 : BoxExpr 1 := .mul ⟨(1769020810935210807323/73786976294838206464:ℚ),(56608665949926745834381/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode150
def thresholdNode183 : BoxExpr 1 := .inv ⟨(196972891202353809497/4722366482869645213696:ℚ),(98486445601176904749/2361183241434822606848:ℚ)⟩ thresholdNode182
def thresholdNode184 : BoxExpr 1 := .mul ⟨(24659744203436063144453/2361183241434822606848:ℚ),(49319488406872126289469/4722366482869645213696:ℚ)⟩ thresholdNode181 thresholdNode183
def thresholdNode185 : BoxExpr 1 := .add ⟨(24659744203436063144453/2361183241434822606848:ℚ),(49319488406872126289469/4722366482869645213696:ℚ)⟩ thresholdNode184 thresholdNode32
def thresholdNode186 : BoxExpr 1 := .mul ⟨(24659744203436063144453/4722366482869645213696:ℚ),(24659744203436063144735/4722366482869645213696:ℚ)⟩ thresholdNode185 thresholdNode152
def thresholdNode187 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode188 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode187
def thresholdNode189 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode188
def thresholdNode190 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode189
def thresholdNode191 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode151 thresholdNode190
def thresholdNode192 : BoxExpr 1 := .add ⟨(24659744203436063144453/4722366482869645213696:ℚ),(24659744203436063144735/4722366482869645213696:ℚ)⟩ thresholdNode186 thresholdNode191
def thresholdNode193 : BoxExpr 1 := .add ⟨(24659744203436063144453/4722366482869645213696:ℚ),(24659744203436063144735/4722366482869645213696:ℚ)⟩ thresholdNode192 thresholdNode32
def thresholdNode194 : BoxExpr 1 := .mul ⟨(24647127719226931422979/4722366482869645213696:ℚ),(24647127719226931423267/4722366482869645213696:ℚ)⟩ thresholdNode29 thresholdNode193
def thresholdNode195 : BoxExpr 1 := .add ⟨(3260973361023233745883/590295810358705651712:ℚ),(3260973361023233745921/590295810358705651712:ℚ)⟩ thresholdNode161 thresholdNode194
def thresholdNode196 : BoxExpr 1 := .neg ⟨(-3260973361023233745921/590295810358705651712:ℚ),(-3260973361023233745883/590295810358705651712:ℚ)⟩ thresholdNode195
def thresholdNode197 : BoxExpr 1 := .add ⟨(-12322181155771284781519/2361183241434822606848:ℚ),(-12322181155771284781341/2361183241434822606848:ℚ)⟩ thresholdNode160 thresholdNode196
def thresholdNode198 : BoxExpr 1 := .mul ⟨(-1995664569516525351073/295147905179352825856:ℚ),(-15958436075616351448555/2361183241434822606848:ℚ)⟩ thresholdNode116 thresholdNode18
def thresholdNode199 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode85 thresholdNode17
def thresholdNode200 : BoxExpr 1 := .mul ⟨(248475932270086644347/4722366482869645213696:ℚ),(153486513497859835251/2361183241434822606848:ℚ)⟩ thresholdNode11 thresholdNode93
def thresholdNode201 : BoxExpr 1 := .add ⟨(248475932270086644347/4722366482869645213696:ℚ),(153486513497859835251/2361183241434822606848:ℚ)⟩ thresholdNode199 thresholdNode200
def thresholdNode202 : BoxExpr 1 := .mul ⟨(3268503680382028591/1180591620717411303424:ℚ),(9977247598713740231/2361183241434822606848:ℚ)⟩ thresholdNode201 thresholdNode201
def thresholdNode203 : BoxExpr 1 := .add ⟨(-7979389774385719375701/1180591620717411303424:ℚ),(-3987114707004409427081/590295810358705651712:ℚ)⟩ thresholdNode198 thresholdNode202
def thresholdNode204 : BoxExpr 1 := .mul ⟨(-1995664569516525351073/295147905179352825856:ℚ),(-15958436075616351448555/2361183241434822606848:ℚ)⟩ thresholdNode18 thresholdNode116
def thresholdNode205 : BoxExpr 1 := .add ⟨(-7979389774385719375701/1180591620717411303424:ℚ),(-3987114707004409427081/590295810358705651712:ℚ)⟩ thresholdNode202 thresholdNode204
def thresholdNode206 : BoxExpr 1 := .add ⟨(-7979389774385719375701/590295810358705651712:ℚ),(-3987114707004409427081/295147905179352825856:ℚ)⟩ thresholdNode203 thresholdNode205
def thresholdNode207 : BoxExpr 1 := .mul ⟨(-32033893443967342881313/2361183241434822606848:ℚ),(-15830176101416130558589/1180591620717411303424:ℚ)⟩ thresholdNode103 thresholdNode135
def thresholdNode208 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode209 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode208 thresholdNode99
def thresholdNode210 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode209
def thresholdNode211 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode32 thresholdNode210
def thresholdNode212 : BoxExpr 1 := .mul ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode211 thresholdNode121
def thresholdNode213 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode120 thresholdNode32
def thresholdNode214 : BoxExpr 1 := .add ⟨(-351515330597236149577949/1180591620717411303424:ℚ),(-703030661194472299155897/2361183241434822606848:ℚ)⟩ thresholdNode212 thresholdNode213
def thresholdNode215 : BoxExpr 1 := .mul ⟨(-1300761287142040763156337/4722366482869645213696:ℚ),(-79889847863008215813121/295147905179352825856:ℚ)⟩ thresholdNode214 thresholdNode127
def thresholdNode216 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode12 thresholdNode123
def thresholdNode217 : BoxExpr 1 := .add ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode216 thresholdNode99
def thresholdNode218 : BoxExpr 1 := .neg ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode217
def thresholdNode219 : BoxExpr 1 := .add ⟨(-4/1:ℚ),(-4/1:ℚ)⟩ thresholdNode32 thresholdNode218
def thresholdNode220 : BoxExpr 1 := .mul ⟨(5517889580239892656077/4722366482869645213696:ℚ),(2857031722136135354289/2361183241434822606848:ℚ)⟩ thresholdNode126 thresholdNode126
def thresholdNode221 : BoxExpr 1 := .inv ⟨(487847777155955084059/590295810358705651712:ℚ),(1010383810433240334875/1180591620717411303424:ℚ)⟩ thresholdNode220
def thresholdNode222 : BoxExpr 1 := .mul ⟨(-1010383810433240334875/295147905179352825856:ℚ),(-487847777155955084059/147573952589676412928:ℚ)⟩ thresholdNode219 thresholdNode221
def thresholdNode223 : BoxExpr 1 := .neg ⟨(487847777155955084059/147573952589676412928:ℚ),(1010383810433240334875/295147905179352825856:ℚ)⟩ thresholdNode222
def thresholdNode224 : BoxExpr 1 := .mul ⟨(1209069005723051635304453/2361183241434822606848:ℚ),(2527029076392377141741889/4722366482869645213696:ℚ)⟩ thresholdNode122 thresholdNode223
def thresholdNode225 : BoxExpr 1 := .add ⟨(1117376724304062507452569/4722366482869645213696:ℚ),(1248791510584245688731953/4722366482869645213696:ℚ)⟩ thresholdNode215 thresholdNode224
def thresholdNode226 : BoxExpr 1 := .add ⟨(1117376724304062507452569/4722366482869645213696:ℚ),(1248791510584245688731953/4722366482869645213696:ℚ)⟩ thresholdNode225 thresholdNode32
def thresholdNode227 : BoxExpr 1 := .mul ⟨(56237154681360054413813/2361183241434822606848:ℚ),(28492118581815108971041/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode130
def thresholdNode228 : BoxExpr 1 := .inv ⟨(97837341993778212597/2361183241434822606848:ℚ),(99137062165070119199/2361183241434822606848:ℚ)⟩ thresholdNode227
def thresholdNode229 : BoxExpr 1 := .mul ⟨(46299315865545822702795/4722366482869645213696:ℚ),(26215991932242325420547/2361183241434822606848:ℚ)⟩ thresholdNode226 thresholdNode228
def thresholdNode230 : BoxExpr 1 := .add ⟨(46299315865545822702795/4722366482869645213696:ℚ),(26215991932242325420547/2361183241434822606848:ℚ)⟩ thresholdNode229 thresholdNode32
def thresholdNode231 : BoxExpr 1 := .mul ⟨(23149657932772911351397/4722366482869645213696:ℚ),(26215991932242325420547/4722366482869645213696:ℚ)⟩ thresholdNode230 thresholdNode132
def thresholdNode232 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode233 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode232
def thresholdNode234 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode233
def thresholdNode235 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode234
def thresholdNode236 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode131 thresholdNode235
def thresholdNode237 : BoxExpr 1 := .add ⟨(23149657932772911351397/4722366482869645213696:ℚ),(26215991932242325420547/4722366482869645213696:ℚ)⟩ thresholdNode231 thresholdNode236
def thresholdNode238 : BoxExpr 1 := .add ⟨(23149657932772911351397/4722366482869645213696:ℚ),(26215991932242325420547/4722366482869645213696:ℚ)⟩ thresholdNode237 thresholdNode32
def thresholdNode239 : BoxExpr 1 := .mul ⟨(234253185074280901575/1180591620717411303424:ℚ),(1310799596612116271035/4722366482869645213696:ℚ)⟩ thresholdNode90 thresholdNode238
def thresholdNode240 : BoxExpr 1 := .add ⟨(-31565387073818781078163/2361183241434822606848:ℚ),(-62009904809052405963321/4722366482869645213696:ℚ)⟩ thresholdNode207 thresholdNode239
def thresholdNode241 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode5
def thresholdNode242 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode12 thresholdNode32
def thresholdNode243 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode241 thresholdNode242
def thresholdNode244 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode242 thresholdNode99
def thresholdNode245 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode243 thresholdNode244
def thresholdNode246 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode245
def thresholdNode247 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode246
def thresholdNode248 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode247 thresholdNode121
def thresholdNode249 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode211 thresholdNode32
def thresholdNode250 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode248 thresholdNode249
def thresholdNode251 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode249 thresholdNode213
def thresholdNode252 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode250 thresholdNode251
def thresholdNode253 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode252 thresholdNode127
def thresholdNode254 : BoxExpr 1 := .mul ⟨(-2406694358468930611182167/2361183241434822606848:ℚ),(-2324068301469329914562547/2361183241434822606848:ℚ)⟩ thresholdNode214 thresholdNode223
def thresholdNode255 : BoxExpr 1 := .add ⟨(-2406694358468930611182167/2361183241434822606848:ℚ),(-2324068301469329914562547/2361183241434822606848:ℚ)⟩ thresholdNode253 thresholdNode254
def thresholdNode256 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode123
def thresholdNode257 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode256 thresholdNode242
def thresholdNode258 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode257 thresholdNode244
def thresholdNode259 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode258
def thresholdNode260 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode259
def thresholdNode261 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode260 thresholdNode221
def thresholdNode262 : BoxExpr 1 := .mul ⟨(-1298650782789152433767/295147905179352825856:ℚ),(-319040901631239008195/73786976294838206464:ℚ)⟩ thresholdNode219 thresholdNode126
def thresholdNode263 : BoxExpr 1 := .mul ⟨(-1298650782789152433767/295147905179352825856:ℚ),(-319040901631239008195/73786976294838206464:ℚ)⟩ thresholdNode126 thresholdNode219
def thresholdNode264 : BoxExpr 1 := .add ⟨(-1298650782789152433767/147573952589676412928:ℚ),(-319040901631239008195/36893488147419103232:ℚ)⟩ thresholdNode262 thresholdNode263
def thresholdNode265 : BoxExpr 1 := .mul ⟨(6447425359756948692033/4722366482869645213696:ℚ),(6914016767569447557387/4722366482869645213696:ℚ)⟩ thresholdNode220 thresholdNode220
def thresholdNode266 : BoxExpr 1 := .inv ⟨(3225439848964992291295/4722366482869645213696:ℚ),(3458860545749893523585/4722366482869645213696:ℚ)⟩ thresholdNode265
def thresholdNode267 : BoxExpr 1 := .mul ⟨(-30437972802599063007563/4722366482869645213696:ℚ),(-6973095316030085555779/1180591620717411303424:ℚ)⟩ thresholdNode264 thresholdNode266
def thresholdNode268 : BoxExpr 1 := .neg ⟨(6973095316030085555779/1180591620717411303424:ℚ),(30437972802599063007563/4722366482869645213696:ℚ)⟩ thresholdNode267
def thresholdNode269 : BoxExpr 1 := .mul ⟨(-30437972802599063007563/1180591620717411303424:ℚ),(-6973095316030085555779/295147905179352825856:ℚ)⟩ thresholdNode219 thresholdNode268
def thresholdNode270 : BoxExpr 1 := .add ⟨(-30437972802599063007563/1180591620717411303424:ℚ),(-6973095316030085555779/295147905179352825856:ℚ)⟩ thresholdNode261 thresholdNode269
def thresholdNode271 : BoxExpr 1 := .neg ⟨(6973095316030085555779/295147905179352825856:ℚ),(30437972802599063007563/1180591620717411303424:ℚ)⟩ thresholdNode270
def thresholdNode272 : BoxExpr 1 := .mul ⟨(17281934684042556348530739/4722366482869645213696:ℚ),(4757947023717332003840449/1180591620717411303424:ℚ)⟩ thresholdNode122 thresholdNode271
def thresholdNode273 : BoxExpr 1 := .add ⟨(12468545967104695126166405/4722366482869645213696:ℚ),(7191825745965334093118351/2361183241434822606848:ℚ)⟩ thresholdNode254 thresholdNode272
def thresholdNode274 : BoxExpr 1 := .add ⟨(7655157250166833903802071/4722366482869645213696:ℚ),(1216939361124001044638951/590295810358705651712:ℚ)⟩ thresholdNode255 thresholdNode273
def thresholdNode275 : BoxExpr 1 := .add ⟨(7655157250166833903802071/4722366482869645213696:ℚ),(1216939361124001044638951/590295810358705651712:ℚ)⟩ thresholdNode274 thresholdNode32
def thresholdNode276 : BoxExpr 1 := .mul ⟨(317196998842665806823451/4722366482869645213696:ℚ),(408757070532345709723177/4722366482869645213696:ℚ)⟩ thresholdNode275 thresholdNode228
def thresholdNode277 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode130
def thresholdNode278 : BoxExpr 1 := .mul ⟨(46299315865545822702795/2361183241434822606848:ℚ),(26215991932242325420547/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode229
def thresholdNode279 : BoxExpr 1 := .add ⟨(46299315865545822702795/2361183241434822606848:ℚ),(26215991932242325420547/1180591620717411303424:ℚ)⟩ thresholdNode277 thresholdNode278
def thresholdNode280 : BoxExpr 1 := .mul ⟨(1339420639261096089262799/2361183241434822606848:ℚ),(1375244084464882091741919/2361183241434822606848:ℚ)⟩ thresholdNode227 thresholdNode227
def thresholdNode281 : BoxExpr 1 := .inv ⟨(8107922604592773911/4722366482869645213696:ℚ),(2081193217504942809/1180591620717411303424:ℚ)⟩ thresholdNode280
def thresholdNode282 : BoxExpr 1 := .mul ⟨(9936524172921810035/295147905179352825856:ℚ),(92429157791908037751/2361183241434822606848:ℚ)⟩ thresholdNode279 thresholdNode281
def thresholdNode283 : BoxExpr 1 := .neg ⟨(-92429157791908037751/2361183241434822606848:ℚ),(-9936524172921810035/295147905179352825856:ℚ)⟩ thresholdNode282
def thresholdNode284 : BoxExpr 1 := .mul ⟨(-24442141032401654725269/2361183241434822606848:ℚ),(-4702235996118891454809/590295810358705651712:ℚ)⟩ thresholdNode226 thresholdNode283
def thresholdNode285 : BoxExpr 1 := .add ⟨(268312716777862497372913/4722366482869645213696:ℚ),(371139182563394578084705/4722366482869645213696:ℚ)⟩ thresholdNode276 thresholdNode284
def thresholdNode286 : BoxExpr 1 := .add ⟨(268312716777862497372913/4722366482869645213696:ℚ),(371139182563394578084705/4722366482869645213696:ℚ)⟩ thresholdNode285 thresholdNode32
def thresholdNode287 : BoxExpr 1 := .mul ⟨(16769544798616406085807/590295810358705651712:ℚ),(185569591281697289042353/4722366482869645213696:ℚ)⟩ thresholdNode286 thresholdNode132
def thresholdNode288 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode230 thresholdNode235
def thresholdNode289 : BoxExpr 1 := .add ⟨(16769544798616406085807/590295810358705651712:ℚ),(185569591281697289042353/4722366482869645213696:ℚ)⟩ thresholdNode287 thresholdNode288
def thresholdNode290 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode5 thresholdNode32
def thresholdNode291 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode241 thresholdNode290
def thresholdNode292 : BoxExpr 1 := .mul ⟨(16/1:ℚ),(16/1:ℚ)⟩ thresholdNode232 thresholdNode232
def thresholdNode293 : BoxExpr 1 := .inv ⟨(1/16:ℚ),(1/16:ℚ)⟩ thresholdNode292
def thresholdNode294 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode291 thresholdNode293
def thresholdNode295 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode294
def thresholdNode296 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode295
def thresholdNode297 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode234 thresholdNode296
def thresholdNode298 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode297
def thresholdNode299 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode131 thresholdNode298
def thresholdNode300 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode288 thresholdNode299
def thresholdNode301 : BoxExpr 1 := .add ⟨(16769544798616406085807/590295810358705651712:ℚ),(185569591281697289042353/4722366482869645213696:ℚ)⟩ thresholdNode289 thresholdNode300
def thresholdNode302 : BoxExpr 1 := .add ⟨(16769544798616406085807/590295810358705651712:ℚ),(185569591281697289042353/4722366482869645213696:ℚ)⟩ thresholdNode301 thresholdNode32
def thresholdNode303 : BoxExpr 1 := .mul ⟨(67036255332469083328007/2361183241434822606848:ℚ),(5796674535797400818709/147573952589676412928:ℚ)⟩ thresholdNode16 thresholdNode302
def thresholdNode304 : BoxExpr 1 := .add ⟨(67504761702617645131157/2361183241434822606848:ℚ),(186804384742128942469723/4722366482869645213696:ℚ)⟩ thresholdNode239 thresholdNode303
def thresholdNode305 : BoxExpr 1 := .add ⟨(17969687314399432026497/1180591620717411303424:ℚ),(62397239966538268253201/2361183241434822606848:ℚ)⟩ thresholdNode240 thresholdNode304
def thresholdNode306 : BoxExpr 1 := .neg ⟨(-62397239966538268253201/2361183241434822606848:ℚ),(-17969687314399432026497/1180591620717411303424:ℚ)⟩ thresholdNode305
def thresholdNode307 : BoxExpr 1 := .add ⟨(-94314799064081145756005/2361183241434822606848:ℚ),(-33918146142417069734821/1180591620717411303424:ℚ)⟩ thresholdNode206 thresholdNode306
def thresholdCell0Out1 : TaylorCertificate1 :=
  { center := (-6956533366137/307551593775760:ℚ), radius := (732256478257/307551593775760:ℚ)
    whole := thresholdNode138, centerValue := thresholdNode157, gradient := thresholdNode197, hessian := thresholdNode307 }
theorem thresholdCell0Out1_check : thresholdCell0Out1.check = true := by decide +kernel
theorem thresholdCell0Out1_lower_pos : 0 < thresholdCell0Out1.lower := by decide +kernel
theorem thresholdCell0Out1_positive (x : ℝ) (hx : (-(1/40:ℝ)) ≤ x ∧ x ≤ (-(155606922197/7688789844394:ℝ))) :
    0 < thresholdNode138.eval (fun _ => x) := by
  apply thresholdCell0Out1.positive_sound thresholdCell0Out1_check thresholdCell0Out1_lower_pos x
  norm_num [thresholdCell0Out1]
  exact hx
theorem thresholdCell0_public (x : ℝ)
    (hx : (-(1/40:ℝ)) ≤ x ∧ x ≤ (-(155606922197/7688789844394:ℝ))) : qc x < fA (43/20) x := by
  have hf := thresholdCell0Out0_positive x hx
  have hg := thresholdCell0Out1_positive x hx
  have hfa : thresholdNode18.eval (fun _ => x) = thresholdFA 1 x := by
    norm_num [thresholdNode0, thresholdNode1, thresholdNode2, thresholdNode3, thresholdNode4, thresholdNode5, thresholdNode6, thresholdNode7, thresholdNode8, thresholdNode9, thresholdNode10, thresholdNode11, thresholdNode12, thresholdNode13, thresholdNode14, thresholdNode15, thresholdNode16, thresholdNode17, thresholdNode18, BoxExpr.eval, thresholdFA, ftilde, pow_two, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  have hgap : thresholdNode138.eval (fun _ => x) =
      (thresholdNode18.eval (fun _ => x))^2 - (1-x^2)*(thresholdCapacity 1 x+1/4) := by
    norm_num [thresholdNode117, thresholdNode12, thresholdNode13, thresholdNode14, thresholdNode15, thresholdNode16, thresholdNode5, thresholdNode118, thresholdNode119, thresholdNode120, thresholdNode121, thresholdNode122, thresholdNode123, thresholdNode124, thresholdNode125, thresholdNode126, thresholdNode127, thresholdNode128, thresholdNode129, thresholdNode130, thresholdNode131, thresholdNode132, thresholdNode133, thresholdNode134, thresholdNode135, thresholdNode136, thresholdNode137, thresholdNode138, BoxExpr.eval, thresholdCapacity, Da, D5, beta5, eta5, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  rw [hfa] at hf
  rw [hgap, hfa] at hg
  refine threshold_positive_to_public 1 1 x ?_ ?_ ?_ hf hg
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdFADomain] <;> constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdCapacityDomain] <;> linarith [hx.1,hx.2]
def thresholdNode308 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode309 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode308 thresholdNode3
def thresholdNode310 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode311 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode310
def thresholdNode312 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode311 thresholdNode311
def thresholdNode313 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode312 thresholdNode9
def thresholdNode314 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode309 thresholdNode313
def thresholdNode315 : BoxExpr 1 := .var 0
def thresholdNode316 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(1934200681868100471/4722366482869645213696:ℚ)⟩ thresholdNode315 thresholdNode315
def thresholdNode317 : BoxExpr 1 := .neg ⟨(-1934200681868100471/4722366482869645213696:ℚ),(0/1:ℚ)⟩ thresholdNode316
def thresholdNode318 : BoxExpr 1 := .add ⟨(4720432282187777113225/4722366482869645213696:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode317
def thresholdNode319 : BoxExpr 1 := .sqrt ⟨(2360699641740739622335/2361183241434822606848:ℚ),(1/1:ℚ)⟩ thresholdNode318
def thresholdNode320 : BoxExpr 1 := .mul ⟨(3068142306879395768657/1180591620717411303424:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode314 thresholdNode319
def thresholdNode321 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode322 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode321 thresholdNode3
def thresholdNode323 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode324 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode323
def thresholdNode325 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode324 thresholdNode324
def thresholdNode326 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode325 thresholdNode9
def thresholdNode327 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode322 thresholdNode326
def thresholdNode328 : BoxExpr 1 := .var 0
def thresholdNode329 : BoxExpr 1 := .mul ⟨(483550170467025117/4722366482869645213696:ℚ),(241775085233512559/2361183241434822606848:ℚ)⟩ thresholdNode328 thresholdNode328
def thresholdNode330 : BoxExpr 1 := .neg ⟨(-241775085233512559/2361183241434822606848:ℚ),(-483550170467025117/4722366482869645213696:ℚ)⟩ thresholdNode329
def thresholdNode331 : BoxExpr 1 := .add ⟨(2360941466349589094289/2361183241434822606848:ℚ),(4721882932699178188579/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode330
def thresholdNode332 : BoxExpr 1 := .sqrt ⟨(4722124701594910629551/4722366482869645213696:ℚ),(4722124701594910629553/4722366482869645213696:ℚ)⟩ thresholdNode331
def thresholdNode333 : BoxExpr 1 := .mul ⟨(6137227421545365472459/2361183241434822606848:ℚ),(12274454843090730944933/4722366482869645213696:ℚ)⟩ thresholdNode327 thresholdNode332
def thresholdNode334 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode1
def thresholdNode335 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode32
def thresholdNode336 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode334 thresholdNode335
def thresholdNode337 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode336 thresholdNode32
def thresholdNode338 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32
def thresholdNode339 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode338
def thresholdNode340 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode339 thresholdNode324
def thresholdNode341 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode324 thresholdNode339
def thresholdNode342 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode340 thresholdNode341
def thresholdNode343 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode342 thresholdNode9
def thresholdNode344 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode325 thresholdNode32
def thresholdNode345 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode343 thresholdNode344
def thresholdNode346 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode337 thresholdNode345
def thresholdNode347 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode346 thresholdNode332
def thresholdNode348 : BoxExpr 1 := .mul ⟨(-47785992903772364679/4722366482869645213696:ℚ),(-23892996451886182339/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode328
def thresholdNode349 : BoxExpr 1 := .mul ⟨(-47785992903772364679/4722366482869645213696:ℚ),(-23892996451886182339/2361183241434822606848:ℚ)⟩ thresholdNode328 thresholdNode12
def thresholdNode350 : BoxExpr 1 := .add ⟨(-47785992903772364679/2361183241434822606848:ℚ),(-23892996451886182339/1180591620717411303424:ℚ)⟩ thresholdNode348 thresholdNode349
def thresholdNode351 : BoxExpr 1 := .neg ⟨(23892996451886182339/1180591620717411303424:ℚ),(47785992903772364679/2361183241434822606848:ℚ)⟩ thresholdNode350
def thresholdNode352 : BoxExpr 1 := .add ⟨(23892996451886182339/1180591620717411303424:ℚ),(47785992903772364679/2361183241434822606848:ℚ)⟩ thresholdNode32 thresholdNode351
def thresholdNode353 : BoxExpr 1 := .mul ⟨(4722124701594910629551/2361183241434822606848:ℚ),(4722124701594910629553/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode332
def thresholdNode354 : BoxExpr 1 := .inv ⟨(2361304138262007884087/4722366482869645213696:ℚ),(2361304138262007884089/4722366482869645213696:ℚ)⟩ thresholdNode353
def thresholdNode355 : BoxExpr 1 := .mul ⟨(23894219816262268125/2361183241434822606848:ℚ),(11947109908131134063/1180591620717411303424:ℚ)⟩ thresholdNode352 thresholdNode354
def thresholdNode356 : BoxExpr 1 := .mul ⟨(124218880558802653301/4722366482869645213696:ℚ),(124218880558802653307/4722366482869645213696:ℚ)⟩ thresholdNode327 thresholdNode355
def thresholdNode357 : BoxExpr 1 := .add ⟨(124218880558802653301/4722366482869645213696:ℚ),(124218880558802653307/4722366482869645213696:ℚ)⟩ thresholdNode347 thresholdNode356
def thresholdNode358 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode1
def thresholdNode359 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode32
def thresholdNode360 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode358 thresholdNode359
def thresholdNode361 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode32
def thresholdNode362 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode359 thresholdNode361
def thresholdNode363 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode360 thresholdNode362
def thresholdNode364 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode363 thresholdNode32
def thresholdNode365 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32
def thresholdNode366 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode365
def thresholdNode367 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode366 thresholdNode311
def thresholdNode368 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode366 thresholdNode366
def thresholdNode369 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode367 thresholdNode368
def thresholdNode370 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode311 thresholdNode366
def thresholdNode371 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode368 thresholdNode370
def thresholdNode372 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode369 thresholdNode371
def thresholdNode373 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode372 thresholdNode9
def thresholdNode374 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode367 thresholdNode370
def thresholdNode375 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode374 thresholdNode32
def thresholdNode376 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode373 thresholdNode375
def thresholdNode377 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode312 thresholdNode32
def thresholdNode378 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode375 thresholdNode377
def thresholdNode379 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode376 thresholdNode378
def thresholdNode380 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode364 thresholdNode379
def thresholdNode381 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode380 thresholdNode319
def thresholdNode382 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode358 thresholdNode361
def thresholdNode383 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode382 thresholdNode32
def thresholdNode384 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode374 thresholdNode9
def thresholdNode385 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode384 thresholdNode377
def thresholdNode386 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode383 thresholdNode385
def thresholdNode387 : BoxExpr 1 := .mul ⟨(-95571985807544729357/4722366482869645213696:ℚ),(0/1:ℚ)⟩ thresholdNode12 thresholdNode315
def thresholdNode388 : BoxExpr 1 := .mul ⟨(-95571985807544729357/4722366482869645213696:ℚ),(0/1:ℚ)⟩ thresholdNode315 thresholdNode12
def thresholdNode389 : BoxExpr 1 := .add ⟨(-95571985807544729357/2361183241434822606848:ℚ),(0/1:ℚ)⟩ thresholdNode387 thresholdNode388
def thresholdNode390 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(95571985807544729357/2361183241434822606848:ℚ)⟩ thresholdNode389
def thresholdNode391 : BoxExpr 1 := .add ⟨(0/1:ℚ),(95571985807544729357/2361183241434822606848:ℚ)⟩ thresholdNode32 thresholdNode390
def thresholdNode392 : BoxExpr 1 := .mul ⟨(2360699641740739622335/1180591620717411303424:ℚ),(2/1:ℚ)⟩ thresholdNode5 thresholdNode319
def thresholdNode393 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(2361666940196427770805/4722366482869645213696:ℚ)⟩ thresholdNode392
def thresholdNode394 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(95591564148762823149/4722366482869645213696:ℚ)⟩ thresholdNode391 thresholdNode393
def thresholdNode395 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode386 thresholdNode394
def thresholdNode396 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode381 thresholdNode395
def thresholdNode397 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode315
def thresholdNode398 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode12
def thresholdNode399 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode397 thresholdNode398
def thresholdNode400 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode315 thresholdNode32
def thresholdNode401 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode398 thresholdNode400
def thresholdNode402 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode399 thresholdNode401
def thresholdNode403 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode402
def thresholdNode404 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode32 thresholdNode403
def thresholdNode405 : BoxExpr 1 := .mul ⟨(-2361666940196427770805/2361183241434822606848:ℚ),(-1/1:ℚ)⟩ thresholdNode404 thresholdNode393
def thresholdNode406 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode319
def thresholdNode407 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(95591564148762823149/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode394
def thresholdNode408 : BoxExpr 1 := .add ⟨(0/1:ℚ),(95591564148762823149/2361183241434822606848:ℚ)⟩ thresholdNode406 thresholdNode407
def thresholdNode409 : BoxExpr 1 := .mul ⟨(18881729128751108452899/4722366482869645213696:ℚ),(4/1:ℚ)⟩ thresholdNode392 thresholdNode392
def thresholdNode410 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1181075369022924765705/4722366482869645213696:ℚ)⟩ thresholdNode409
def thresholdNode411 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(23907683216037072105/2361183241434822606848:ℚ)⟩ thresholdNode408 thresholdNode410
def thresholdNode412 : BoxExpr 1 := .neg ⟨(-23907683216037072105/2361183241434822606848:ℚ),(0/1:ℚ)⟩ thresholdNode411
def thresholdNode413 : BoxExpr 1 := .mul ⟨(-967694806958692457/2361183241434822606848:ℚ),(0/1:ℚ)⟩ thresholdNode391 thresholdNode412
def thresholdNode414 : BoxExpr 1 := .add ⟨(-1181317317501693231631/1180591620717411303424:ℚ),(-1/1:ℚ)⟩ thresholdNode405 thresholdNode413
def thresholdNode415 : BoxExpr 1 := .mul ⟨(-12282628676992105206565/4722366482869645213696:ℚ),(-1534385414655901535777/590295810358705651712:ℚ)⟩ thresholdNode314 thresholdNode414
def thresholdNode416 : BoxExpr 1 := .add ⟨(-12282628676992105206565/4722366482869645213696:ℚ),(-1534385414655901535777/590295810358705651712:ℚ)⟩ thresholdNode395 thresholdNode415
def thresholdNode417 : BoxExpr 1 := .add ⟨(-12282628676992105206565/4722366482869645213696:ℚ),(-1534385414655901535777/590295810358705651712:ℚ)⟩ thresholdNode396 thresholdNode416
def thresholdCell1Out0 : TaylorCertificate1 :=
  { center := (-155606922197/15377579688788:ℚ), radius := (155606922197/15377579688788:ℚ)
    whole := thresholdNode320, centerValue := thresholdNode333, gradient := thresholdNode357, hessian := thresholdNode417 }
theorem thresholdCell1Out0_check : thresholdCell1Out0.check = true := by decide +kernel
theorem thresholdCell1Out0_lower_pos : 0 < thresholdCell1Out0.lower := by decide +kernel
theorem thresholdCell1Out0_positive (x : ℝ) (hx : (-(155606922197/7688789844394:ℝ)) ≤ x ∧ x ≤ (0:ℝ)) :
    0 < thresholdNode320.eval (fun _ => x) := by
  apply thresholdCell1Out0.positive_sound thresholdCell1Out0_check thresholdCell1Out0_lower_pos x
  norm_num [thresholdCell1Out0]
  exact hx
def thresholdNode418 : BoxExpr 1 := .mul ⟨(31894169160858217823067/4722366482869645213696:ℚ),(31907237820686541256211/4722366482869645213696:ℚ)⟩ thresholdNode320 thresholdNode320
def thresholdNode419 : BoxExpr 1 := .lit (2076850672197/307399000000:ℚ)
def thresholdNode420 : BoxExpr 1 := .mul ⟨(15946104181084036850117/2361183241434822606848:ℚ),(31905276218557657466653/4722366482869645213696:ℚ)⟩ thresholdNode318 thresholdNode419
def thresholdNode421 : BoxExpr 1 := .neg ⟨(-31905276218557657466653/4722366482869645213696:ℚ),(-15946104181084036850117/2361183241434822606848:ℚ)⟩ thresholdNode420
def thresholdNode422 : BoxExpr 1 := .add ⟨(-5553528849719821793/2361183241434822606848:ℚ),(15029458518467555977/4722366482869645213696:ℚ)⟩ thresholdNode418 thresholdNode421
def thresholdNode423 : BoxExpr 1 := .mul ⟨(31903970655729460397875/4722366482869645213696:ℚ),(15951985327864730198977/2361183241434822606848:ℚ)⟩ thresholdNode333 thresholdNode333
def thresholdNode424 : BoxExpr 1 := .mul ⟨(15951004627230130762523/2361183241434822606848:ℚ),(15951004627230130762527/2361183241434822606848:ℚ)⟩ thresholdNode331 thresholdNode419
def thresholdNode425 : BoxExpr 1 := .neg ⟨(-15951004627230130762527/2361183241434822606848:ℚ),(-15951004627230130762523/2361183241434822606848:ℚ)⟩ thresholdNode424
def thresholdNode426 : BoxExpr 1 := .add ⟨(1961401269198872821/4722366482869645213696:ℚ),(490350317299718227/1180591620717411303424:ℚ)⟩ thresholdNode423 thresholdNode425
def thresholdNode427 : BoxExpr 1 := .mul ⟨(161435907781534218235/2361183241434822606848:ℚ),(322871815563068436487/4722366482869645213696:ℚ)⟩ thresholdNode357 thresholdNode333
def thresholdNode428 : BoxExpr 1 := .mul ⟨(161435907781534218235/2361183241434822606848:ℚ),(322871815563068436487/4722366482869645213696:ℚ)⟩ thresholdNode333 thresholdNode357
def thresholdNode429 : BoxExpr 1 := .add ⟨(161435907781534218235/1180591620717411303424:ℚ),(322871815563068436487/2361183241434822606848:ℚ)⟩ thresholdNode427 thresholdNode428
def thresholdNode430 : BoxExpr 1 := .mul ⟨(322851965958902623361/2361183241434822606848:ℚ),(40356495744862827921/295147905179352825856:ℚ)⟩ thresholdNode352 thresholdNode419
def thresholdNode431 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode331 thresholdNode32
def thresholdNode432 : BoxExpr 1 := .add ⟨(322851965958902623361/2361183241434822606848:ℚ),(40356495744862827921/295147905179352825856:ℚ)⟩ thresholdNode430 thresholdNode431
def thresholdNode433 : BoxExpr 1 := .neg ⟨(-40356495744862827921/295147905179352825856:ℚ),(-322851965958902623361/2361183241434822606848:ℚ)⟩ thresholdNode432
def thresholdNode434 : BoxExpr 1 := .add ⟨(9924802082906551/1180591620717411303424:ℚ),(9924802082906563/1180591620717411303424:ℚ)⟩ thresholdNode429 thresholdNode433
def thresholdNode435 : BoxExpr 1 := .mul ⟨(-3990856356442428583587/590295810358705651712:ℚ),(-15950351410773914782511/2361183241434822606848:ℚ)⟩ thresholdNode417 thresholdNode320
def thresholdNode436 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode386 thresholdNode319
def thresholdNode437 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(248475932270086644353/4722366482869645213696:ℚ)⟩ thresholdNode314 thresholdNode394
def thresholdNode438 : BoxExpr 1 := .add ⟨(0/1:ℚ),(248475932270086644353/4722366482869645213696:ℚ)⟩ thresholdNode436 thresholdNode437
def thresholdNode439 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(6537007360764057183/2361183241434822606848:ℚ)⟩ thresholdNode438 thresholdNode438
def thresholdNode440 : BoxExpr 1 := .add ⟨(-3990856356442428583587/590295810358705651712:ℚ),(-996488400213321920333/147573952589676412928:ℚ)⟩ thresholdNode435 thresholdNode439
def thresholdNode441 : BoxExpr 1 := .mul ⟨(-3990856356442428583587/590295810358705651712:ℚ),(-15950351410773914782511/2361183241434822606848:ℚ)⟩ thresholdNode320 thresholdNode417
def thresholdNode442 : BoxExpr 1 := .add ⟨(-3990856356442428583587/590295810358705651712:ℚ),(-996488400213321920333/147573952589676412928:ℚ)⟩ thresholdNode439 thresholdNode441
def thresholdNode443 : BoxExpr 1 := .add ⟨(-3990856356442428583587/295147905179352825856:ℚ),(-996488400213321920333/73786976294838206464:ℚ)⟩ thresholdNode440 thresholdNode442
def thresholdNode444 : BoxExpr 1 := .mul ⟨(-31905276218557657466653/2361183241434822606848:ℚ),(-7976319054639414366663/590295810358705651712:ℚ)⟩ thresholdNode404 thresholdNode419
def thresholdNode445 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode391 thresholdNode32
def thresholdNode446 : BoxExpr 1 := .add ⟨(-31905276218557657466653/2361183241434822606848:ℚ),(-7976319054639414366663/590295810358705651712:ℚ)⟩ thresholdNode444 thresholdNode445
def thresholdNode447 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode318 thresholdNode32
def thresholdNode448 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode445 thresholdNode447
def thresholdNode449 : BoxExpr 1 := .add ⟨(-31905276218557657466653/2361183241434822606848:ℚ),(-7976319054639414366663/590295810358705651712:ℚ)⟩ thresholdNode446 thresholdNode448
def thresholdNode450 : BoxExpr 1 := .neg ⟨(7976319054639414366663/590295810358705651712:ℚ),(31905276218557657466653/2361183241434822606848:ℚ)⟩ thresholdNode449
def thresholdNode451 : BoxExpr 1 := .add ⟨(-5393658245442800511/590295810358705651712:ℚ),(17647411731356015997/2361183241434822606848:ℚ)⟩ thresholdNode443 thresholdNode450
def thresholdCell1Out1 : TaylorCertificate1 :=
  { center := (-155606922197/15377579688788:ℚ), radius := (155606922197/15377579688788:ℚ)
    whole := thresholdNode422, centerValue := thresholdNode426, gradient := thresholdNode434, hessian := thresholdNode451 }
theorem thresholdCell1Out1_check : thresholdCell1Out1.check = true := by decide +kernel
theorem thresholdCell1Out1_lower_pos : 0 < thresholdCell1Out1.lower := by decide +kernel
theorem thresholdCell1Out1_positive (x : ℝ) (hx : (-(155606922197/7688789844394:ℝ)) ≤ x ∧ x ≤ (0:ℝ)) :
    0 < thresholdNode422.eval (fun _ => x) := by
  apply thresholdCell1Out1.positive_sound thresholdCell1Out1_check thresholdCell1Out1_lower_pos x
  norm_num [thresholdCell1Out1]
  exact hx
theorem thresholdCell1_public (x : ℝ)
    (hx : (-(155606922197/7688789844394:ℝ)) ≤ x ∧ x ≤ (0:ℝ)) : qc x < fA (43/20) x := by
  have hf := thresholdCell1Out0_positive x hx
  have hg := thresholdCell1Out1_positive x hx
  have hfa : thresholdNode320.eval (fun _ => x) = thresholdFA 1 x := by
    norm_num [thresholdNode0, thresholdNode1, thresholdNode308, thresholdNode3, thresholdNode309, thresholdNode5, thresholdNode310, thresholdNode311, thresholdNode312, thresholdNode9, thresholdNode313, thresholdNode314, thresholdNode12, thresholdNode315, thresholdNode316, thresholdNode317, thresholdNode318, thresholdNode319, thresholdNode320, BoxExpr.eval, thresholdFA, ftilde, pow_two, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  have hgap : thresholdNode422.eval (fun _ => x) =
      (thresholdNode320.eval (fun _ => x))^2 - (1-x^2)*(thresholdCapacity 2 x+1/4) := by
    norm_num [thresholdNode418, thresholdNode12, thresholdNode315, thresholdNode316, thresholdNode317, thresholdNode318, thresholdNode419, thresholdNode420, thresholdNode421, thresholdNode422, BoxExpr.eval, thresholdCapacity, Da, D5, beta5, eta5, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  rw [hfa] at hf
  rw [hgap, hfa] at hg
  refine threshold_positive_to_public 1 2 x ?_ ?_ ?_ hf hg
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdFADomain] <;> constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdCapacityDomain] <;> linarith [hx.1,hx.2]
def thresholdNode452 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode453 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode452 thresholdNode3
def thresholdNode454 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode455 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode454
def thresholdNode456 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode455 thresholdNode455
def thresholdNode457 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode456 thresholdNode9
def thresholdNode458 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode453 thresholdNode457
def thresholdNode459 : BoxExpr 1 := .var 0
def thresholdNode460 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(1786640353283903609/4722366482869645213696:ℚ)⟩ thresholdNode459 thresholdNode459
def thresholdNode461 : BoxExpr 1 := .neg ⟨(-1786640353283903609/4722366482869645213696:ℚ),(0/1:ℚ)⟩ thresholdNode460
def thresholdNode462 : BoxExpr 1 := .add ⟨(4720579842516361310087/4722366482869645213696:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode461
def thresholdNode463 : BoxExpr 1 := .sqrt ⟨(2360736539091631294971/2361183241434822606848:ℚ),(1/1:ℚ)⟩ thresholdNode462
def thresholdNode464 : BoxExpr 1 := .mul ⟨(12272761045775663613161/4722366482869645213696:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode458 thresholdNode463
def thresholdNode465 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode466 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode465 thresholdNode3
def thresholdNode467 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode468 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode467
def thresholdNode469 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode468 thresholdNode468
def thresholdNode470 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode469 thresholdNode9
def thresholdNode471 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode466 thresholdNode470
def thresholdNode472 : BoxExpr 1 := .var 0
def thresholdNode473 : BoxExpr 1 := .mul ⟨(223330044160487951/2361183241434822606848:ℚ),(446660088320975903/4722366482869645213696:ℚ)⟩ thresholdNode472 thresholdNode472
def thresholdNode474 : BoxExpr 1 := .neg ⟨(-446660088320975903/4722366482869645213696:ℚ),(-223330044160487951/2361183241434822606848:ℚ)⟩ thresholdNode473
def thresholdNode475 : BoxExpr 1 := .add ⟨(4721919822781324237793/4722366482869645213696:ℚ),(2360959911390662118897/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode474
def thresholdNode476 : BoxExpr 1 := .sqrt ⟨(2361071573772187691061/2361183241434822606848:ℚ),(4722143147544375382123/4722366482869645213696:ℚ)⟩ thresholdNode475
def thresholdNode477 : BoxExpr 1 := .mul ⟨(6137251395284736074757/2361183241434822606848:ℚ),(6137251395284736074763/2361183241434822606848:ℚ)⟩ thresholdNode471 thresholdNode476
def thresholdNode478 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode1
def thresholdNode479 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode32
def thresholdNode480 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode478 thresholdNode479
def thresholdNode481 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode480 thresholdNode32
def thresholdNode482 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32
def thresholdNode483 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode482
def thresholdNode484 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode483 thresholdNode468
def thresholdNode485 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode468 thresholdNode483
def thresholdNode486 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode484 thresholdNode485
def thresholdNode487 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode486 thresholdNode9
def thresholdNode488 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode469 thresholdNode32
def thresholdNode489 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode487 thresholdNode488
def thresholdNode490 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode481 thresholdNode489
def thresholdNode491 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode490 thresholdNode476
def thresholdNode492 : BoxExpr 1 := .mul ⟨(45927035940963706679/4722366482869645213696:ℚ),(5740879492620463335/590295810358705651712:ℚ)⟩ thresholdNode12 thresholdNode472
def thresholdNode493 : BoxExpr 1 := .mul ⟨(45927035940963706679/4722366482869645213696:ℚ),(5740879492620463335/590295810358705651712:ℚ)⟩ thresholdNode472 thresholdNode12
def thresholdNode494 : BoxExpr 1 := .add ⟨(45927035940963706679/2361183241434822606848:ℚ),(5740879492620463335/295147905179352825856:ℚ)⟩ thresholdNode492 thresholdNode493
def thresholdNode495 : BoxExpr 1 := .neg ⟨(-5740879492620463335/295147905179352825856:ℚ),(-45927035940963706679/2361183241434822606848:ℚ)⟩ thresholdNode494
def thresholdNode496 : BoxExpr 1 := .add ⟨(-5740879492620463335/295147905179352825856:ℚ),(-45927035940963706679/2361183241434822606848:ℚ)⟩ thresholdNode32 thresholdNode495
def thresholdNode497 : BoxExpr 1 := .mul ⟨(2361071573772187691061/1180591620717411303424:ℚ),(4722143147544375382123/2361183241434822606848:ℚ)⟩ thresholdNode5 thresholdNode476
def thresholdNode498 : BoxExpr 1 := .inv ⟨(2361294914378816638073/4722366482869645213696:ℚ),(1180647457189408319037/2361183241434822606848:ℚ)⟩ thresholdNode497
def thresholdNode499 : BoxExpr 1 := .mul ⟨(-45929208075350587417/4722366482869645213696:ℚ),(-45929208075350587415/4722366482869645213696:ℚ)⟩ thresholdNode496 thresholdNode498
def thresholdNode500 : BoxExpr 1 := .mul ⟨(-119386087010662549403/4722366482869645213696:ℚ),(-119386087010662549397/4722366482869645213696:ℚ)⟩ thresholdNode471 thresholdNode499
def thresholdNode501 : BoxExpr 1 := .add ⟨(-119386087010662549403/4722366482869645213696:ℚ),(-119386087010662549397/4722366482869645213696:ℚ)⟩ thresholdNode491 thresholdNode500
def thresholdNode502 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode1
def thresholdNode503 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode32
def thresholdNode504 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode502 thresholdNode503
def thresholdNode505 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode32
def thresholdNode506 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode503 thresholdNode505
def thresholdNode507 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode504 thresholdNode506
def thresholdNode508 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode507 thresholdNode32
def thresholdNode509 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32
def thresholdNode510 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode509
def thresholdNode511 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode510 thresholdNode455
def thresholdNode512 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode510 thresholdNode510
def thresholdNode513 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode511 thresholdNode512
def thresholdNode514 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode455 thresholdNode510
def thresholdNode515 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode512 thresholdNode514
def thresholdNode516 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode513 thresholdNode515
def thresholdNode517 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode516 thresholdNode9
def thresholdNode518 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode511 thresholdNode514
def thresholdNode519 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode518 thresholdNode32
def thresholdNode520 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode517 thresholdNode519
def thresholdNode521 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode456 thresholdNode32
def thresholdNode522 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode519 thresholdNode521
def thresholdNode523 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode520 thresholdNode522
def thresholdNode524 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode508 thresholdNode523
def thresholdNode525 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode524 thresholdNode463
def thresholdNode526 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode502 thresholdNode505
def thresholdNode527 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode526 thresholdNode32
def thresholdNode528 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode518 thresholdNode9
def thresholdNode529 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode528 thresholdNode521
def thresholdNode530 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode527 thresholdNode529
def thresholdNode531 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(91854071881927413359/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode459
def thresholdNode532 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(91854071881927413359/4722366482869645213696:ℚ)⟩ thresholdNode459 thresholdNode12
def thresholdNode533 : BoxExpr 1 := .add ⟨(0/1:ℚ),(91854071881927413359/2361183241434822606848:ℚ)⟩ thresholdNode531 thresholdNode532
def thresholdNode534 : BoxExpr 1 := .neg ⟨(-91854071881927413359/2361183241434822606848:ℚ),(0/1:ℚ)⟩ thresholdNode533
def thresholdNode535 : BoxExpr 1 := .add ⟨(-91854071881927413359/2361183241434822606848:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode534
def thresholdNode536 : BoxExpr 1 := .mul ⟨(2360736539091631294971/1180591620717411303424:ℚ),(2/1:ℚ)⟩ thresholdNode5 thresholdNode463
def thresholdNode537 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(2361630028303745658951/4722366482869645213696:ℚ)⟩ thresholdNode536
def thresholdNode538 : BoxExpr 1 := .mul ⟨(-45935726328150476009/2361183241434822606848:ℚ),(0/1:ℚ)⟩ thresholdNode535 thresholdNode537
def thresholdNode539 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode530 thresholdNode538
def thresholdNode540 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode525 thresholdNode539
def thresholdNode541 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode459
def thresholdNode542 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode12
def thresholdNode543 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode541 thresholdNode542
def thresholdNode544 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode459 thresholdNode32
def thresholdNode545 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode542 thresholdNode544
def thresholdNode546 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode543 thresholdNode545
def thresholdNode547 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode546
def thresholdNode548 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode32 thresholdNode547
def thresholdNode549 : BoxExpr 1 := .mul ⟨(-2361630028303745658951/2361183241434822606848:ℚ),(-1/1:ℚ)⟩ thresholdNode548 thresholdNode537
def thresholdNode550 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode463
def thresholdNode551 : BoxExpr 1 := .mul ⟨(-45935726328150476009/1180591620717411303424:ℚ),(0/1:ℚ)⟩ thresholdNode5 thresholdNode538
def thresholdNode552 : BoxExpr 1 := .add ⟨(-45935726328150476009/1180591620717411303424:ℚ),(0/1:ℚ)⟩ thresholdNode550 thresholdNode551
def thresholdNode553 : BoxExpr 1 := .mul ⟨(18882319370065445240343/4722366482869645213696:ℚ),(4/1:ℚ)⟩ thresholdNode536 thresholdNode536
def thresholdNode554 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1181038449857197272707/4722366482869645213696:ℚ)⟩ thresholdNode553
def thresholdNode555 : BoxExpr 1 := .mul ⟨(-45953112036062055523/4722366482869645213696:ℚ),(0/1:ℚ)⟩ thresholdNode552 thresholdNode554
def thresholdNode556 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(45953112036062055523/4722366482869645213696:ℚ)⟩ thresholdNode555
def thresholdNode557 : BoxExpr 1 := .mul ⟨(-1787654758041455683/4722366482869645213696:ℚ),(0/1:ℚ)⟩ thresholdNode535 thresholdNode556
def thresholdNode558 : BoxExpr 1 := .add ⟨(-4725047711365532773585/4722366482869645213696:ℚ),(-1/1:ℚ)⟩ thresholdNode549 thresholdNode557
def thresholdNode559 : BoxExpr 1 := .mul ⟨(-12282052768537997615023/4722366482869645213696:ℚ),(-1534385414655901535777/590295810358705651712:ℚ)⟩ thresholdNode458 thresholdNode558
def thresholdNode560 : BoxExpr 1 := .add ⟨(-12282052768537997615023/4722366482869645213696:ℚ),(-1534385414655901535777/590295810358705651712:ℚ)⟩ thresholdNode539 thresholdNode559
def thresholdNode561 : BoxExpr 1 := .add ⟨(-12282052768537997615023/4722366482869645213696:ℚ),(-1534385414655901535777/590295810358705651712:ℚ)⟩ thresholdNode540 thresholdNode560
def thresholdCell2Out0 : TaylorCertificate1 :=
  { center := (155606922197/16000007377576:ℚ), radius := (155606922197/16000007377576:ℚ)
    whole := thresholdNode464, centerValue := thresholdNode477, gradient := thresholdNode501, hessian := thresholdNode561 }
theorem thresholdCell2Out0_check : thresholdCell2Out0.check = true := by decide +kernel
theorem thresholdCell2Out0_lower_pos : 0 < thresholdCell2Out0.lower := by decide +kernel
theorem thresholdCell2Out0_positive (x : ℝ) (hx : (0:ℝ) ≤ x ∧ x ≤ (155606922197/8000003688788:ℝ)) :
    0 < thresholdNode464.eval (fun _ => x) := by
  apply thresholdCell2Out0.positive_sound thresholdCell2Out0_check thresholdCell2Out0_lower_pos x
  norm_num [thresholdCell2Out0]
  exact hx
def thresholdNode562 : BoxExpr 1 := .mul ⟨(31895166169987880618089/4722366482869645213696:ℚ),(31907237820686541256211/4722366482869645213696:ℚ)⟩ thresholdNode464 thresholdNode464
def thresholdNode563 : BoxExpr 1 := .mul ⟨(31893205310003329180721/4722366482869645213696:ℚ),(31905276218557657466653/4722366482869645213696:ℚ)⟩ thresholdNode462 thresholdNode419
def thresholdNode564 : BoxExpr 1 := .neg ⟨(-31905276218557657466653/4722366482869645213696:ℚ),(-31893205310003329180721/4722366482869645213696:ℚ)⟩ thresholdNode563
def thresholdNode565 : BoxExpr 1 := .add ⟨(-2527512142444212141/1180591620717411303424:ℚ),(7016255341606037745/2361183241434822606848:ℚ)⟩ thresholdNode562 thresholdNode564
def thresholdNode566 : BoxExpr 1 := .mul ⟨(7976054977002969024159/1180591620717411303424:ℚ),(31904219908011876096699/4722366482869645213696:ℚ)⟩ thresholdNode477 thresholdNode477
def thresholdNode567 : BoxExpr 1 := .mul ⟨(7975564622854768848791/1180591620717411303424:ℚ),(31902258491419075395173/4722366482869645213696:ℚ)⟩ thresholdNode475 thresholdNode419
def thresholdNode568 : BoxExpr 1 := .neg ⟨(-31902258491419075395173/4722366482869645213696:ℚ),(-7975564622854768848791/1180591620717411303424:ℚ)⟩ thresholdNode567
def thresholdNode569 : BoxExpr 1 := .add ⟨(1961416592800701463/4722366482869645213696:ℚ),(1961416592800701535/4722366482869645213696:ℚ)⟩ thresholdNode566 thresholdNode568
def thresholdNode570 : BoxExpr 1 := .mul ⟨(-310311548983606884889/4722366482869645213696:ℚ),(-38788943622950860609/590295810358705651712:ℚ)⟩ thresholdNode501 thresholdNode477
def thresholdNode571 : BoxExpr 1 := .mul ⟨(-310311548983606884889/4722366482869645213696:ℚ),(-38788943622950860609/590295810358705651712:ℚ)⟩ thresholdNode477 thresholdNode501
def thresholdNode572 : BoxExpr 1 := .add ⟨(-310311548983606884889/2361183241434822606848:ℚ),(-38788943622950860609/295147905179352825856:ℚ)⟩ thresholdNode570 thresholdNode571
def thresholdNode573 : BoxExpr 1 := .mul ⟨(-155146235781518893403/1180591620717411303424:ℚ),(-310292471563037786799/2361183241434822606848:ℚ)⟩ thresholdNode496 thresholdNode419
def thresholdNode574 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode475 thresholdNode32
def thresholdNode575 : BoxExpr 1 := .add ⟨(-155146235781518893403/1180591620717411303424:ℚ),(-310292471563037786799/2361183241434822606848:ℚ)⟩ thresholdNode573 thresholdNode574
def thresholdNode576 : BoxExpr 1 := .neg ⟨(310292471563037786799/2361183241434822606848:ℚ),(155146235781518893403/1180591620717411303424:ℚ)⟩ thresholdNode575
def thresholdNode577 : BoxExpr 1 := .add ⟨(-9538710284549045/1180591620717411303424:ℚ),(-9538710284549033/1180591620717411303424:ℚ)⟩ thresholdNode572 thresholdNode576
def thresholdNode578 : BoxExpr 1 := .mul ⟨(-15962676931949622050311/2361183241434822606848:ℚ),(-31901201424336971212857/4722366482869645213696:ℚ)⟩ thresholdNode561 thresholdNode464
def thresholdNode579 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode530 thresholdNode463
def thresholdNode580 : BoxExpr 1 := .mul ⟨(-238806060462155879629/4722366482869645213696:ℚ),(0/1:ℚ)⟩ thresholdNode458 thresholdNode538
def thresholdNode581 : BoxExpr 1 := .add ⟨(-238806060462155879629/4722366482869645213696:ℚ),(0/1:ℚ)⟩ thresholdNode579 thresholdNode580
def thresholdNode582 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(12076219564983949315/4722366482869645213696:ℚ)⟩ thresholdNode581 thresholdNode581
def thresholdNode583 : BoxExpr 1 := .add ⟨(-15962676931949622050311/2361183241434822606848:ℚ),(-15944562602385993631771/2361183241434822606848:ℚ)⟩ thresholdNode578 thresholdNode582
def thresholdNode584 : BoxExpr 1 := .mul ⟨(-15962676931949622050311/2361183241434822606848:ℚ),(-31901201424336971212857/4722366482869645213696:ℚ)⟩ thresholdNode464 thresholdNode561
def thresholdNode585 : BoxExpr 1 := .add ⟨(-15962676931949622050311/2361183241434822606848:ℚ),(-15944562602385993631771/2361183241434822606848:ℚ)⟩ thresholdNode582 thresholdNode584
def thresholdNode586 : BoxExpr 1 := .add ⟨(-15962676931949622050311/1180591620717411303424:ℚ),(-15944562602385993631771/1180591620717411303424:ℚ)⟩ thresholdNode583 thresholdNode585
def thresholdNode587 : BoxExpr 1 := .mul ⟨(-31905276218557657466653/2361183241434822606848:ℚ),(-7976319054639414366663/590295810358705651712:ℚ)⟩ thresholdNode548 thresholdNode419
def thresholdNode588 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode535 thresholdNode32
def thresholdNode589 : BoxExpr 1 := .add ⟨(-31905276218557657466653/2361183241434822606848:ℚ),(-7976319054639414366663/590295810358705651712:ℚ)⟩ thresholdNode587 thresholdNode588
def thresholdNode590 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode462 thresholdNode32
def thresholdNode591 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode588 thresholdNode590
def thresholdNode592 : BoxExpr 1 := .add ⟨(-31905276218557657466653/2361183241434822606848:ℚ),(-7976319054639414366663/590295810358705651712:ℚ)⟩ thresholdNode589 thresholdNode591
def thresholdNode593 : BoxExpr 1 := .neg ⟨(7976319054639414366663/590295810358705651712:ℚ),(31905276218557657466653/2361183241434822606848:ℚ)⟩ thresholdNode592
def thresholdNode594 : BoxExpr 1 := .add ⟨(-10038822670793316985/1180591620717411303424:ℚ),(16151013785670203111/2361183241434822606848:ℚ)⟩ thresholdNode586 thresholdNode593
def thresholdCell2Out1 : TaylorCertificate1 :=
  { center := (155606922197/16000007377576:ℚ), radius := (155606922197/16000007377576:ℚ)
    whole := thresholdNode565, centerValue := thresholdNode569, gradient := thresholdNode577, hessian := thresholdNode594 }
theorem thresholdCell2Out1_check : thresholdCell2Out1.check = true := by decide +kernel
theorem thresholdCell2Out1_lower_pos : 0 < thresholdCell2Out1.lower := by decide +kernel
theorem thresholdCell2Out1_positive (x : ℝ) (hx : (0:ℝ) ≤ x ∧ x ≤ (155606922197/8000003688788:ℝ)) :
    0 < thresholdNode565.eval (fun _ => x) := by
  apply thresholdCell2Out1.positive_sound thresholdCell2Out1_check thresholdCell2Out1_lower_pos x
  norm_num [thresholdCell2Out1]
  exact hx
theorem thresholdCell2_public (x : ℝ)
    (hx : (0:ℝ) ≤ x ∧ x ≤ (155606922197/8000003688788:ℝ)) : qc x < fA (43/20) x := by
  have hf := thresholdCell2Out0_positive x hx
  have hg := thresholdCell2Out1_positive x hx
  have hfa : thresholdNode464.eval (fun _ => x) = thresholdFA 1 x := by
    norm_num [thresholdNode0, thresholdNode1, thresholdNode452, thresholdNode3, thresholdNode453, thresholdNode5, thresholdNode454, thresholdNode455, thresholdNode456, thresholdNode9, thresholdNode457, thresholdNode458, thresholdNode12, thresholdNode459, thresholdNode460, thresholdNode461, thresholdNode462, thresholdNode463, thresholdNode464, BoxExpr.eval, thresholdFA, ftilde, pow_two, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  have hgap : thresholdNode565.eval (fun _ => x) =
      (thresholdNode464.eval (fun _ => x))^2 - (1-x^2)*(thresholdCapacity 2 x+1/4) := by
    norm_num [thresholdNode562, thresholdNode12, thresholdNode459, thresholdNode460, thresholdNode461, thresholdNode462, thresholdNode419, thresholdNode563, thresholdNode564, thresholdNode565, BoxExpr.eval, thresholdCapacity, Da, D5, beta5, eta5, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  rw [hfa] at hf
  rw [hgap, hfa] at hg
  refine threshold_positive_to_public 1 2 x ?_ ?_ ?_ hf hg
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdFADomain] <;> constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdCapacityDomain] <;> linarith [hx.1,hx.2]
def thresholdNode595 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode596 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode595 thresholdNode3
def thresholdNode597 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode598 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode597
def thresholdNode599 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode598 thresholdNode598
def thresholdNode600 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode599 thresholdNode9
def thresholdNode601 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode596 thresholdNode600
def thresholdNode602 : BoxExpr 1 := .var 0
def thresholdNode603 : BoxExpr 1 := .mul ⟨(223330044160487951/590295810358705651712:ℚ),(944473296573929043/2361183241434822606848:ℚ)⟩ thresholdNode602 thresholdNode602
def thresholdNode604 : BoxExpr 1 := .neg ⟨(-944473296573929043/2361183241434822606848:ℚ),(-223330044160487951/590295810358705651712:ℚ)⟩ thresholdNode603
def thresholdNode605 : BoxExpr 1 := .add ⟨(2360238768138248677805/2361183241434822606848:ℚ),(590072480314545163761/590295810358705651712:ℚ)⟩ thresholdNode12 thresholdNode604
def thresholdNode606 : BoxExpr 1 := .sqrt ⟨(4721421915106847437639/4722366482869645213696:ℚ),(590184134772907823743/590295810358705651712:ℚ)⟩ thresholdNode605
def thresholdNode607 : BoxExpr 1 := .mul ⟨(6136314027516491943511/2361183241434822606848:ℚ),(1534095130721957951647/590295810358705651712:ℚ)⟩ thresholdNode601 thresholdNode606
def thresholdNode608 : BoxExpr 1 := .mul ⟨(5279605727848263348909/4722366482869645213696:ℚ),(5279605727848263348913/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode1
def thresholdNode609 : BoxExpr 1 := .add ⟨(12013700332420377423639/4722366482869645213696:ℚ),(3003425083105094355911/1180591620717411303424:ℚ)⟩ thresholdNode608 thresholdNode3
def thresholdNode610 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode5
def thresholdNode611 : BoxExpr 1 := .add ⟨(354177486215223391027/2361183241434822606848:ℚ),(708354972430446782055/4722366482869645213696:ℚ)⟩ thresholdNode0 thresholdNode610
def thresholdNode612 : BoxExpr 1 := .mul ⟨(26563311466141754327/1180591620717411303424:ℚ),(106253245864567017309/4722366482869645213696:ℚ)⟩ thresholdNode611 thresholdNode611
def thresholdNode613 : BoxExpr 1 := .mul ⟨(261382984826834862577/4722366482869645213696:ℚ),(261382984826834862581/4722366482869645213696:ℚ)⟩ thresholdNode612 thresholdNode9
def thresholdNode614 : BoxExpr 1 := .add ⟨(1534385414655901535777/590295810358705651712:ℚ),(12275083317247212286225/4722366482869645213696:ℚ)⟩ thresholdNode609 thresholdNode613
def thresholdNode615 : BoxExpr 1 := .var 0
def thresholdNode616 : BoxExpr 1 := .mul ⟨(1837437455427214557/4722366482869645213696:ℚ),(918718727713607279/2361183241434822606848:ℚ)⟩ thresholdNode615 thresholdNode615
def thresholdNode617 : BoxExpr 1 := .neg ⟨(-918718727713607279/2361183241434822606848:ℚ),(-1837437455427214557/4722366482869645213696:ℚ)⟩ thresholdNode616
def thresholdNode618 : BoxExpr 1 := .add ⟨(2360264522707108999569/2361183241434822606848:ℚ),(4720529045414217999139/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode617
def thresholdNode619 : BoxExpr 1 := .sqrt ⟨(4721447674757896157429/4722366482869645213696:ℚ),(2360723837378948078715/2361183241434822606848:ℚ)⟩ thresholdNode618
def thresholdNode620 : BoxExpr 1 := .mul ⟨(1534086876672742172101/590295810358705651712:ℚ),(3068173753345484344205/1180591620717411303424:ℚ)⟩ thresholdNode614 thresholdNode619
def thresholdNode621 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode1
def thresholdNode622 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode32
def thresholdNode623 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode621 thresholdNode622
def thresholdNode624 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode623 thresholdNode32
def thresholdNode625 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32
def thresholdNode626 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode625
def thresholdNode627 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode626 thresholdNode611
def thresholdNode628 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode611 thresholdNode626
def thresholdNode629 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode627 thresholdNode628
def thresholdNode630 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode629 thresholdNode9
def thresholdNode631 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode612 thresholdNode32
def thresholdNode632 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode630 thresholdNode631
def thresholdNode633 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode624 thresholdNode632
def thresholdNode634 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode633 thresholdNode619
def thresholdNode635 : BoxExpr 1 := .mul ⟨(2910959399051879963/147573952589676412928:ℚ),(93150700769660158817/4722366482869645213696:ℚ)⟩ thresholdNode12 thresholdNode615
def thresholdNode636 : BoxExpr 1 := .mul ⟨(2910959399051879963/147573952589676412928:ℚ),(93150700769660158817/4722366482869645213696:ℚ)⟩ thresholdNode615 thresholdNode12
def thresholdNode637 : BoxExpr 1 := .add ⟨(2910959399051879963/73786976294838206464:ℚ),(93150700769660158817/2361183241434822606848:ℚ)⟩ thresholdNode635 thresholdNode636
def thresholdNode638 : BoxExpr 1 := .neg ⟨(-93150700769660158817/2361183241434822606848:ℚ),(-2910959399051879963/73786976294838206464:ℚ)⟩ thresholdNode637
def thresholdNode639 : BoxExpr 1 := .add ⟨(-93150700769660158817/2361183241434822606848:ℚ),(-2910959399051879963/73786976294838206464:ℚ)⟩ thresholdNode32 thresholdNode638
def thresholdNode640 : BoxExpr 1 := .mul ⟨(4721447674757896157429/2361183241434822606848:ℚ),(2360723837378948078715/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode619
def thresholdNode641 : BoxExpr 1 := .inv ⟨(2361642734892126989771/4722366482869645213696:ℚ),(2361642734892126989773/4722366482869645213696:ℚ)⟩ thresholdNode640
def thresholdNode642 : BoxExpr 1 := .mul ⟨(-93168828180017758837/4722366482869645213696:ℚ),(-46584414090008879417/2361183241434822606848:ℚ)⟩ thresholdNode639 thresholdNode641
def thresholdNode643 : BoxExpr 1 := .mul ⟨(-121089196764864580717/2361183241434822606848:ℚ),(-242178393529729161425/4722366482869645213696:ℚ)⟩ thresholdNode614 thresholdNode642
def thresholdNode644 : BoxExpr 1 := .add ⟨(-121089196764864580717/2361183241434822606848:ℚ),(-242178393529729161425/4722366482869645213696:ℚ)⟩ thresholdNode634 thresholdNode643
def thresholdNode645 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode1
def thresholdNode646 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode32
def thresholdNode647 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode645 thresholdNode646
def thresholdNode648 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode0 thresholdNode32
def thresholdNode649 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode646 thresholdNode648
def thresholdNode650 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode647 thresholdNode649
def thresholdNode651 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode650 thresholdNode32
def thresholdNode652 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32
def thresholdNode653 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode652
def thresholdNode654 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode653 thresholdNode598
def thresholdNode655 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode653 thresholdNode653
def thresholdNode656 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode654 thresholdNode655
def thresholdNode657 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode598 thresholdNode653
def thresholdNode658 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode655 thresholdNode657
def thresholdNode659 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode656 thresholdNode658
def thresholdNode660 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode659 thresholdNode9
def thresholdNode661 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode654 thresholdNode657
def thresholdNode662 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode661 thresholdNode32
def thresholdNode663 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode660 thresholdNode662
def thresholdNode664 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode599 thresholdNode32
def thresholdNode665 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode662 thresholdNode664
def thresholdNode666 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode663 thresholdNode665
def thresholdNode667 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode651 thresholdNode666
def thresholdNode668 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode667 thresholdNode606
def thresholdNode669 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode645 thresholdNode648
def thresholdNode670 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode669 thresholdNode32
def thresholdNode671 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode661 thresholdNode9
def thresholdNode672 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode671 thresholdNode664
def thresholdNode673 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode670 thresholdNode672
def thresholdNode674 : BoxExpr 1 := .mul ⟨(45927035940963706679/2361183241434822606848:ℚ),(47223664828696452137/2361183241434822606848:ℚ)⟩ thresholdNode12 thresholdNode602
def thresholdNode675 : BoxExpr 1 := .mul ⟨(45927035940963706679/2361183241434822606848:ℚ),(47223664828696452137/2361183241434822606848:ℚ)⟩ thresholdNode602 thresholdNode12
def thresholdNode676 : BoxExpr 1 := .add ⟨(45927035940963706679/1180591620717411303424:ℚ),(47223664828696452137/1180591620717411303424:ℚ)⟩ thresholdNode674 thresholdNode675
def thresholdNode677 : BoxExpr 1 := .neg ⟨(-47223664828696452137/1180591620717411303424:ℚ),(-45927035940963706679/1180591620717411303424:ℚ)⟩ thresholdNode676
def thresholdNode678 : BoxExpr 1 := .add ⟨(-47223664828696452137/1180591620717411303424:ℚ),(-45927035940963706679/1180591620717411303424:ℚ)⟩ thresholdNode32 thresholdNode677
def thresholdNode679 : BoxExpr 1 := .mul ⟨(4721421915106847437639/2361183241434822606848:ℚ),(590184134772907823743/295147905179352825856:ℚ)⟩ thresholdNode5 thresholdNode606
def thresholdNode680 : BoxExpr 1 := .inv ⟨(2361630028303745658949/4722366482869645213696:ℚ),(2361655619801344256523/4722366482869645213696:ℚ)⟩ thresholdNode679
def thresholdNode681 : BoxExpr 1 := .mul ⟨(-47233112396026885131/2361183241434822606848:ℚ),(-5741965791018809501/295147905179352825856:ℚ)⟩ thresholdNode678 thresholdNode680
def thresholdNode682 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode673 thresholdNode681
def thresholdNode683 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode668 thresholdNode682
def thresholdNode684 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode602
def thresholdNode685 : BoxExpr 1 := .mul ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode12 thresholdNode12
def thresholdNode686 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode684 thresholdNode685
def thresholdNode687 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode602 thresholdNode32
def thresholdNode688 : BoxExpr 1 := .add ⟨(1/1:ℚ),(1/1:ℚ)⟩ thresholdNode685 thresholdNode687
def thresholdNode689 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode686 thresholdNode688
def thresholdNode690 : BoxExpr 1 := .neg ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode689
def thresholdNode691 : BoxExpr 1 := .add ⟨(-2/1:ℚ),(-2/1:ℚ)⟩ thresholdNode32 thresholdNode690
def thresholdNode692 : BoxExpr 1 := .mul ⟨(-2361655619801344256523/2361183241434822606848:ℚ),(-2361630028303745658949/2361183241434822606848:ℚ)⟩ thresholdNode691 thresholdNode680
def thresholdNode693 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode606
def thresholdNode694 : BoxExpr 1 := .mul ⟨(-47233112396026885131/1180591620717411303424:ℚ),(-5741965791018809501/147573952589676412928:ℚ)⟩ thresholdNode5 thresholdNode681
def thresholdNode695 : BoxExpr 1 := .add ⟨(-47233112396026885131/1180591620717411303424:ℚ),(-5741965791018809501/147573952589676412928:ℚ)⟩ thresholdNode693 thresholdNode694
def thresholdNode696 : BoxExpr 1 := .mul ⟨(4720477536276497355609/1180591620717411303424:ℚ),(2360289921258180655045/590295810358705651712:ℚ)⟩ thresholdNode679 thresholdNode679
def thresholdNode697 : BoxExpr 1 := .inv ⟨(1181038449857197272705/4722366482869645213696:ℚ),(590532023167972840849/2361183241434822606848:ℚ)⟩ thresholdNode696
def thresholdNode698 : BoxExpr 1 := .mul ⟨(-47252013201307408095/4722366482869645213696:ℚ),(-45953112036062055521/4722366482869645213696:ℚ)⟩ thresholdNode695 thresholdNode697
def thresholdNode699 : BoxExpr 1 := .neg ⟨(45953112036062055521/4722366482869645213696:ℚ),(47252013201307408095/4722366482869645213696:ℚ)⟩ thresholdNode698
def thresholdNode700 : BoxExpr 1 := .mul ⟨(-472520132013074081/1180591620717411303424:ℚ),(-893827379020727841/2361183241434822606848:ℚ)⟩ thresholdNode678 thresholdNode699
def thresholdNode701 : BoxExpr 1 := .add ⟨(-2362600660065370404685/2361183241434822606848:ℚ),(-1181261927841383193395/1180591620717411303424:ℚ)⟩ thresholdNode692 thresholdNode700
def thresholdNode702 : BoxExpr 1 := .mul ⟨(-12282452051481841122841/4722366482869645213696:ℚ),(-1535256596067249701875/590295810358705651712:ℚ)⟩ thresholdNode601 thresholdNode701
def thresholdNode703 : BoxExpr 1 := .add ⟨(-12282452051481841122841/4722366482869645213696:ℚ),(-1535256596067249701875/590295810358705651712:ℚ)⟩ thresholdNode682 thresholdNode702
def thresholdNode704 : BoxExpr 1 := .add ⟨(-12282452051481841122841/4722366482869645213696:ℚ),(-1535256596067249701875/590295810358705651712:ℚ)⟩ thresholdNode683 thresholdNode703
def thresholdCell3Out0 : TaylorCertificate1 :=
  { center := (7890174899319/400000184439400:ℚ), radius := (109828789469/400000184439400:ℚ)
    whole := thresholdNode607, centerValue := thresholdNode620, gradient := thresholdNode644, hessian := thresholdNode704 }
theorem thresholdCell3Out0_check : thresholdCell3Out0.check = true := by decide +kernel
theorem thresholdCell3Out0_lower_pos : 0 < thresholdCell3Out0.lower := by decide +kernel
theorem thresholdCell3Out0_positive (x : ℝ) (hx : (155606922197/8000003688788:ℝ) ≤ x ∧ x ≤ (1/50:ℝ)) :
    0 < thresholdNode607.eval (fun _ => x) := by
  apply thresholdCell3Out0.positive_sound thresholdCell3Out0_check thresholdCell3Out0_lower_pos x
  norm_num [thresholdCell3Out0]
  exact hx
def thresholdNode705 : BoxExpr 1 := .mul ⟨(31894474925558266639649/4722366482869645213696:ℚ),(3986895771248485077271/590295810358705651712:ℚ)⟩ thresholdNode607 thresholdNode607
def thresholdNode706 : BoxExpr 1 := .mul ⟨(45927035940963706679/1180591620717411303424:ℚ),(47223664828696452137/1180591620717411303424:ℚ)⟩ thresholdNode602 thresholdNode5
def thresholdNode707 : BoxExpr 1 := .add ⟨(1226518656658375010103/1180591620717411303424:ℚ),(1227815285546107755561/1180591620717411303424:ℚ)⟩ thresholdNode706 thresholdNode12
def thresholdNode708 : BoxExpr 1 := .inv ⟨(2270368501379637121969/2361183241434822606848:ℚ),(4545537297265527791021/4722366482869645213696:ℚ)⟩ thresholdNode707
def thresholdNode709 : BoxExpr 1 := .mul ⟨(84498877547412535956229/590295810358705651712:ℚ),(169176413095686585091777/1180591620717411303424:ℚ)⟩ thresholdNode121 thresholdNode708
def thresholdNode710 : BoxExpr 1 := .add ⟨(85089173357771241607941/590295810358705651712:ℚ),(170357004716403996395201/1180591620717411303424:ℚ)⟩ thresholdNode709 thresholdNode12
def thresholdNode711 : BoxExpr 1 := .sqrt ⟨(28348624669278885422223/2361183241434822606848:ℚ),(14181750678202711778193/1180591620717411303424:ℚ)⟩ thresholdNode710
def thresholdNode712 : BoxExpr 1 := .add ⟨(30709807910713708029071/2361183241434822606848:ℚ),(15362342298920123081617/1180591620717411303424:ℚ)⟩ thresholdNode711 thresholdNode12
def thresholdNode713 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode714 : BoxExpr 1 := .mul ⟨(30709807910713708029071/4722366482869645213696:ℚ),(15362342298920123081617/2361183241434822606848:ℚ)⟩ thresholdNode712 thresholdNode713
def thresholdNode715 : BoxExpr 1 := .add ⟨(31890399531431119332495/4722366482869645213696:ℚ),(15952638109278828733329/2361183241434822606848:ℚ)⟩ thresholdNode714 thresholdNode134
def thresholdNode716 : BoxExpr 1 := .mul ⟨(15938821685809273442379/2361183241434822606848:ℚ),(31893205310003329180735/4722366482869645213696:ℚ)⟩ thresholdNode605 thresholdNode715
def thresholdNode717 : BoxExpr 1 := .neg ⟨(-31893205310003329180735/4722366482869645213696:ℚ),(-15938821685809273442379/2361183241434822606848:ℚ)⟩ thresholdNode716
def thresholdNode718 : BoxExpr 1 := .add ⟨(634807777468729457/2361183241434822606848:ℚ),(8761399184666866705/2361183241434822606848:ℚ)⟩ thresholdNode705 thresholdNode717
def thresholdNode719 : BoxExpr 1 := .mul ⟨(1993426434578133456551/295147905179352825856:ℚ),(31894822953250135304879/4722366482869645213696:ℚ)⟩ thresholdNode620 thresholdNode620
def thresholdNode720 : BoxExpr 1 := .mul ⟨(2910959399051879963/73786976294838206464:ℚ),(93150700769660158817/2361183241434822606848:ℚ)⟩ thresholdNode615 thresholdNode5
def thresholdNode721 : BoxExpr 1 := .add ⟨(76697935693890086427/73786976294838206464:ℚ),(2454333942204482765665/2361183241434822606848:ℚ)⟩ thresholdNode720 thresholdNode12
def thresholdNode722 : BoxExpr 1 := .inv ⟨(4543135882010435310527/4722366482869645213696:ℚ),(2271567941005217655265/2361183241434822606848:ℚ)⟩ thresholdNode721
def thresholdNode723 : BoxExpr 1 := .mul ⟨(676348147610358525378051/4722366482869645213696:ℚ),(169087036902589631344625/1180591620717411303424:ℚ)⟩ thresholdNode121 thresholdNode722
def thresholdNode724 : BoxExpr 1 := .add ⟨(681070514093228170591747/4722366482869645213696:ℚ),(170267628523307042648049/1180591620717411303424:ℚ)⟩ thresholdNode723 thresholdNode12
def thresholdNode725 : BoxExpr 1 := .sqrt ⟨(56712120117525663252749/4722366482869645213696:ℚ),(1772253753672676976649/147573952589676412928:ℚ)⟩ thresholdNode724
def thresholdNode726 : BoxExpr 1 := .add ⟨(61434486600395308466445/4722366482869645213696:ℚ),(1919827706262353389577/147573952589676412928:ℚ)⟩ thresholdNode725 thresholdNode12
def thresholdNode727 : BoxExpr 1 := .inv ⟨(1/2:ℚ),(1/2:ℚ)⟩ thresholdNode5
def thresholdNode728 : BoxExpr 1 := .mul ⟨(15358621650098827116611/2361183241434822606848:ℚ),(1919827706262353389577/295147905179352825856:ℚ)⟩ thresholdNode726 thresholdNode727
def thresholdNode729 : BoxExpr 1 := .add ⟨(15948917460457532768323/2361183241434822606848:ℚ),(1993614682557191596041/295147905179352825856:ℚ)⟩ thresholdNode728 thresholdNode134
def thresholdNode730 : BoxExpr 1 := .mul ⟨(31885423712076587639077/4722366482869645213696:ℚ),(31885423712076587639095/4722366482869645213696:ℚ)⟩ thresholdNode618 thresholdNode729
def thresholdNode731 : BoxExpr 1 := .neg ⟨(-31885423712076587639095/4722366482869645213696:ℚ),(-31885423712076587639077/4722366482869645213696:ℚ)⟩ thresholdNode730
def thresholdNode732 : BoxExpr 1 := .add ⟨(9399241173547665721/4722366482869645213696:ℚ),(4699620586773832901/2361183241434822606848:ℚ)⟩ thresholdNode719 thresholdNode731
def thresholdNode733 : BoxExpr 1 := .mul ⟨(-314691963595236148729/2361183241434822606848:ℚ),(-629383927190472297433/4722366482869645213696:ℚ)⟩ thresholdNode644 thresholdNode620
def thresholdNode734 : BoxExpr 1 := .mul ⟨(-314691963595236148729/2361183241434822606848:ℚ),(-629383927190472297433/4722366482869645213696:ℚ)⟩ thresholdNode620 thresholdNode644
def thresholdNode735 : BoxExpr 1 := .add ⟨(-314691963595236148729/1180591620717411303424:ℚ),(-629383927190472297433/2361183241434822606848:ℚ)⟩ thresholdNode733 thresholdNode734
def thresholdNode736 : BoxExpr 1 := .mul ⟨(-157299612741650207713/590295810358705651712:ℚ),(-1258396901933201661689/4722366482869645213696:ℚ)⟩ thresholdNode639 thresholdNode729
def thresholdNode737 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode722
def thresholdNode738 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode739 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode615 thresholdNode32
def thresholdNode740 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode738 thresholdNode739
def thresholdNode741 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode740 thresholdNode32
def thresholdNode742 : BoxExpr 1 := .mul ⟨(1275579758942498676797/1180591620717411303424:ℚ),(5102319035769994707193/4722366482869645213696:ℚ)⟩ thresholdNode721 thresholdNode721
def thresholdNode743 : BoxExpr 1 := .inv ⟨(1092676929950402509993/1180591620717411303424:ℚ),(2185353859900805019989/2361183241434822606848:ℚ)⟩ thresholdNode742
def thresholdNode744 : BoxExpr 1 := .mul ⟨(1092676929950402509993/590295810358705651712:ℚ),(2185353859900805019989/1180591620717411303424:ℚ)⟩ thresholdNode741 thresholdNode743
def thresholdNode745 : BoxExpr 1 := .neg ⟨(-2185353859900805019989/1180591620717411303424:ℚ),(-1092676929950402509993/590295810358705651712:ℚ)⟩ thresholdNode744
def thresholdNode746 : BoxExpr 1 := .mul ⟨(-1301356660600680156562583/4722366482869645213696:ℚ),(-650678330300340078280397/2361183241434822606848:ℚ)⟩ thresholdNode121 thresholdNode745
def thresholdNode747 : BoxExpr 1 := .add ⟨(-1301356660600680156562583/4722366482869645213696:ℚ),(-650678330300340078280397/2361183241434822606848:ℚ)⟩ thresholdNode737 thresholdNode746
def thresholdNode748 : BoxExpr 1 := .add ⟨(-1301356660600680156562583/4722366482869645213696:ℚ),(-650678330300340078280397/2361183241434822606848:ℚ)⟩ thresholdNode747 thresholdNode32
def thresholdNode749 : BoxExpr 1 := .mul ⟨(56712120117525663252749/2361183241434822606848:ℚ),(1772253753672676976649/73786976294838206464:ℚ)⟩ thresholdNode5 thresholdNode725
def thresholdNode750 : BoxExpr 1 := .inv ⟨(98306786769372851307/2361183241434822606848:ℚ),(196613573538745702615/4722366482869645213696:ℚ)⟩ thresholdNode749
def thresholdNode751 : BoxExpr 1 := .mul ⟨(-54181390711054469401245/4722366482869645213696:ℚ),(-27090695355527234700447/2361183241434822606848:ℚ)⟩ thresholdNode748 thresholdNode750
def thresholdNode752 : BoxExpr 1 := .add ⟨(-54181390711054469401245/4722366482869645213696:ℚ),(-27090695355527234700447/2361183241434822606848:ℚ)⟩ thresholdNode751 thresholdNode32
def thresholdNode753 : BoxExpr 1 := .mul ⟨(-27090695355527234700623/4722366482869645213696:ℚ),(-27090695355527234700447/4722366482869645213696:ℚ)⟩ thresholdNode752 thresholdNode727
def thresholdNode754 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode755 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode754
def thresholdNode756 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode755
def thresholdNode757 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode756
def thresholdNode758 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode726 thresholdNode757
def thresholdNode759 : BoxExpr 1 := .add ⟨(-27090695355527234700623/4722366482869645213696:ℚ),(-27090695355527234700447/4722366482869645213696:ℚ)⟩ thresholdNode753 thresholdNode758
def thresholdNode760 : BoxExpr 1 := .add ⟨(-27090695355527234700623/4722366482869645213696:ℚ),(-27090695355527234700447/4722366482869645213696:ℚ)⟩ thresholdNode759 thresholdNode32
def thresholdNode761 : BoxExpr 1 := .mul ⟨(-13540077284358067268639/2361183241434822606848:ℚ),(-27080154568716134537095/4722366482869645213696:ℚ)⟩ thresholdNode618 thresholdNode760
def thresholdNode762 : BoxExpr 1 := .add ⟨(-14169275735324668099491/2361183241434822606848:ℚ),(-221394933364447939053/36893488147419103232:ℚ)⟩ thresholdNode736 thresholdNode761
def thresholdNode763 : BoxExpr 1 := .neg ⟨(221394933364447939053/36893488147419103232:ℚ),(14169275735324668099491/2361183241434822606848:ℚ)⟩ thresholdNode762
def thresholdNode764 : BoxExpr 1 := .add ⟨(6769945904067097900967/1180591620717411303424:ℚ),(6769945904067097901029/1180591620717411303424:ℚ)⟩ thresholdNode735 thresholdNode763
def thresholdNode765 : BoxExpr 1 := .mul ⟨(-7980087930005044889133/1180591620717411303424:ℚ),(-3989871019311456702997/590295810358705651712:ℚ)⟩ thresholdNode704 thresholdNode607
def thresholdNode766 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode673 thresholdNode606
def thresholdNode767 : BoxExpr 1 := .mul ⟨(-245550781413224967731/4722366482869645213696:ℚ),(-119403030231077939811/2361183241434822606848:ℚ)⟩ thresholdNode601 thresholdNode681
def thresholdNode768 : BoxExpr 1 := .add ⟨(-245550781413224967731/4722366482869645213696:ℚ),(-119403030231077939811/2361183241434822606848:ℚ)⟩ thresholdNode766 thresholdNode767
def thresholdNode769 : BoxExpr 1 := .mul ⟨(12076219564983949313/4722366482869645213696:ℚ),(12768002329206299023/4722366482869645213696:ℚ)⟩ thresholdNode768 thresholdNode768
def thresholdNode770 : BoxExpr 1 := .add ⟨(-31908275500455195607219/4722366482869645213696:ℚ),(-31906200152162447324953/4722366482869645213696:ℚ)⟩ thresholdNode765 thresholdNode769
def thresholdNode771 : BoxExpr 1 := .mul ⟨(-7980087930005044889133/1180591620717411303424:ℚ),(-3989871019311456702997/590295810358705651712:ℚ)⟩ thresholdNode607 thresholdNode704
def thresholdNode772 : BoxExpr 1 := .add ⟨(-31908275500455195607219/4722366482869645213696:ℚ),(-31906200152162447324953/4722366482869645213696:ℚ)⟩ thresholdNode769 thresholdNode771
def thresholdNode773 : BoxExpr 1 := .add ⟨(-31908275500455195607219/2361183241434822606848:ℚ),(-31906200152162447324953/2361183241434822606848:ℚ)⟩ thresholdNode770 thresholdNode772
def thresholdNode774 : BoxExpr 1 := .mul ⟨(-15952638109278828733329/1180591620717411303424:ℚ),(-31890399531431119332495/2361183241434822606848:ℚ)⟩ thresholdNode691 thresholdNode715
def thresholdNode775 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode708
def thresholdNode776 : BoxExpr 1 := .mul ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode12 thresholdNode5
def thresholdNode777 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode776 thresholdNode687
def thresholdNode778 : BoxExpr 1 := .add ⟨(2/1:ℚ),(2/1:ℚ)⟩ thresholdNode777 thresholdNode32
def thresholdNode779 : BoxExpr 1 := .mul ⟨(5096929331810490481563/4722366482869645213696:ℚ),(2553855793935904131567/2361183241434822606848:ℚ)⟩ thresholdNode707 thresholdNode707
def thresholdNode780 : BoxExpr 1 := .inv ⟨(545761658985489692781/590295810358705651712:ℚ),(4375329486981356822473/4722366482869645213696:ℚ)⟩ thresholdNode779
def thresholdNode781 : BoxExpr 1 := .mul ⟨(545761658985489692781/295147905179352825856:ℚ),(4375329486981356822473/2361183241434822606848:ℚ)⟩ thresholdNode778 thresholdNode780
def thresholdNode782 : BoxExpr 1 := .neg ⟨(-4375329486981356822473/2361183241434822606848:ℚ),(-545761658985489692781/295147905179352825856:ℚ)⟩ thresholdNode781
def thresholdNode783 : BoxExpr 1 := .mul ⟨(-1302732768976872857554335/4722366482869645213696:ℚ),(-1299982731498654399326577/4722366482869645213696:ℚ)⟩ thresholdNode121 thresholdNode782
def thresholdNode784 : BoxExpr 1 := .add ⟨(-1302732768976872857554335/4722366482869645213696:ℚ),(-1299982731498654399326577/4722366482869645213696:ℚ)⟩ thresholdNode775 thresholdNode783
def thresholdNode785 : BoxExpr 1 := .add ⟨(-1302732768976872857554335/4722366482869645213696:ℚ),(-1299982731498654399326577/4722366482869645213696:ℚ)⟩ thresholdNode784 thresholdNode32
def thresholdNode786 : BoxExpr 1 := .mul ⟨(28348624669278885422223/1180591620717411303424:ℚ),(14181750678202711778193/590295810358705651712:ℚ)⟩ thresholdNode5 thresholdNode711
def thresholdNode787 : BoxExpr 1 := .inv ⟨(196561991045354242827/4722366482869645213696:ℚ),(98332571062511334987/2361183241434822606848:ℚ)⟩ thresholdNode786
def thresholdNode788 : BoxExpr 1 := .mul ⟨(-27126455146072697426275/2361183241434822606848:ℚ),(-27054994032639879610017/2361183241434822606848:ℚ)⟩ thresholdNode785 thresholdNode787
def thresholdNode789 : BoxExpr 1 := .add ⟨(-27126455146072697426275/2361183241434822606848:ℚ),(-27054994032639879610017/2361183241434822606848:ℚ)⟩ thresholdNode788 thresholdNode32
def thresholdNode790 : BoxExpr 1 := .mul ⟨(-27126455146072697426275/4722366482869645213696:ℚ),(-27054994032639879610017/4722366482869645213696:ℚ)⟩ thresholdNode789 thresholdNode713
def thresholdNode791 : BoxExpr 1 := .mul ⟨(4/1:ℚ),(4/1:ℚ)⟩ thresholdNode5 thresholdNode5
def thresholdNode792 : BoxExpr 1 := .inv ⟨(1/4:ℚ),(1/4:ℚ)⟩ thresholdNode791
def thresholdNode793 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode792
def thresholdNode794 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode793
def thresholdNode795 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode712 thresholdNode794
def thresholdNode796 : BoxExpr 1 := .add ⟨(-27126455146072697426275/4722366482869645213696:ℚ),(-27054994032639879610017/4722366482869645213696:ℚ)⟩ thresholdNode790 thresholdNode795
def thresholdNode797 : BoxExpr 1 := .add ⟨(-27126455146072697426275/4722366482869645213696:ℚ),(-27054994032639879610017/4722366482869645213696:ℚ)⟩ thresholdNode796 thresholdNode32
def thresholdNode798 : BoxExpr 1 := .mul ⟨(526242801284895319857/2361183241434822606848:ℚ),(271264551460726974263/1180591620717411303424:ℚ)⟩ thresholdNode678 thresholdNode797
def thresholdNode799 : BoxExpr 1 := .add ⟨(-31379033417272762146801/2361183241434822606848:ℚ),(-31347870428509665383969/2361183241434822606848:ℚ)⟩ thresholdNode774 thresholdNode798
def thresholdNode800 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode782
def thresholdNode801 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode775 thresholdNode800
def thresholdNode802 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode5
def thresholdNode803 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode12 thresholdNode32
def thresholdNode804 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode802 thresholdNode803
def thresholdNode805 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode803 thresholdNode687
def thresholdNode806 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode804 thresholdNode805
def thresholdNode807 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode806 thresholdNode32
def thresholdNode808 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode807 thresholdNode780
def thresholdNode809 : BoxExpr 1 := .mul ⟨(1226518656658375010103/590295810358705651712:ℚ),(1227815285546107755561/590295810358705651712:ℚ)⟩ thresholdNode778 thresholdNode707
def thresholdNode810 : BoxExpr 1 := .mul ⟨(1226518656658375010103/590295810358705651712:ℚ),(1227815285546107755561/590295810358705651712:ℚ)⟩ thresholdNode707 thresholdNode778
def thresholdNode811 : BoxExpr 1 := .add ⟨(1226518656658375010103/295147905179352825856:ℚ),(1227815285546107755561/295147905179352825856:ℚ)⟩ thresholdNode809 thresholdNode810
def thresholdNode812 : BoxExpr 1 := .mul ⟨(85956270242458359201/73786976294838206464:ℚ),(5524500853442147817407/4722366482869645213696:ℚ)⟩ thresholdNode779 thresholdNode779
def thresholdNode813 : BoxExpr 1 := .inv ⟨(2018349330567639396379/2361183241434822606848:ℚ),(2026897762921566831915/2361183241434822606848:ℚ)⟩ thresholdNode812
def thresholdNode814 : BoxExpr 1 := .mul ⟨(16774932609403653174655/4722366482869645213696:ℚ),(8431894693753718020767/2361183241434822606848:ℚ)⟩ thresholdNode811 thresholdNode813
def thresholdNode815 : BoxExpr 1 := .neg ⟨(-8431894693753718020767/2361183241434822606848:ℚ),(-16774932609403653174655/4722366482869645213696:ℚ)⟩ thresholdNode814
def thresholdNode816 : BoxExpr 1 := .mul ⟨(-8431894693753718020767/1180591620717411303424:ℚ),(-16774932609403653174655/2361183241434822606848:ℚ)⟩ thresholdNode778 thresholdNode815
def thresholdNode817 : BoxExpr 1 := .add ⟨(-8431894693753718020767/1180591620717411303424:ℚ),(-16774932609403653174655/2361183241434822606848:ℚ)⟩ thresholdNode808 thresholdNode816
def thresholdNode818 : BoxExpr 1 := .neg ⟨(16774932609403653174655/2361183241434822606848:ℚ),(8431894693753718020767/1180591620717411303424:ℚ)⟩ thresholdNode817
def thresholdNode819 : BoxExpr 1 := .mul ⟨(4994653424998613480065871/4722366482869645213696:ℚ),(1255277523075599537697903/1180591620717411303424:ℚ)⟩ thresholdNode121 thresholdNode818
def thresholdNode820 : BoxExpr 1 := .add ⟨(4994653424998613480065871/4722366482869645213696:ℚ),(1255277523075599537697903/1180591620717411303424:ℚ)⟩ thresholdNode800 thresholdNode819
def thresholdNode821 : BoxExpr 1 := .add ⟨(4994653424998613480065871/4722366482869645213696:ℚ),(1255277523075599537697903/1180591620717411303424:ℚ)⟩ thresholdNode801 thresholdNode820
def thresholdNode822 : BoxExpr 1 := .add ⟨(4994653424998613480065871/4722366482869645213696:ℚ),(1255277523075599537697903/1180591620717411303424:ℚ)⟩ thresholdNode821 thresholdNode32
def thresholdNode823 : BoxExpr 1 := .mul ⟨(103947779716012094118807/2361183241434822606848:ℚ),(52276614569734509576115/1180591620717411303424:ℚ)⟩ thresholdNode822 thresholdNode787
def thresholdNode824 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode711
def thresholdNode825 : BoxExpr 1 := .mul ⟨(-27126455146072697426275/1180591620717411303424:ℚ),(-27054994032639879610017/1180591620717411303424:ℚ)⟩ thresholdNode5 thresholdNode788
def thresholdNode826 : BoxExpr 1 := .add ⟨(-27126455146072697426275/1180591620717411303424:ℚ),(-27054994032639879610017/1180591620717411303424:ℚ)⟩ thresholdNode824 thresholdNode825
def thresholdNode827 : BoxExpr 1 := .mul ⟨(2722853547448679731454077/4722366482869645213696:ℚ),(2725712075462463942323311/4722366482869645213696:ℚ)⟩ thresholdNode786 thresholdNode786
def thresholdNode828 : BoxExpr 1 := .inv ⟨(8181621749152253395/4722366482869645213696:ℚ),(2047552761277454179/1180591620717411303424:ℚ)⟩ thresholdNode827
def thresholdNode829 : BoxExpr 1 := .mul ⟨(-94093244714473544369/2361183241434822606848:ℚ),(-187493900275287932515/4722366482869645213696:ℚ)⟩ thresholdNode826 thresholdNode828
def thresholdNode830 : BoxExpr 1 := .neg ⟨(187493900275287932515/4722366482869645213696:ℚ),(94093244714473544369/2361183241434822606848:ℚ)⟩ thresholdNode829
def thresholdNode831 : BoxExpr 1 := .mul ⟨(-25956975951264442135973/2361183241434822606848:ℚ),(-12903426359610494152543/1180591620717411303424:ℚ)⟩ thresholdNode785 thresholdNode830
def thresholdNode832 : BoxExpr 1 := .add ⟨(38995401882373825991417/1180591620717411303424:ℚ),(9843297052531003855893/295147905179352825856:ℚ)⟩ thresholdNode823 thresholdNode831
def thresholdNode833 : BoxExpr 1 := .add ⟨(38995401882373825991417/1180591620717411303424:ℚ),(9843297052531003855893/295147905179352825856:ℚ)⟩ thresholdNode832 thresholdNode32
def thresholdNode834 : BoxExpr 1 := .mul ⟨(38995401882373825991417/2361183241434822606848:ℚ),(9843297052531003855893/590295810358705651712:ℚ)⟩ thresholdNode833 thresholdNode713
def thresholdNode835 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode789 thresholdNode794
def thresholdNode836 : BoxExpr 1 := .add ⟨(38995401882373825991417/2361183241434822606848:ℚ),(9843297052531003855893/590295810358705651712:ℚ)⟩ thresholdNode834 thresholdNode835
def thresholdNode837 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode5 thresholdNode32
def thresholdNode838 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode802 thresholdNode837
def thresholdNode839 : BoxExpr 1 := .mul ⟨(16/1:ℚ),(16/1:ℚ)⟩ thresholdNode791 thresholdNode791
def thresholdNode840 : BoxExpr 1 := .inv ⟨(1/16:ℚ),(1/16:ℚ)⟩ thresholdNode839
def thresholdNode841 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode838 thresholdNode840
def thresholdNode842 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode841
def thresholdNode843 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode32 thresholdNode842
def thresholdNode844 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode793 thresholdNode843
def thresholdNode845 : BoxExpr 1 := .neg ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode844
def thresholdNode846 : BoxExpr 1 := .mul ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode712 thresholdNode845
def thresholdNode847 : BoxExpr 1 := .add ⟨(0/1:ℚ),(0/1:ℚ)⟩ thresholdNode835 thresholdNode846
def thresholdNode848 : BoxExpr 1 := .add ⟨(38995401882373825991417/2361183241434822606848:ℚ),(9843297052531003855893/590295810358705651712:ℚ)⟩ thresholdNode836 thresholdNode847
def thresholdNode849 : BoxExpr 1 := .add ⟨(38995401882373825991417/2361183241434822606848:ℚ),(9843297052531003855893/590295810358705651712:ℚ)⟩ thresholdNode848 thresholdNode32
def thresholdNode850 : BoxExpr 1 := .mul ⟨(4872475465202609557627/295147905179352825856:ℚ),(19679145961514823447053/1180591620717411303424:ℚ)⟩ thresholdNode605 thresholdNode849
def thresholdNode851 : BoxExpr 1 := .add ⟨(39506046522905771780873/2361183241434822606848:ℚ),(4987602628243887605329/295147905179352825856:ℚ)⟩ thresholdNode798 thresholdNode850
def thresholdNode852 : BoxExpr 1 := .add ⟨(1015876638204126204259/295147905179352825856:ℚ),(8552950597441435458663/2361183241434822606848:ℚ)⟩ thresholdNode799 thresholdNode851
def thresholdNode853 : BoxExpr 1 := .neg ⟨(-8552950597441435458663/2361183241434822606848:ℚ),(-1015876638204126204259/295147905179352825856:ℚ)⟩ thresholdNode852
def thresholdNode854 : BoxExpr 1 := .add ⟨(-20230613048948315532941/1180591620717411303424:ℚ),(-40033213257795456959025/2361183241434822606848:ℚ)⟩ thresholdNode773 thresholdNode853
def thresholdCell3Out1 : TaylorCertificate1 :=
  { center := (7890174899319/400000184439400:ℚ), radius := (109828789469/400000184439400:ℚ)
    whole := thresholdNode718, centerValue := thresholdNode732, gradient := thresholdNode764, hessian := thresholdNode854 }
theorem thresholdCell3Out1_check : thresholdCell3Out1.check = true := by decide +kernel
theorem thresholdCell3Out1_lower_pos : 0 < thresholdCell3Out1.lower := by decide +kernel
theorem thresholdCell3Out1_positive (x : ℝ) (hx : (155606922197/8000003688788:ℝ) ≤ x ∧ x ≤ (1/50:ℝ)) :
    0 < thresholdNode718.eval (fun _ => x) := by
  apply thresholdCell3Out1.positive_sound thresholdCell3Out1_check thresholdCell3Out1_lower_pos x
  norm_num [thresholdCell3Out1]
  exact hx
theorem thresholdCell3_public (x : ℝ)
    (hx : (155606922197/8000003688788:ℝ) ≤ x ∧ x ≤ (1/50:ℝ)) : qc x < fA (43/20) x := by
  have hf := thresholdCell3Out0_positive x hx
  have hg := thresholdCell3Out1_positive x hx
  have hfa : thresholdNode607.eval (fun _ => x) = thresholdFA 1 x := by
    norm_num [thresholdNode0, thresholdNode1, thresholdNode595, thresholdNode3, thresholdNode596, thresholdNode5, thresholdNode597, thresholdNode598, thresholdNode599, thresholdNode9, thresholdNode600, thresholdNode601, thresholdNode12, thresholdNode602, thresholdNode603, thresholdNode604, thresholdNode605, thresholdNode606, thresholdNode607, BoxExpr.eval, thresholdFA, ftilde, pow_two, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  have hgap : thresholdNode718.eval (fun _ => x) =
      (thresholdNode607.eval (fun _ => x))^2 - (1-x^2)*(thresholdCapacity 3 x+1/4) := by
    norm_num [thresholdNode705, thresholdNode12, thresholdNode602, thresholdNode603, thresholdNode604, thresholdNode605, thresholdNode121, thresholdNode5, thresholdNode706, thresholdNode707, thresholdNode708, thresholdNode709, thresholdNode710, thresholdNode711, thresholdNode712, thresholdNode713, thresholdNode714, thresholdNode134, thresholdNode715, thresholdNode716, thresholdNode717, thresholdNode718, BoxExpr.eval, thresholdCapacity, Da, D5, beta5, eta5, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_comm, mul_left_comm, add_left_comm, mul_assoc, add_assoc] <;> ring
  rw [hfa] at hf
  rw [hgap, hfa] at hg
  refine threshold_positive_to_public 1 3 x ?_ ?_ ?_ hf hg
  · constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdFADomain] <;> constructor <;> linarith [hx.1,hx.2]
  · norm_num [thresholdCapacityDomain] <;> constructor <;> linarith [hx.1,hx.2]
theorem threshold_fgt_low_domain (x : ℝ)
    (hx : x ∈ Set.Icc (-(1/40:ℝ)) (1/50:ℝ)) : qc x < fA (43/20) x := by
  have hlo := hx.1
  by_cases h0 : x ≤ (-(155606922197/7688789844394:ℝ))
  · exact thresholdCell0_public x ⟨hlo, h0⟩
  have hlo : (-(155606922197/7688789844394:ℝ)) ≤ x := (lt_of_not_ge h0).le
  by_cases h1 : x ≤ (0:ℝ)
  · exact thresholdCell1_public x ⟨hlo, h1⟩
  have hlo : (0:ℝ) ≤ x := (lt_of_not_ge h1).le
  by_cases h2 : x ≤ (155606922197/8000003688788:ℝ)
  · exact thresholdCell2_public x ⟨hlo, h2⟩
  have hlo : (155606922197/8000003688788:ℝ) ≤ x := (lt_of_not_ge h2).le
  exact thresholdCell3_public x ⟨hlo,hx.2⟩
#print axioms threshold_fgt_low_domain
end GaussLocalMaxColoring.Certificate.ThresholdBranch1

open GaussLocalMaxColoring.Main

theorem solution (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (-(1/40):ℝ) (1/50:ℝ)) : qc ρ < fA (43/20) ρ  := by exact GaussLocalMaxColoring.Certificate.ThresholdBranch1.threshold_fgt_low_domain ρ hρ

#print axioms solution
