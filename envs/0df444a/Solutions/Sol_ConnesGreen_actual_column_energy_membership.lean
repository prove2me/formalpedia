-- Prove2me | solution 1 for ConnesGreen.actual_column_energy_membership
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T04:03:21.119656+00:00
-- url     : https://prove2.me/submissions/283efd4f-95a9-4033-88db-1809b2cd53eb

import Definitions.Def_ConnesGreen_canonical_model
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex MeasureTheory Set ConnesRZ ConnesRZFrontier
open scoped BigOperators InnerProductSpace lp ENNReal Classical Topology Interval ComplexConjugate
noncomputable section
namespace WeilDefect
attribute [local instance 1100] NormedSpace.complexToReal
open Filter Set Bornology
theorem hasDerivAt_realExpMode (freq : ℂ) (x : ℝ) :
    HasDerivAt (realExpMode freq) (freq * realExpMode freq x) x := by
  have hcomplex :
      HasDerivAt
        (fun z : ℂ => Complex.exp (z * freq))
        (freq * Complex.exp ((x : ℂ) * freq))
        (x : ℂ) := by
    have h :=
      hasDerivAt_exp_smul_const' (𝕂 := ℂ) (𝔸 := ℂ) freq (x : ℂ)
    simpa [← Complex.exp_eq_exp_ℂ, smul_eq_mul] using h
  change HasDerivAt
    (fun y : ℝ => Complex.exp ((y : ℂ) * freq))
    (freq * Complex.exp ((x : ℂ) * freq))
    x
  exact hcomplex.comp_ofReal

theorem iteratedDeriv_realExpMode (k : ℕ) (freq : ℂ) :
    iteratedDeriv k (realExpMode freq) =
      fun x : ℝ => freq ^ k * realExpMode freq x := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have h :=
        (hasDerivAt_realExpMode freq x).const_mul (freq ^ k)
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h.deriv

theorem contDiffAt_const_mul_realExpMode
    (k : ℕ) (c freq : ℂ) (x : ℝ) :
    ContDiffAt ℝ k (fun y : ℝ => c * realExpMode freq y) x := by
  change ContDiffAt ℝ k (fun y => c * Complex.exp (Complex.ofRealCLM y * freq)) x
  fun_prop

noncomputable def problemOneDenominator (freq : ℂ) : ℂ :=
  (1 / 4 : ℂ) - freq ^ 2

theorem problemOneL_realExpMode (freq : ℂ) (x : ℝ) :
    problemOneL (realExpMode freq) x =
      problemOneDenominator freq * realExpMode freq x := by
  simp [problemOneL, problemOneDenominator, iteratedDeriv_realExpMode]
  ring

theorem problemOneL_const_mul
    (c : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    problemOneL (fun y => c * f y) x =
      c * problemOneL f x := by
  simp [problemOneL, iteratedDeriv_const_mul_field]
  ring

theorem problemOneL_const_mul_realExpMode
    (c freq : ℂ) (x : ℝ) :
    problemOneL (fun y => c * realExpMode freq y) x =
      c * problemOneDenominator freq * realExpMode freq x := by
  rw [problemOneL_const_mul, problemOneL_realExpMode]
  ring

theorem problemOneL_add
    (f g : ℝ → ℂ) (x : ℝ)
    (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    problemOneL (f + g) x =
      problemOneL f x + problemOneL g x := by
  simp [problemOneL, iteratedDeriv_add hf hg]
  ring

theorem problemOneDenominator_problemOneFreq (gamma : ℂ) :
    problemOneDenominator (problemOneFreq gamma) =
      problemOneGreenDenom gamma := by
  simp [problemOneDenominator, problemOneFreq, problemOneGreenDenom, mul_pow, Complex.I_sq]

theorem dirichletRightReal_neg (t : ℝ) :
    dirichletRightReal t (-t) = 0 := by
  simp [dirichletRightReal]

theorem dirichletLeftReal_pos (t : ℝ) :
    dirichletLeftReal t t = 0 := by
  simp [dirichletLeftReal]

theorem dirichletRightReal_pos
    (t : ℝ) (ht : t ≠ 0) :
    dirichletRightReal t t = 1 := by
  have hs : Real.sinh t ≠ 0 := Real.sinh_ne_zero.mpr ht
  simp [dirichletRightReal, hs]

theorem dirichletLeftReal_neg
    (t : ℝ) (ht : t ≠ 0) :
    dirichletLeftReal t (-t) = 1 := by
  have hs : Real.sinh t ≠ 0 := Real.sinh_ne_zero.mpr ht
  simp [dirichletLeftReal, hs]

theorem dirichletRightBasis_neg (t : ℝ) :
    dirichletRightBasis t (-t) = 0 := by
  simp [dirichletRightBasis, dirichletRightReal_neg]

theorem dirichletLeftBasis_pos (t : ℝ) :
    dirichletLeftBasis t t = 0 := by
  simp [dirichletLeftBasis, dirichletLeftReal_pos]

theorem dirichletRightBasis_pos
    (t : ℝ) (ht : t ≠ 0) :
    dirichletRightBasis t t = 1 := by
  simp [dirichletRightBasis, dirichletRightReal_pos t ht]

theorem dirichletLeftBasis_neg
    (t : ℝ) (ht : t ≠ 0) :
    dirichletLeftBasis t (-t) = 1 := by
  simp [dirichletLeftBasis, dirichletLeftReal_neg t ht]

theorem hasDerivAt_dirichletRightReal
    (t x : ℝ) :
    HasDerivAt
      (dirichletRightReal t)
      (Real.cosh ((t + x) / 2) / (2 * Real.sinh t))
      x := by
  have hinner : HasDerivAt (fun y : ℝ => (t + y) / 2) (1 / 2 : ℝ) x := by
    simpa only [Pi.add_apply, id_eq, zero_add] using
      ((hasDerivAt_const x t).add (hasDerivAt_id x)).div_const 2
  have h := hinner.sinh.div_const (Real.sinh t)
  have he : Real.cosh ((t + x) / 2) * (1 / 2) / Real.sinh t =
      Real.cosh ((t + x) / 2) / (2 * Real.sinh t) := by ring
  rw [he] at h
  exact h

theorem hasDerivAt_dirichletRightReal_deriv
    (t x : ℝ) :
    HasDerivAt
      (fun y : ℝ =>
        Real.cosh ((t + y) / 2) / (2 * Real.sinh t))
      ((1 / 4 : ℝ) * dirichletRightReal t x)
      x := by
  have hinner : HasDerivAt (fun y : ℝ => (t + y) / 2) (1 / 2 : ℝ) x := by
    simpa only [Pi.add_apply, id_eq, zero_add] using
      ((hasDerivAt_const x t).add (hasDerivAt_id x)).div_const 2
  have h := hinner.cosh.div_const (2 * Real.sinh t)
  have he : (Real.sinh ((t + x) / 2) * (1 / 2)) / (2 * Real.sinh t) =
      (1 / 4 : ℝ) * dirichletRightReal t x := by
    unfold dirichletRightReal
    ring
  rw [he] at h
  exact h

theorem hasDerivAt_dirichletLeftReal
    (t x : ℝ) :
    HasDerivAt
      (dirichletLeftReal t)
      (-Real.cosh ((t - x) / 2) / (2 * Real.sinh t))
      x := by
  have hinner : HasDerivAt (fun y : ℝ => (t - y) / 2) (-1 / 2 : ℝ) x := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using
      ((hasDerivAt_const x t).sub (hasDerivAt_id x)).div_const 2
  have h := hinner.sinh.div_const (Real.sinh t)
  have he : Real.cosh ((t - x) / 2) * (-1 / 2) / Real.sinh t =
      -Real.cosh ((t - x) / 2) / (2 * Real.sinh t) := by ring
  rw [he] at h
  exact h

theorem hasDerivAt_dirichletLeftReal_deriv
    (t x : ℝ) :
    HasDerivAt
      (fun y : ℝ =>
        -Real.cosh ((t - y) / 2) / (2 * Real.sinh t))
      ((1 / 4 : ℝ) * dirichletLeftReal t x)
      x := by
  have hinner : HasDerivAt (fun y : ℝ => (t - y) / 2) (-1 / 2 : ℝ) x := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using
      ((hasDerivAt_const x t).sub (hasDerivAt_id x)).div_const 2
  have h := hinner.cosh.neg.div_const (2 * Real.sinh t)
  have he : (-(Real.sinh ((t - x) / 2) * (-1 / 2))) / (2 * Real.sinh t) =
      (1 / 4 : ℝ) * dirichletLeftReal t x := by
    unfold dirichletLeftReal
    ring
  rw [he] at h
  exact h

theorem hasDerivAt_dirichletRightBasis
    (t x : ℝ) :
    HasDerivAt
      (dirichletRightBasis t)
      ((Real.cosh ((t + x) / 2) / (2 * Real.sinh t) : ℝ) : ℂ)
      x := by
  change HasDerivAt
    (fun y : ℝ => (dirichletRightReal t y : ℂ))
    ((Real.cosh ((t + x) / 2) / (2 * Real.sinh t) : ℝ) : ℂ) x
  exact (hasDerivAt_dirichletRightReal t x).ofReal_comp

theorem hasDerivAt_dirichletLeftBasis
    (t x : ℝ) :
    HasDerivAt
      (dirichletLeftBasis t)
      ((-Real.cosh ((t - x) / 2) / (2 * Real.sinh t) : ℝ) : ℂ)
      x := by
  change HasDerivAt
    (fun y : ℝ => (dirichletLeftReal t y : ℂ))
    ((-Real.cosh ((t - x) / 2) / (2 * Real.sinh t) : ℝ) : ℂ) x
  exact (hasDerivAt_dirichletLeftReal t x).ofReal_comp

theorem iteratedDeriv_two_dirichletRightBasis
    (t x : ℝ) :
    iteratedDeriv 2 (dirichletRightBasis t) x =
      (1 / 4 : ℂ) * dirichletRightBasis t x := by
  have h1 :
      deriv (dirichletRightBasis t) =
        fun y : ℝ =>
          ((Real.cosh ((t + y) / 2) / (2 * Real.sinh t) : ℝ) : ℂ) := by
    funext y
    exact (hasDerivAt_dirichletRightBasis t y).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1]
  have h2 :=
    (hasDerivAt_dirichletRightReal_deriv t x).ofReal_comp
  simpa [dirichletRightBasis] using h2.deriv

theorem iteratedDeriv_two_dirichletLeftBasis
    (t x : ℝ) :
    iteratedDeriv 2 (dirichletLeftBasis t) x =
      (1 / 4 : ℂ) * dirichletLeftBasis t x := by
  have h1 :
      deriv (dirichletLeftBasis t) =
        fun y : ℝ =>
          ((-Real.cosh ((t - y) / 2) / (2 * Real.sinh t) : ℝ) : ℂ) := by
    funext y
    exact (hasDerivAt_dirichletLeftBasis t y).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1]
  have h2 :=
    (hasDerivAt_dirichletLeftReal_deriv t x).ofReal_comp
  simpa [dirichletLeftBasis] using h2.deriv

theorem problemOneL_dirichletRightBasis (t x : ℝ) :
    problemOneL (dirichletRightBasis t) x = 0 := by
  rw [problemOneL, iteratedDeriv_two_dirichletRightBasis]
  ring

theorem problemOneL_dirichletLeftBasis (t x : ℝ) :
    problemOneL (dirichletLeftBasis t) x = 0 := by
  rw [problemOneL, iteratedDeriv_two_dirichletLeftBasis]
  ring

theorem dirichletProblemOneColumn_pos
    (t : ℝ) (gamma : ℂ) (ht : t ≠ 0) :
    dirichletProblemOneColumn t gamma t = 0 := by
  simp [dirichletProblemOneColumn,
    dirichletRightBasis_pos t ht, dirichletLeftBasis_pos]

theorem dirichletProblemOneColumn_neg
    (t : ℝ) (gamma : ℂ) (ht : t ≠ 0) :
    dirichletProblemOneColumn t gamma (-t) = 0 := by
  simp [dirichletProblemOneColumn,
    dirichletRightBasis_neg, dirichletLeftBasis_neg t ht]

theorem contDiffAt_dirichletRightBasis
    (k : ℕ) (t x : ℝ) :
    ContDiffAt ℝ k (dirichletRightBasis t) x := by
  have hreal : ContDiffAt ℝ k (dirichletRightReal t) x := by
    unfold dirichletRightReal
    fun_prop
  have hcoe :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hreal
  change ContDiffAt ℝ k
    (Complex.ofRealCLM ∘ dirichletRightReal t) x
  exact hcoe

theorem contDiffAt_dirichletLeftBasis
    (k : ℕ) (t x : ℝ) :
    ContDiffAt ℝ k (dirichletLeftBasis t) x := by
  have hreal : ContDiffAt ℝ k (dirichletLeftReal t) x := by
    unfold dirichletLeftReal
    fun_prop
  have hcoe :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hreal
  change ContDiffAt ℝ k
    (Complex.ofRealCLM ∘ dirichletLeftReal t) x
  exact hcoe

theorem problemOneL_dirichletProblemOneColumn
    (t x : ℝ) (gamma : ℂ)
    (hden : problemOneGreenDenom gamma ≠ 0) :
    problemOneL (dirichletProblemOneColumn t gamma) x =
      realExpMode (problemOneFreq gamma) x := by
  let q := problemOneGreenQ gamma
  let f0 : ℝ → ℂ :=
    fun y => q * realExpMode (problemOneFreq gamma) y
  let fR : ℝ → ℂ :=
    fun y =>
      (-q * realExpMode (problemOneFreq gamma) t) * dirichletRightBasis t y
  let fL : ℝ → ℂ :=
    fun y =>
      (-q * realExpMode (problemOneFreq gamma) (-t)) * dirichletLeftBasis t y
  have hq :
      q * problemOneDenominator (problemOneFreq gamma) = 1 := by
    dsimp [q, problemOneGreenQ]
    rw [problemOneDenominator_problemOneFreq]
    exact inv_mul_cancel₀ hden
  have hf0 : ContDiffAt ℝ 2 f0 x := by
    simpa [f0] using
      contDiffAt_const_mul_realExpMode 2 q (problemOneFreq gamma) x
  have hfR : ContDiffAt ℝ 2 fR x := by
    exact (contDiff_const.contDiffAt.mul
      (contDiffAt_dirichletRightBasis 2 t x))
  have hfL : ContDiffAt ℝ 2 fL x := by
    exact (contDiff_const.contDiffAt.mul
      (contDiffAt_dirichletLeftBasis 2 t x))
  have hcol :
      dirichletProblemOneColumn t gamma = f0 + fR + fL := by
    funext y
    rfl
  rw [hcol]
  rw [problemOneL_add (f0 + fR) fL x (hf0.add hfR) hfL]
  rw [problemOneL_add f0 fR x hf0 hfR]
  have h0 :
      problemOneL f0 x =
        realExpMode (problemOneFreq gamma) x := by
    rw [show f0 =
      fun y => q * realExpMode (problemOneFreq gamma) y by rfl]
    rw [problemOneL_const_mul_realExpMode, hq, one_mul]
  have hR : problemOneL fR x = 0 := by
    rw [show fR =
      fun y => (-q * realExpMode (problemOneFreq gamma) t) *
        dirichletRightBasis t y by rfl]
    rw [problemOneL_const_mul, problemOneL_dirichletRightBasis, mul_zero]
  have hL : problemOneL fL x = 0 := by
    rw [show fL =
      fun y => (-q * realExpMode (problemOneFreq gamma) (-t)) *
        dirichletLeftBasis t y by rfl]
    rw [problemOneL_const_mul, problemOneL_dirichletLeftBasis, mul_zero]
  rw [h0, hR, hL, add_zero, add_zero]

theorem contDiff_dirichletProblemOneColumn
    (t : ℝ) (gamma : ℂ) :
    ContDiff ℝ 2 (dirichletProblemOneColumn t gamma) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  let q := problemOneGreenQ gamma
  let f0 : ℝ → ℂ :=
    fun y => q * realExpMode (problemOneFreq gamma) y
  let fR : ℝ → ℂ :=
    fun y =>
      (-q * realExpMode (problemOneFreq gamma) t) *
        dirichletRightBasis t y
  let fL : ℝ → ℂ :=
    fun y =>
      (-q * realExpMode (problemOneFreq gamma) (-t)) *
        dirichletLeftBasis t y
  have hf0 : ContDiffAt ℝ 2 f0 x := by
    simpa [f0] using
      contDiffAt_const_mul_realExpMode 2 q (problemOneFreq gamma) x
  have hfR : ContDiffAt ℝ 2 fR x := by
    exact
      (contDiff_const.contDiffAt.mul
        (contDiffAt_dirichletRightBasis 2 t x))
  have hfL : ContDiffAt ℝ 2 fL x := by
    exact
      (contDiff_const.contDiffAt.mul
        (contDiffAt_dirichletLeftBasis 2 t x))
  have hcol :
      dirichletProblemOneColumn t gamma = f0 + fR + fL := by
    funext y
    rfl
  rw [hcol]
  exact (hf0.add hfR).add hfL

end WeilDefect

namespace WeilDefect.ConnesNative
open WeilDefect
def dirichletTestAnalysis (t : ℝ) (γ : ℂ) (g : ℝ → ℂ) : ℂ :=
  ∫ x in -t..t,
    star (iteratedDeriv 1 (dirichletProblemOneColumn t γ) x) * iteratedDeriv 1 g x +
      (1 / 4 : ℂ) * star (dirichletProblemOneColumn t γ x) * g x

theorem dirichletTestAnalysis_eq_source (t : ℝ) (_ht : 0 < t)
    (γ : ℂ) (hden : problemOneGreenDenom γ ≠ 0)
    (g : ℝ → ℂ) (hg : SupportedTest t g) :
    dirichletTestAnalysis t γ g =
      ∫ x in -t..t, star (realExpMode (problemOneFreq γ) x) * g x := by
  let F := dirichletProblemOneColumn t γ
  let dF := iteratedDeriv 1 F
  let ddF := iteratedDeriv 2 F
  let dg := iteratedDeriv 1 g
  have hF : ContDiff ℝ 2 F := contDiff_dirichletProblemOneColumn t γ
  have hdF : Continuous dF := hF.continuous_iteratedDeriv 1 (by norm_num)
  have hddF : Continuous ddF := hF.continuous_iteratedDeriv 2 (by norm_num)
  have hgc : Continuous g := hg.1.1.continuous
  have hdg : Continuous dg := hg.1.1.continuous_iteratedDeriv 1 (by simp)
  have hgder : ∀ x, HasDerivAt g (dg x) x := by
    intro x
    simpa [dg, iteratedDeriv_one] using
      (hg.1.1.differentiable (by simp) x).hasDerivAt
  have hFder : ∀ x, HasDerivAt dF (ddF x) x := by
    intro x
    have h := (hF.differentiable_iteratedDeriv 1 (by norm_num) x).hasDerivAt
    simpa [dF, ddF, iteratedDeriv_succ] using h
  have hb : g t = 0 ∧ g (-t) = 0 := by
    constructor <;> by_contra hn
    · have h := hg.2 (subset_tsupport g hn)
      exact (lt_irrefl t) h.2
    · have h := hg.2 (subset_tsupport g hn)
      exact (lt_irrefl (-t)) h.1
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := -t) (b := t) (u := fun x => star (dF x)) (v := g)
    (u' := fun x => star (ddF x)) (v' := dg)
    hdF.star.continuousOn hgc.continuousOn
    (fun x _ => (hFder x).star) (fun x _ => hgder x)
    (hddF.star.intervalIntegrable (-t) t) (hdg.intervalIntegrable (-t) t)
  simp only [hb.1, hb.2, mul_zero, sub_zero, zero_sub] at hip
  have hmass : IntervalIntegrable (fun x => (1 / 4 : ℂ) * star (F x) * g x)
      volume (-t) t :=
    ((continuous_const.mul hF.continuous.star).mul hgc).intervalIntegrable _ _
  have hdd : IntervalIntegrable (fun x => star (ddF x) * g x) volume (-t) t :=
    (hddF.star.mul hgc).intervalIntegrable _ _
  have hgrad : IntervalIntegrable (fun x => star (dF x) * dg x) volume (-t) t :=
    (hdF.star.mul hdg).intervalIntegrable _ _
  have hsrc : ∀ x, star (realExpMode (problemOneFreq γ) x) * g x =
      -(star (ddF x) * g x) + (1 / 4 : ℂ) * star (F x) * g x := by
    intro x
    have h := (problemOneL_dirichletProblemOneColumn t x γ hden).symm
    change realExpMode (problemOneFreq γ) x = -ddF x + (1 / 4 : ℂ) * F x at h
    rw [h]
    simp
    ring
  unfold dirichletTestAnalysis
  change (∫ x in -t..t, star (dF x) * dg x + (1 / 4 : ℂ) * star (F x) * g x) = _
  rw [intervalIntegral.integral_add hgrad hmass, hip]
  rw [intervalIntegral.integral_congr (fun x _ => hsrc x)]
  simpa only [Pi.neg_apply, intervalIntegral.integral_neg] using
    (intervalIntegral.integral_add hdd.neg hmass).symm

theorem reflected_ordinate_denominator_ne_zero (z : ℂ) (hz : IsCriticalZero z) :
    problemOneGreenDenom (-I * (mirror z - 1 / 2)) ≠ 0 := by
  have hfactor : problemOneGreenDenom (-I * (mirror z - 1 / 2)) =
      star z * (1 - star z) := by
    simp [problemOneGreenDenom, mirror, mul_pow, Complex.I_sq]
    ring
  rw [hfactor]
  apply mul_ne_zero
  · intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith [hz.2.1]
  · intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith [hz.2.2]

theorem dirichlet_source_pairing_eq_analysis (t : ℝ) (ht : 0 < t)
    (γ : ℂ) (g : ℝ → ℂ) (hg : IsTest g) :
    (∫ x in -t..t, star (dirichletProblemOneColumn t γ x) * problemOneL g x) =
      dirichletTestAnalysis t γ g := by
  let F := dirichletProblemOneColumn t γ
  let dF := iteratedDeriv 1 F
  let dg := iteratedDeriv 1 g
  let ddg := iteratedDeriv 2 g
  have hF := contDiff_dirichletProblemOneColumn t γ
  have hdF : Continuous dF := hF.continuous_iteratedDeriv 1 (by norm_num)
  have hdg : Continuous dg := hg.1.continuous_iteratedDeriv 1 (by simp)
  have hddg : Continuous ddg := hg.1.continuous_iteratedDeriv 2 (by norm_cast <;> simp)
  have hFder : ∀ x, HasDerivAt F (dF x) x := by
    intro x
    simpa [dF, iteratedDeriv_one] using (hF.differentiable (by norm_num) x).hasDerivAt
  have hgder : ∀ x, HasDerivAt dg (ddg x) x := by
    intro x
    simpa [dg, ddg, iteratedDeriv_succ] using
      (hg.1.differentiable_iteratedDeriv 1 (by simp) x).hasDerivAt
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := -t) (b := t) (u := fun x => star (F x)) (v := dg)
    (u' := fun x => star (dF x)) (v' := ddg)
    hF.continuous.star.continuousOn hdg.continuousOn
    (fun x _ => (hFder x).star) (fun x _ => hgder x)
    (hdF.star.intervalIntegrable (-t) t) (hddg.intervalIntegrable (-t) t)
  have hb : F t = 0 ∧ F (-t) = 0 :=
    ⟨dirichletProblemOneColumn_pos t γ ht.ne', dirichletProblemOneColumn_neg t γ ht.ne'⟩
  simp only [hb.1, hb.2, star_zero, zero_mul, sub_zero, zero_sub] at hip
  have hmass : IntervalIntegrable (fun x => (1 / 4 : ℂ) * star (F x) * g x)
      volume (-t) t :=
    ((continuous_const.mul hF.continuous.star).mul hg.1.continuous).intervalIntegrable _ _
  have hdd : IntervalIntegrable (fun x => star (F x) * ddg x) volume (-t) t :=
    (hF.continuous.star.mul hddg).intervalIntegrable _ _
  have hgrad : IntervalIntegrable (fun x => star (dF x) * dg x) volume (-t) t :=
    (hdF.star.mul hdg).intervalIntegrable _ _
  have heq : ∀ x, star (F x) * problemOneL g x =
      -(star (F x) * ddg x) + (1 / 4 : ℂ) * star (F x) * g x := by
    intro x
    simp [problemOneL, ddg]
    ring
  rw [intervalIntegral.integral_congr (fun x _ => heq x)]
  have hadd := intervalIntegral.integral_add hdd.neg hmass
  simp only [Pi.neg_apply, intervalIntegral.integral_neg] at hadd
  rw [hadd, hip, neg_neg]
  exact (intervalIntegral.integral_add hgrad hmass).symm

theorem problemOneL_supported (t : ℝ) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    SupportedTest t (problemOneL g) := by
  have hd : iteratedDeriv 2 g = deriv (deriv g) := by
    simp [iteratedDeriv_succ, iteratedDeriv_one]
  have hs : tsupport (iteratedDeriv 2 g) ⊆ tsupport g := by
    rw [hd]
    exact tsupport_deriv_subset.trans tsupport_deriv_subset
  have hcompact : HasCompactSupport (iteratedDeriv 2 g) := by
    rw [hd]
    exact hg.1.2.deriv.deriv
  have hts : tsupport (problemOneL g) ⊆ tsupport g := by
    apply closure_minimal ?_ (isClosed_tsupport g)
    intro x hx
    by_contra hn
    have h0 := image_eq_zero_of_notMem_tsupport hn
    have h2 := image_eq_zero_of_notMem_tsupport (fun h => hn (hs h))
    exact hx (by simp [problemOneL, h0, h2])
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hder : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv 2 g) := by
      rw [hd]
      exact (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hg.1.1).2).2
    exact hder.neg.add (contDiff_const.mul hg.1.1)
  · exact hcompact.neg.add hg.1.2.mul_left
  · exact hts.trans hg.2

end WeilDefect.ConnesNative

namespace ConnesGreen
theorem sourceLift_inner (t : ℝ) (f : WindowL2 t) (h : Physical t) :
    ⟪sourceLift t f, h⟫_ℂ = (2 : ℂ) * ⟪f, (h : Ambient t) 1⟫_ℂ := by
  rw [sourceLift, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  simp [sourceLoad, PiLp.inner_apply, Fin.sum_univ_two, inner_smul_left,
    map_ofNat]

end ConnesGreen
namespace ConnesGreen
open WeilDefect WeilDefect.ConnesNative

/-- All continuous native sources and columns are valid L2 inputs on a finite
window, so the total extension used in the model is never invoked there. -/
theorem continuous_window_memLp (t : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    MemLp f 2 (windowMeasure t) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  exact (hf.norm.pow 2).integrableOn_Icc

theorem actual_source_memLp (t : ℝ) (ρ : CriticalZeros) :
    MemLp (actualGreenSource ρ) 2 (windowMeasure t) := by
  apply continuous_window_memLp
  unfold actualGreenSource realExpMode
  fun_prop

theorem greenColumn_energyDomain (t : ℝ) (ρ : CriticalZeros) :
    EnergyDomain t (greenColumn t ρ) := by
  have hc : ContDiff ℝ 2 (greenColumn t ρ) :=
    contDiff_dirichletProblemOneColumn t (actualGreenOrdinate ρ)
  exact ⟨continuous_window_memLp _ _ hc.continuous,
    continuous_window_memLp _ _ (hc.continuous_iteratedDeriv 1 (by norm_num))⟩

theorem supported_energyDomain (t : ℝ) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    EnergyDomain t g :=
  ⟨continuous_window_memLp _ _ hg.1.1.continuous,
    continuous_window_memLp _ _ (hg.1.1.continuous_iteratedDeriv 1 (by simp))⟩

theorem supported_L_memLp (t : ℝ) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    MemLp (problemOneL g) 2 (windowMeasure t) := by
  apply continuous_window_memLp
  exact (problemOneL_supported t g hg).1.1.continuous

theorem supported_energy_mem (t : ℝ) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    energyVector t g ∈ energySubspace t := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨⟨g, hg⟩, rfl⟩

theorem supported_Green_product_integrable (t : ℝ) (g : ℝ → ℂ)
    (hg : SupportedTest t g) (ρ : CriticalZeros) :
    IntervalIntegrable (fun x => star (greenColumn t ρ x) * problemOneL g x)
      volume (-t) t := by
  have hc : Continuous (greenColumn t ρ) :=
    (contDiff_dirichletProblemOneColumn t (actualGreenOrdinate ρ)).continuous
  exact (hc.star.mul (problemOneL_supported t g hg).1.1.continuous).intervalIntegrable _ _

end ConnesGreen

namespace ConnesGreen
open WeilDefect WeilDefect.ConnesNative

instance windowMeasure_finite (t : ℝ) : IsFiniteMeasure (windowMeasure t) := by
  unfold windowMeasure
  infer_instance

theorem windowL2_inner (t : ℝ) (f g : ℝ → ℂ)
    (hf : MemLp f 2 (windowMeasure t)) (hg : MemLp g 2 (windowMeasure t)) :
    ⟪windowL2 t f, windowL2 t g⟫_ℂ =
      ∫ x, star (f x) * g x ∂windowMeasure t := by
  simp only [windowL2, dif_pos hf, dif_pos hg, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, RCLike.inner_apply, mul_comm]

/-- A smooth dual probe of the energy graph; this is not a replacement for
the original admissible-test class or a change to the physical carrier. -/
def derivativeProbe (t : ℝ) (φ : ℝ → ℂ) : Ambient t :=
  WithLp.toLp 2 (fun i : Fin 2 =>
    if i = 0 then windowL2 t φ else (2 : ℂ) • windowL2 t (iteratedDeriv 1 φ))

theorem supported_endpoints_zero (t : ℝ) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    g t = 0 ∧ g (-t) = 0 := by
  constructor <;> by_contra hn
  · exact (lt_irrefl t) (hg.2 (subset_tsupport g hn)).2
  · exact (lt_irrefl (-t)) (hg.2 (subset_tsupport g hn)).1

theorem derivativeProbe_inner_energy (t : ℝ) (ht : 0 < t)
    (φ g : ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) (hg : SupportedTest t g) :
    ⟪derivativeProbe t φ, energyVector t g⟫_ℂ = 0 := by
  have hφd : Continuous (iteratedDeriv 1 φ) :=
    hφ.continuous_iteratedDeriv 1 (by norm_num)
  have hgd : Continuous (iteratedDeriv 1 g) :=
    hg.1.1.continuous_iteratedDeriv 1 (by simp)
  have hφlp := continuous_window_memLp t φ hφ.continuous
  have hφdlp := continuous_window_memLp t _ hφd
  have hglp := (supported_energyDomain t g hg).1
  have hgdlp := (supported_energyDomain t g hg).2
  have hb := supported_endpoints_zero t g hg
  have hip := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (a := -t) (b := t) (u := fun x => star (φ x)) (v := g)
    (u' := fun x => star (iteratedDeriv 1 φ x)) (v' := iteratedDeriv 1 g)
    hφ.continuous.star.continuousOn hg.1.1.continuous.continuousOn
    (fun x _ => by simpa [iteratedDeriv_one] using
      (hφ.differentiable (by norm_num) x).hasDerivAt.star)
    (fun x _ => by simpa [iteratedDeriv_one] using
      (hg.1.1.differentiable (by simp) x).hasDerivAt)
    (hφd.star.intervalIntegrable _ _) (hgd.intervalIntegrable _ _)
  simp only [hb.1, hb.2, mul_zero, sub_zero] at hip
  have hi1 : Integrable (fun x => star (φ x) * iteratedDeriv 1 g x)
      (windowMeasure t) := (hφ.continuous.star.mul hgd).integrableOn_Icc
  have hi2 : Integrable (fun x => star (iteratedDeriv 1 φ x) * g x)
      (windowMeasure t) := (hφd.star.mul hg.1.1.continuous).integrableOn_Icc
  have hsum : (∫ x, star (φ x) * iteratedDeriv 1 g x +
      star (iteratedDeriv 1 φ x) * g x ∂windowMeasure t) = 0 := by
    unfold windowMeasure
    rw [integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by linarith : -t ≤ t)]
    convert hip using 1
    congr 1
    ext x
    ring
  have hinner : ⟪derivativeProbe t φ, energyVector t g⟫_ℂ =
      ⟪windowL2 t φ, windowL2 t (iteratedDeriv 1 g)⟫_ℂ +
      ⟪windowL2 t (iteratedDeriv 1 φ), windowL2 t g⟫_ℂ := by
    simp [derivativeProbe, energyVector, PiLp.inner_apply, Fin.sum_univ_two,
      inner_smul_left, inner_smul_right, map_ofNat]
  rw [hinner, windowL2_inner t φ _ hφlp hgdlp,
    windowL2_inner t _ g hφdlp hglp, ← integral_add hi1 hi2]
  exact hsum

/-- Integration by parts is a closed linear constraint, so it survives the
span and completion in the exact published energySubspace definition. -/
theorem derivativeProbe_inner_physical (t : ℝ) (ht : 0 < t)
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) (h : Physical t) :
    ⟪derivativeProbe t φ, (h : Ambient t)⟫_ℂ = 0 := by
  let K : Submodule ℂ (Ambient t) := (ℂ ∙ derivativeProbe t φ)ᗮ
  have hs : energySubspace t ≤ K := by
    unfold energySubspace
    apply Submodule.topologicalClosure_minimal _ _
      (ℂ ∙ derivativeProbe t φ).isClosed_orthogonal
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right).mpr
      (derivativeProbe_inner_energy t ht φ g hφ hg)
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right).mp (hs h.2)

/-- RG-1a closed on the prescribed carrier. Smooth probes are used only to
test the first coordinate; the physical carrier is never replaced. -/
theorem energyGraph_no_derivative_only (t : ℝ) (ht : 0 < t) :
    ∀ h : Physical t, (h : Ambient t) 1 = 0 → h = 0 := by
  intro h hh
  have hfirst : (h : Ambient t) 0 = 0 := by
    apply (SchwartzMap.denseRange_toLpCLM (F := ℂ) (μ := windowMeasure t)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).eq_zero_of_inner_right ℂ
    intro φ
    have hip := derivativeProbe_inner_physical t ht φ (φ.smooth 1) h
    have hlp : windowL2 t φ = φ.toLp 2 (windowMeasure t) := by
      simp only [windowL2, dif_pos (φ.memLp 2 (windowMeasure t)), SchwartzMap.toLp]
    simpa [derivativeProbe, PiLp.inner_apply, Fin.sum_univ_two, hh, hlp] using hip
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [hfirst, hh]

end ConnesGreen

namespace ConnesGreen
open WeilDefect WeilDefect.ConnesNative

theorem windowL2_L (t : ℝ) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    windowL2 t (problemOneL g) = -windowL2 t (iteratedDeriv 2 g) +
      (1 / 4 : ℂ) • windowL2 t g := by
  have hf := continuous_window_memLp t _
    (hg.1.1.continuous_iteratedDeriv 2 (by norm_cast <;> simp))
  have hh := (supported_energyDomain t g hg).1
  change windowL2 t (-iteratedDeriv 2 g + (1 / 4 : ℂ) • g) = _
  simp only [windowL2, dif_pos hf, dif_pos hh,
    dif_pos (hf.neg.add (hh.const_smul (1 / 4 : ℂ))),
    MemLp.toLp_add, MemLp.toLp_neg, MemLp.toLp_const_smul]
  rfl

theorem sourceLoad_L_sub_energy_orthogonal (t : ℝ) (ht : 0 < t)
    (g : ℝ → ℂ) (hg : SupportedTest t g) :
    sourceLoad t (windowL2 t (problemOneL g)) - energyVector t g ∈ (energySubspace t)ᗮ := by
  let D := sourceLoad t (windowL2 t (problemOneL g)) - energyVector t g
  have hi : ∀ u : ℝ → ℂ, SupportedTest t u → ⟪energyVector t u, D⟫_ℂ = 0 := by
    intro u hu
    have hder : ContDiff ℝ 1 (iteratedDeriv 1 g) :=
      (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv (n := 1)).mp
        (hg.1.1.of_le (by norm_cast <;> simp)) |>.2
    have hip := derivativeProbe_inner_energy t ht (iteratedDeriv 1 g) u hder hu
    have hid : iteratedDeriv 1 (iteratedDeriv 1 g) = iteratedDeriv 2 g := by
      simp [iteratedDeriv_succ, iteratedDeriv_one]
    have hip' : ⟪windowL2 t (iteratedDeriv 1 g), windowL2 t (iteratedDeriv 1 u)⟫_ℂ +
        ⟪windowL2 t (iteratedDeriv 2 g), windowL2 t u⟫_ℂ = 0 := by
      simpa [derivativeProbe, energyVector, PiLp.inner_apply, Fin.sum_univ_two,
        inner_smul_left, inner_smul_right, map_ofNat,
        iteratedDeriv_succ, iteratedDeriv_one] using hip
    have hc := congrArg (starRingEnd ℂ) hip'
    simp only [map_add, map_zero, inner_conj_symm] at hc
    have hex : ⟪energyVector t u, D⟫_ℂ =
        -(⟪windowL2 t (iteratedDeriv 1 u), windowL2 t (iteratedDeriv 1 g)⟫_ℂ +
          ⟪windowL2 t u, windowL2 t (iteratedDeriv 2 g)⟫_ℂ) := by
      simp [D, sourceLoad, energyVector, PiLp.inner_apply, Fin.sum_univ_two,
        inner_sub_right, windowL2_L t g hg, inner_add_right, inner_neg_right,
        inner_smul_left, inner_smul_right, map_ofNat]
      ring
    rw [hex, hc, neg_zero]
  have hs : energySubspace t ≤ (ℂ ∙ D)ᗮ := by
    unfold energySubspace
    apply Submodule.topologicalClosure_minimal _ _ (ℂ ∙ D).isClosed_orthogonal
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, hu⟩, rfl⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    exact hi u hu
  apply (energySubspace t).mem_orthogonal D |>.mpr
  intro u hu
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hs hu)

/-- The computed source embedding of Lg is exactly the original energy image
of g, in the same completed physical carrier. -/
theorem sourceEmbed_L (t : ℝ) (ht : 0 < t) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    sourceEmbed t (problemOneL g) =
      (⟨energyVector t g, supported_energy_mem t g hg⟩ : Physical t) := by
  let e : Physical t := ⟨energyVector t g, supported_energy_mem t g hg⟩
  have hz := (energySubspace t).orthogonalProjectionOnto_eq_zero_iff.mpr
    (sourceLoad_L_sub_energy_orthogonal t ht g hg)
  change (energySubspace t).orthogonalProjectionOnto
    (sourceLoad t (windowL2 t (problemOneL g)) - (e : Ambient t)) = 0 at hz
  rw [map_sub, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] at hz
  exact sub_eq_zero.mp hz

theorem source_pairing_eq_original_integral (t : ℝ) (ht : 0 < t)
    (g : ℝ → ℂ) (hg : SupportedTest t g) (ρ : CriticalZeros) :
    ⟪sourceEmbed t (actualGreenSource ρ), sourceEmbed t (problemOneL g)⟫_ℂ =
      ∫ x in -t..t, star (greenColumn t ρ x) * problemOneL g x := by
  rw [sourceEmbed_L t ht g hg]
  change ⟪sourceLift t (windowL2 t (actualGreenSource ρ)),
    (⟨energyVector t g, supported_energy_mem t g hg⟩ : Physical t)⟫_ℂ = _
  rw [sourceLift_inner]
  have he : (energyVector t g) 1 = (1 / 2 : ℂ) • windowL2 t g := by
    simp [energyVector]
  rw [he, inner_smul_right]
  have hm : (2 : ℂ) * ((1 / 2 : ℂ) *
      ⟪windowL2 t (actualGreenSource ρ), windowL2 t g⟫_ℂ) =
      ⟪windowL2 t (actualGreenSource ρ), windowL2 t g⟫_ℂ := by ring
  rw [hm, windowL2_inner t _ _ (actual_source_memLp t ρ)
    (supported_energyDomain t g hg).1]
  unfold windowMeasure
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -t ≤ t)]
  have hd : problemOneGreenDenom (actualGreenOrdinate ρ) ≠ 0 :=
    reflected_ordinate_denominator_ne_zero ρ.1 ρ.2
  rw [greenColumn, dirichlet_source_pairing_eq_analysis t ht _ g hg.1,
    dirichletTestAnalysis_eq_source t ht (actualGreenOrdinate ρ) hd g hg]
  rfl

/-- RG-3 closed independently of the remaining RG-2 column membership and
metric theorem. The source representative is exactly Lg. -/
theorem supported_source_pairing (t : ℝ) (ht : 0 < t) : TestPairing t := by
  intro g hg
  exact ⟨supported_energyDomain t g hg, supported_L_memLp t g hg,
    fun ρ => ⟨supported_Green_product_integrable t g hg ρ,
      source_pairing_eq_original_integral t ht g hg ρ⟩⟩

end ConnesGreen

namespace WeilDefect
noncomputable def problemOneDirichletEnergyComplex
    (t : ℝ) (gamma : ℂ) : ℂ :=
  ∫ x in -t..t,
    star (iteratedDeriv 1 (dirichletProblemOneColumn t gamma) x) *
        iteratedDeriv 1 (dirichletProblemOneColumn t gamma) x
      + (1 / 4 : ℂ) *
        star (dirichletProblemOneColumn t gamma x) *
        dirichletProblemOneColumn t gamma x


theorem problemOneDirichletEnergyComplex_eq_ofReal
    (t : ℝ) (gamma : ℂ) :
    problemOneDirichletEnergyComplex t gamma
      =
    (problemOneDirichletEnergy t gamma : ℂ) := by
  unfold problemOneDirichletEnergyComplex problemOneDirichletEnergy
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x hx
  have hstar (z : ℂ) :
      star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    simpa [RCLike.star_def] using Complex.conj_mul' z
  change
    star (iteratedDeriv 1 (dirichletProblemOneColumn t gamma) x) *
          iteratedDeriv 1 (dirichletProblemOneColumn t gamma) x
        + (1 / 4 : ℂ) *
          star (dirichletProblemOneColumn t gamma x) *
          dirichletProblemOneColumn t gamma x
      =
    ((‖iteratedDeriv 1 (dirichletProblemOneColumn t gamma) x‖ ^ 2
        + (1 / 4 : ℝ) *
          ‖dirichletProblemOneColumn t gamma x‖ ^ 2 : ℝ) : ℂ)
  rw [hstar (iteratedDeriv 1 (dirichletProblemOneColumn t gamma) x)]
  rw [mul_assoc, hstar (dirichletProblemOneColumn t gamma x)]
  push_cast
  rfl


end WeilDefect

namespace ConnesGreen
open WeilDefect WeilDefect.ConnesNative
theorem windowL2_L_of_contDiff (t : ℝ) (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) :
    windowL2 t (problemOneL g) = -windowL2 t (iteratedDeriv 2 g) +
      (1 / 4 : ℂ) • windowL2 t g := by
  have hf := continuous_window_memLp t _
    (hg.continuous_iteratedDeriv 2 (by simp))
  have hh := continuous_window_memLp t g hg.continuous
  change windowL2 t (-iteratedDeriv 2 g + (1 / 4 : ℂ) • g) = _
  simp only [windowL2, dif_pos hf, dif_pos hh,
    dif_pos (hf.neg.add (hh.const_smul (1 / 4 : ℂ))),
    MemLp.toLp_add, MemLp.toLp_neg, MemLp.toLp_const_smul]
  rfl

theorem sourceLoad_L_sub_energy_orthogonal_of_contDiff (t : ℝ) (ht : 0 < t)
    (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) :
    sourceLoad t (windowL2 t (problemOneL g)) - energyVector t g ∈ (energySubspace t)ᗮ := by
  let D := sourceLoad t (windowL2 t (problemOneL g)) - energyVector t g
  have hi : ∀ u : ℝ → ℂ, SupportedTest t u → ⟪energyVector t u, D⟫_ℂ = 0 := by
    intro u hu
    have hder : ContDiff ℝ 1 (iteratedDeriv 1 g) :=
      (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv (n := 1)).mp
        hg |>.2
    have hip := derivativeProbe_inner_energy t ht (iteratedDeriv 1 g) u hder hu
    have hid : iteratedDeriv 1 (iteratedDeriv 1 g) = iteratedDeriv 2 g := by
      simp [iteratedDeriv_succ, iteratedDeriv_one]
    have hip' : ⟪windowL2 t (iteratedDeriv 1 g), windowL2 t (iteratedDeriv 1 u)⟫_ℂ +
        ⟪windowL2 t (iteratedDeriv 2 g), windowL2 t u⟫_ℂ = 0 := by
      simpa [derivativeProbe, energyVector, PiLp.inner_apply, Fin.sum_univ_two,
        inner_smul_left, inner_smul_right, map_ofNat,
        iteratedDeriv_succ, iteratedDeriv_one] using hip
    have hc := congrArg (starRingEnd ℂ) hip'
    simp only [map_add, map_zero, inner_conj_symm] at hc
    have hex : ⟪energyVector t u, D⟫_ℂ =
        -(⟪windowL2 t (iteratedDeriv 1 u), windowL2 t (iteratedDeriv 1 g)⟫_ℂ +
          ⟪windowL2 t u, windowL2 t (iteratedDeriv 2 g)⟫_ℂ) := by
      simp [D, sourceLoad, energyVector, PiLp.inner_apply, Fin.sum_univ_two,
        inner_sub_right, windowL2_L_of_contDiff t g hg, inner_add_right, inner_neg_right,
        inner_smul_left, inner_smul_right, map_ofNat]
      ring
    rw [hex, hc, neg_zero]
  have hs : energySubspace t ≤ (ℂ ∙ D)ᗮ := by
    unfold energySubspace
    apply Submodule.topologicalClosure_minimal _ _ (ℂ ∙ D).isClosed_orthogonal
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, hu⟩, rfl⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    exact hi u hu
  apply (energySubspace t).mem_orthogonal D |>.mpr
  intro u hu
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hs hu)


theorem greenColumn_L (t : ℝ) (ρ : CriticalZeros) :
    problemOneL (greenColumn t ρ) = actualGreenSource ρ := by
  funext x
  exact problemOneL_dirichletProblemOneColumn t x _
    (reflected_ordinate_denominator_ne_zero ρ.1 ρ.2)

theorem greenColumn_weak_equation (t : ℝ) (ht : 0 < t) (ρ : CriticalZeros) :
    sourceLoad t (windowL2 t (actualGreenSource ρ)) - energyVector t (greenColumn t ρ)
      ∈ (energySubspace t)ᗮ := by
  rw [← greenColumn_L t ρ]
  exact sourceLoad_L_sub_energy_orthogonal_of_contDiff t ht _
    (contDiff_dirichletProblemOneColumn t (actualGreenOrdinate ρ))

theorem greenColumn_energy_inner (t : ℝ) (ht : 0 < t) (ρ : CriticalZeros) :
    ⟪energyVector t (greenColumn t ρ), energyVector t (greenColumn t ρ)⟫_ℂ =
      (problemOneDirichletEnergy t (actualGreenOrdinate ρ) : ℂ) := by
  let F := greenColumn t ρ
  have hc : ContDiff ℝ 2 F := contDiff_dirichletProblemOneColumn t _
  have hfd := hc.continuous_iteratedDeriv 1 (by norm_num)
  have hf := (greenColumn_energyDomain t ρ).1
  have hdf := (greenColumn_energyDomain t ρ).2
  have hi1 : Integrable (fun x => star (iteratedDeriv 1 F x) * iteratedDeriv 1 F x)
      (windowMeasure t) := (hfd.star.mul hfd).integrableOn_Icc
  have hi2 : Integrable (fun x => star (F x) * F x) (windowMeasure t) :=
    (hc.continuous.star.mul hc.continuous).integrableOn_Icc
  have he : ⟪energyVector t F, energyVector t F⟫_ℂ =
      ⟪windowL2 t (iteratedDeriv 1 F), windowL2 t (iteratedDeriv 1 F)⟫_ℂ +
      (1 / 4 : ℂ) * ⟪windowL2 t F, windowL2 t F⟫_ℂ := by
    simp only [energyVector, PiLp.inner_apply, Fin.sum_univ_two,
      ite_true, (by decide : (1 : Fin 2) ≠ 0), ite_false,
      inner_smul_left, inner_smul_right, map_div₀, map_one, map_ofNat]
    ring
  rw [he, windowL2_inner t _ _ hdf hdf, windowL2_inner t _ _ hf hf,
    ← integral_const_mul, ← integral_add hi1 (hi2.const_mul (1 / 4 : ℂ))]
  rw [← problemOneDirichletEnergyComplex_eq_ofReal]
  unfold windowMeasure problemOneDirichletEnergyComplex
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -t ≤ t)]
  congr 1
  ext x
  dsimp [F, greenColumn]
  ring

theorem greenColumn_energy_norm (t : ℝ) (ht : 0 < t) (ρ : CriticalZeros) :
    ‖energyVector t (greenColumn t ρ)‖ ^ 2 =
      problemOneDirichletEnergy t (actualGreenOrdinate ρ) := by
  have h := congrArg Complex.re (greenColumn_energy_inner t ht ρ)
  change RCLike.re ⟪energyVector t (greenColumn t ρ), energyVector t (greenColumn t ρ)⟫_ℂ =
    problemOneDirichletEnergy t (actualGreenOrdinate ρ) at h
  rw [← @norm_sq_eq_re_inner ℂ _ _ _] at h
  exact h

theorem greenColumn_projection_iff_membership (t : ℝ) (ht : 0 < t)
    (ρ : CriticalZeros) :
    (sourceEmbed t (actualGreenSource ρ) : Ambient t) = energyVector t (greenColumn t ρ) ↔
      energyVector t (greenColumn t ρ) ∈ energySubspace t := by
  constructor
  · intro h
    rw [← h]
    exact (sourceEmbed t (actualGreenSource ρ)).2
  · intro hm
    let e : Physical t := ⟨energyVector t (greenColumn t ρ), hm⟩
    have hz := (energySubspace t).orthogonalProjectionOnto_eq_zero_iff.mpr
      (greenColumn_weak_equation t ht ρ)
    change (energySubspace t).orthogonalProjectionOnto
      (sourceLoad t (windowL2 t (actualGreenSource ρ)) - (e : Ambient t)) = 0 at hz
    rw [map_sub, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] at hz
    exact congrArg (fun x : Physical t => (x : Ambient t)) (sub_eq_zero.mp hz)

theorem columnRealization_iff_membership (t : ℝ) (ht : 0 < t) :
    ColumnRealization t ↔
      ∀ ρ : CriticalZeros, energyVector t (greenColumn t ρ) ∈ energySubspace t := by
  constructor
  · intro hc ρ
    exact (hc ρ).2.2.1
  · intro hm ρ
    have hp := (greenColumn_projection_iff_membership t ht ρ).mpr (hm ρ)
    refine ⟨actual_source_memLp t ρ, greenColumn_energyDomain t ρ, hm ρ, hp, ?_⟩
    change ‖(sourceEmbed t (actualGreenSource ρ) : Ambient t)‖ ^ 2 = _
    rw [hp]
    exact greenColumn_energy_norm t ht ρ


end ConnesGreen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex MeasureTheory Set Filter ConnesRZ ConnesRZFrontier
open scoped BigOperators InnerProductSpace lp ENNReal Classical Topology
noncomputable section
namespace ConnesGreen
open WeilDefect WeilDefect.ConnesNative

def windowCutoff (t ε x : ℝ) : ℝ :=
  Real.smoothTransition ((t - x) / ε - 1) * Real.smoothTransition ((t + x) / ε - 1)

def cutoffColumn (t ε : ℝ) (F : ℝ → ℂ) (x : ℝ) : ℂ := windowCutoff t ε x • F x

theorem windowCutoff_smooth (t ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (windowCutoff t ε) := by
  unfold windowCutoff
  exact (Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub contDiff_id).div_const ε |>.sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp
      ((contDiff_const.add contDiff_id).div_const ε |>.sub contDiff_const))

theorem windowCutoff_bounds (t ε x : ℝ) : 0 ≤ windowCutoff t ε x ∧ windowCutoff t ε x ≤ 1 := by
  unfold windowCutoff
  exact ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
    mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)⟩

theorem windowCutoff_zero_right (t ε x : ℝ) (hε : 0 < ε) (hx : t - ε ≤ x) :
    windowCutoff t ε x = 0 := by
  unfold windowCutoff
  rw [Real.smoothTransition.zero_of_nonpos]
  · simp
  · have h : (t - x) / ε ≤ 1 := (div_le_one hε).mpr (by linarith)
    linarith

theorem windowCutoff_zero_left (t ε x : ℝ) (hε : 0 < ε) (hx : x ≤ -t + ε) :
    windowCutoff t ε x = 0 := by
  unfold windowCutoff
  rw [Real.smoothTransition.zero_of_nonpos (x := (t + x) / ε - 1)]
  · simp
  · have h : (t + x) / ε ≤ 1 := (div_le_one hε).mpr (by linarith)
    linarith

theorem windowCutoff_one (t ε x : ℝ) (hε : 0 < ε)
    (hl : -t + 2 * ε ≤ x) (hr : x ≤ t - 2 * ε) : windowCutoff t ε x = 1 := by
  unfold windowCutoff
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le]
  · simp
  · have : 2 ≤ (t + x) / ε := (le_div_iff₀ hε).mpr (by linarith)
    linarith
  · have : 2 ≤ (t - x) / ε := (le_div_iff₀ hε).mpr (by linarith)
    linarith

theorem cutoffColumn_tsupport (t ε : ℝ) (hε : 0 < ε) (F : ℝ → ℂ) :
    tsupport (cutoffColumn t ε F) ⊆ Icc (-t + ε) (t - ε) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra hn
    have hz := windowCutoff_zero_left t ε x hε (le_of_not_ge hn)
    exact hx (by simp [cutoffColumn, hz])
  · by_contra hn
    have hz := windowCutoff_zero_right t ε x hε (le_of_not_ge hn)
    exact hx (by simp [cutoffColumn, hz])

theorem cutoffColumn_supported (t ε : ℝ) (hε : 0 < ε) (F : ℝ → ℂ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : SupportedTest t (cutoffColumn t ε F) := by
  refine ⟨⟨(windowCutoff_smooth t ε).smul hF, ?_⟩, ?_⟩
  · exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (cutoffColumn_tsupport t ε hε F)
  · intro x hx
    have hh := cutoffColumn_tsupport t ε hε F hx
    constructor <;> linarith [hh.1, hh.2]

theorem cutoffColumn_hasDerivAt (t ε : ℝ) (F : ℝ → ℂ)
    (hF : Differentiable ℝ F) (x : ℝ) :
    HasDerivAt (cutoffColumn t ε F)
      (deriv (windowCutoff t ε) x • F x + windowCutoff t ε x • deriv F x) x := by
  change HasDerivAt (fun y => windowCutoff t ε y • F y) _ x
  convert ((windowCutoff_smooth t ε).differentiable (by simp) x).hasDerivAt.smul
    (hF x).hasDerivAt using 1 <;> first | rfl | exact add_comm _ _

theorem transition_deriv_zero_left (x : ℝ) (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have he : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
  simpa using he.deriv_eq

theorem transition_deriv_zero_right (x : ℝ) (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have he : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
  simpa using he.deriv_eq

theorem transition_deriv_bounded : ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ A := by
  have hd : Continuous (deriv Real.smoothTransition) := by
    simpa only [iteratedDeriv_one] using
      (Real.smoothTransition.contDiff (n := 2)).continuous_iteratedDeriv 1 (by norm_num)
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) hd.continuousOn
  refine ⟨max A 0, le_max_right _ _, fun x => ?_⟩
  by_cases hl : x < 0
  · rw [transition_deriv_zero_left x hl, abs_zero]
    exact le_max_right _ _
  by_cases hr : 1 < x
  · rw [transition_deriv_zero_right x hr, abs_zero]
    exact le_max_right _ _
  exact (hA x ⟨le_of_not_gt hl, le_of_not_gt hr⟩).trans (le_max_left _ _)

theorem windowCutoff_hasDerivAt (t ε x : ℝ) :
    HasDerivAt (windowCutoff t ε)
      (deriv Real.smoothTransition ((t - x) / ε - 1) * (-1 / ε) *
          Real.smoothTransition ((t + x) / ε - 1) +
       Real.smoothTransition ((t - x) / ε - 1) *
          (deriv Real.smoothTransition ((t + x) / ε - 1) * (1 / ε))) x := by
  have hd : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  change HasDerivAt (fun y => Real.smoothTransition ((t - y) / ε - 1) *
    Real.smoothTransition ((t + y) / ε - 1)) _ x
  convert ((hd _).hasDerivAt.comp x
    (((hasDerivAt_id x).const_sub t).div_const ε |>.sub_const 1)).mul
    ((hd _).hasDerivAt.comp x
      (((hasDerivAt_id x).const_add t).div_const ε |>.sub_const 1)) using 1 <;>
    first | rfl | ring

theorem windowCutoff_deriv_zero (t ε x : ℝ) (hε : 0 < ε)
    (hl : -t + 2 * ε < x) (hr : x < t - 2 * ε) : deriv (windowCutoff t ε) x = 0 := by
  rw [(windowCutoff_hasDerivAt t ε x).deriv]
  have hl' : 1 < (t + x) / ε - 1 := by
    have : 2 < (t + x) / ε := (lt_div_iff₀ hε).mpr (by linarith)
    linarith
  have hr' : 1 < (t - x) / ε - 1 := by
    have : 2 < (t - x) / ε := (lt_div_iff₀ hε).mpr (by linarith)
    linarith
  rw [transition_deriv_zero_right _ hl', transition_deriv_zero_right _ hr']
  ring

theorem greenColumn_smooth (t : ℝ) (ρ : CriticalZeros) :
    ContDiff ℝ (⊤ : ℕ∞) (greenColumn t ρ) := by
  apply contDiff_infty.mpr
  intro n
  change ContDiff ℝ n (dirichletProblemOneColumn t (actualGreenOrdinate ρ))
  let gamma := actualGreenOrdinate ρ
  rw [contDiff_iff_contDiffAt]
  intro x
  let q := problemOneGreenQ gamma
  let f0 : ℝ → ℂ :=
    fun y => q * realExpMode (problemOneFreq gamma) y
  let fR : ℝ → ℂ :=
    fun y =>
      (-q * realExpMode (problemOneFreq gamma) t) *
        dirichletRightBasis t y
  let fL : ℝ → ℂ :=
    fun y =>
      (-q * realExpMode (problemOneFreq gamma) (-t)) *
        dirichletLeftBasis t y
  have hf0 : ContDiffAt ℝ n f0 x := by
    simpa [f0] using
      contDiffAt_const_mul_realExpMode n q (problemOneFreq gamma) x
  have hfR : ContDiffAt ℝ n fR x := by
    exact
      (contDiff_const.contDiffAt.mul
        (contDiffAt_dirichletRightBasis n t x))
  have hfL : ContDiffAt ℝ n fL x := by
    exact
      (contDiff_const.contDiffAt.mul
        (contDiffAt_dirichletLeftBasis n t x))
  have hcol :
      dirichletProblemOneColumn t gamma = f0 + fR + fL := by
    funext y
    rfl
  rw [hcol]
  exact (hf0.add hfR).add hfL


theorem endpoint_norm_bounds (t M : ℝ) (ht : 0 < t) (F : ℝ → ℂ)
    (hF : Differentiable ℝ F) (hM : ∀ x ∈ Icc (-t) t, ‖deriv F x‖ ≤ M)
    (hl : F (-t) = 0) (hr : F t = 0) (x : ℝ) (hx : x ∈ Icc (-t) t) :
    ‖F x‖ ≤ M * (t - x) ∧ ‖F x‖ ≤ M * (t + x) := by
  have hp := Convex.norm_image_sub_le_of_norm_deriv_le (fun y _ => hF y) hM (convex_Icc (-t) t)
    (right_mem_Icc.mpr (by linarith : -t ≤ t)) hx
  have hn := Convex.norm_image_sub_le_of_norm_deriv_le (fun y _ => hF y) hM (convex_Icc (-t) t)
    (left_mem_Icc.mpr (by linarith : -t ≤ t)) hx
  constructor
  · simpa [hr, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hx.2)] using hp
  · simpa [hl, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1] : 0 ≤ t + x), add_comm] using hn

theorem transition_scaled_product_bound (A M ε s : ℝ) (a : ℂ)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hε : 0 < ε)
    (hD : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ A)
    (ha : ‖a‖ ≤ M * s) :
    |deriv Real.smoothTransition (s / ε - 1) / ε| * ‖a‖ ≤ 2 * A * M := by
  by_cases hh : 1 < s / ε - 1
  · rw [transition_deriv_zero_right _ hh]
    simp only [zero_div, abs_zero, zero_mul]
    positivity
  · have hdist : s ≤ 2 * ε := by
      have : s / ε ≤ 2 := by linarith [le_of_not_gt hh]
      exact (div_le_iff₀ hε).mp this
    have hn : ‖a‖ / ε ≤ 2 * M := by
      apply (div_le_iff₀ hε).mpr
      exact ha.trans (by nlinarith [mul_le_mul_of_nonneg_left hdist hM])
    calc
      _ = |deriv Real.smoothTransition (s / ε - 1)| * (‖a‖ / ε) := by
        rw [abs_div, abs_of_pos hε]
        ring
      _ ≤ A * (2 * M) := mul_le_mul (hD _) hn (by positivity) hA
      _ = _ := by ring

theorem cutoff_derivative_boundary_bound (t ε A M : ℝ) (ht : 0 < t) (hε : 0 < ε)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hD : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ A)
    (F : ℝ → ℂ) (hF : Differentiable ℝ F)
    (hMF : ∀ x ∈ Icc (-t) t, ‖deriv F x‖ ≤ M) (hl : F (-t) = 0) (hr : F t = 0)
    (x : ℝ) (hx : x ∈ Icc (-t) t) :
    ‖deriv (windowCutoff t ε) x • F x‖ ≤ 4 * A * M := by
  have hb := endpoint_norm_bounds t M ht F hF hMF hl hr x hx
  have h1 := transition_scaled_product_bound A M ε (t - x) (F x) hA hM hε hD hb.1
  have h2 := transition_scaled_product_bound A M ε (t + x) (F x) hA hM hε hD hb.2
  let a := deriv Real.smoothTransition ((t - x) / ε - 1) * (-1 / ε)
  let b := Real.smoothTransition ((t + x) / ε - 1)
  let c := Real.smoothTransition ((t - x) / ε - 1)
  let d := deriv Real.smoothTransition ((t + x) / ε - 1) * (1 / ε)
  have ha : |a| * ‖F x‖ ≤ 2 * A * M := by simpa [a, div_eq_mul_inv] using h1
  have hd : |d| * ‖F x‖ ≤ 2 * A * M := by simpa [d, div_eq_mul_inv] using h2
  have hab : |a * b| * ‖F x‖ ≤ 2 * A * M := by
    calc
      _ = |b| * (|a| * ‖F x‖) := by rw [abs_mul]; ring
      _ ≤ 1 * (2 * A * M) := mul_le_mul
        (by simpa [b, abs_of_nonneg (Real.smoothTransition.nonneg _)] using Real.smoothTransition.le_one ((t + x) / ε - 1))
        ha (by positivity) (by norm_num)
      _ = _ := one_mul _
  have hcd : |c * d| * ‖F x‖ ≤ 2 * A * M := by
    calc
      _ = |c| * (|d| * ‖F x‖) := by rw [abs_mul]; ring
      _ ≤ 1 * (2 * A * M) := mul_le_mul
        (by simpa [c, abs_of_nonneg (Real.smoothTransition.nonneg _)] using Real.smoothTransition.le_one ((t - x) / ε - 1))
        hd (by positivity) (by norm_num)
      _ = _ := one_mul _
  rw [norm_smul, Real.norm_eq_abs, (windowCutoff_hasDerivAt t ε x).deriv]
  change |a * b + c * d| * ‖F x‖ ≤ _
  have hh := mul_le_mul_of_nonneg_right (abs_add_le (a * b) (c * d)) (norm_nonneg (F x))
  nlinarith

end ConnesGreen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex MeasureTheory Set Filter ConnesRZ ConnesRZFrontier
open scoped BigOperators InnerProductSpace lp ENNReal Classical Topology
noncomputable section
namespace ConnesGreen
open WeilDefect WeilDefect.ConnesNative

def cutoffScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem cutoffScale_pos (n : ℕ) : 0 < cutoffScale n := by unfold cutoffScale; positivity

theorem cutoffScale_tendsto : Tendsto cutoffScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem cutoff_eventually_identity (t x : ℝ) (hx : x ∈ Ioo (-t) t) :
    ∀ᶠ n : ℕ in atTop,
      windowCutoff t (cutoffScale n) x = 1 ∧ deriv (windowCutoff t (cutoffScale n)) x = 0 := by
  have hl : ∀ᶠ n in atTop, cutoffScale n < (t + x) / 2 :=
    cutoffScale_tendsto.eventually (gt_mem_nhds (by linarith [hx.1] : 0 < (t + x) / 2))
  have hr : ∀ᶠ n in atTop, cutoffScale n < (t - x) / 2 :=
    cutoffScale_tendsto.eventually (gt_mem_nhds (by linarith [hx.2] : 0 < (t - x) / 2))
  filter_upwards [hl, hr] with n hn hm
  exact ⟨windowCutoff_one t _ x (cutoffScale_pos n) (by linarith) (by linarith),
    windowCutoff_deriv_zero t _ x (cutoffScale_pos n) (by linarith) (by linarith)⟩

theorem window_ae_interior (t : ℝ) : ∀ᵐ x ∂windowMeasure t, x ∈ Ioo (-t) t := by
  unfold windowMeasure
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [volume.ae_ne (-t), volume.ae_ne t] with x hl hr hx
  exact ⟨lt_of_le_of_ne hx.1 hl.symm, lt_of_le_of_ne hx.2 hr⟩

theorem windowL2_sub (t : ℝ) (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    windowL2 t (fun x => f x - g x) = windowL2 t f - windowL2 t g := by
  have hfl := continuous_window_memLp t f hf
  have hgl := continuous_window_memLp t g hg
  have hsg : MemLp (fun x => f x - g x) 2 (windowMeasure t) := hfl.sub hgl
  simp only [windowL2, dif_pos hfl, dif_pos hgl, dif_pos hsg]
  exact MemLp.toLp_sub hfl hgl

theorem windowL2_norm_sq (t : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    ‖windowL2 t f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂windowMeasure t := by
  rw [@norm_sq_eq_re_inner ℂ]
  change (⟪windowL2 t f, windowL2 t f⟫_ℂ).re = _
  rw [windowL2_inner t f f (continuous_window_memLp t f hf) (continuous_window_memLp t f hf)]
  have he : (∫ x, star (f x) * f x ∂windowMeasure t) =
      ((∫ x, ‖f x‖ ^ 2 ∂windowMeasure t : ℝ) : ℂ) := by
    trans ∫ x, ((‖f x‖ ^ 2 : ℝ) : ℂ) ∂windowMeasure t
    · apply integral_congr_ae
      exact Eventually.of_forall (fun x => by simpa [RCLike.star_def] using Complex.conj_mul' (f x))
    · exact integral_complex_ofReal
  rw [he]
  rfl

/-- Dominated convergence in the original restricted-window L2 class. -/
theorem windowL2_tendsto_of_dominated (t B : ℝ) (f : ℕ → ℝ → ℂ) (g : ℝ → ℂ)
    (hf : ∀ n, Continuous (f n)) (hg : Continuous g)
    (hb : ∀ n x, x ∈ Icc (-t) t → ‖f n x - g x‖ ≤ B)
    (hl : ∀ x ∈ Ioo (-t) t, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => windowL2 t (f n)) atTop (𝓝 (windowL2 t g)) := by
  have hi := tendsto_integral_of_dominated_convergence (μ := windowMeasure t)
    (F := fun n x => ‖f n x - g x‖ ^ 2) (f := fun _ => (0 : ℝ)) (fun _ => B ^ 2)
    (fun n => ((hf n).sub hg).norm.pow 2 |>.aestronglyMeasurable)
    (integrable_const _) (fun n => ?_) (by
      filter_upwards [window_ae_interior t] with x hx
      have hc : Tendsto (fun _ : ℕ => g x) atTop (𝓝 (g x)) := tendsto_const_nhds
      simpa using ((hl x hx).sub hc).norm.pow 2)
  · have hs : Tendsto (fun n => ‖windowL2 t (f n) - windowL2 t g‖ ^ 2) atTop (𝓝 0) := by
      have heq : (fun n => ‖windowL2 t (f n) - windowL2 t g‖ ^ 2) =
          (fun n => ∫ x, ‖f n x - g x‖ ^ 2 ∂windowMeasure t) := by
        ext n
        rw [← windowL2_sub t _ _ (hf n) hg]
        exact windowL2_norm_sq t (fun x => f n x - g x) ((hf n).sub hg)
      rw [heq]
      simpa only [integral_zero] using hi
    have hn := hs.sqrt
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hn
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb n x hx) 2

theorem cutoffColumn_norm_le (t ε : ℝ) (F : ℝ → ℂ) (x : ℝ) :
    ‖cutoffColumn t ε F x‖ ≤ ‖F x‖ := by
  rw [cutoffColumn, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (windowCutoff_bounds t ε x).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (windowCutoff_bounds t ε x).2

/-- Original smooth endpoint-zero columns are limits of original strictly
supported tests in both energy coordinates. -/
theorem smooth_dirichlet_energy_mem (t : ℝ) (ht : 0 < t) (F : ℝ → ℂ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hl : F (-t) = 0) (hr : F t = 0) :
    energyVector t F ∈ energySubspace t := by
  have hdiff := hF.differentiable (by simp)
  have hdcont : Continuous (deriv F) := by
    simpa only [iteratedDeriv_one] using hF.continuous_iteratedDeriv 1 (by simp)
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-t) t) hdcont.continuousOn
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hMF : ∀ x ∈ Icc (-t) t, ‖deriv F x‖ ≤ M :=
    fun x hx => (hM₀ x hx).trans (le_max_left _ _)
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-t) t) hF.continuous.continuousOn
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hCF : ∀ x ∈ Icc (-t) t, ‖F x‖ ≤ C :=
    fun x hx => (hC₀ x hx).trans (le_max_left _ _)
  obtain ⟨A, hA, hDA⟩ := transition_deriv_bounded
  let fn := fun n => cutoffColumn t (cutoffScale n) F
  have hfn : ∀ n, SupportedTest t (fn n) :=
    fun n => cutoffColumn_supported t _ (cutoffScale_pos n) F hF
  have hfun : Tendsto (fun n => windowL2 t (fn n)) atTop (𝓝 (windowL2 t F)) := by
    apply windowL2_tendsto_of_dominated t (2 * C) fn F (fun n => (hfn n).1.1.continuous)
      hF.continuous
    · intro n x hx
      exact (norm_sub_le _ _).trans (by
        have hh := (cutoffColumn_norm_le t (cutoffScale n) F x).trans (hCF x hx)
        linarith [hCF x hx])
    · intro x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [cutoff_eventually_identity t x hx] with n hn
      simp only [fn, cutoffColumn, hn.1, one_smul]
  have hderiv : Tendsto (fun n => windowL2 t (deriv (fn n))) atTop
      (𝓝 (windowL2 t (deriv F))) := by
    apply windowL2_tendsto_of_dominated t (4 * A * M + 2 * M) (fun n => deriv (fn n))
      (deriv F) (fun n => by
        simpa only [iteratedDeriv_one] using (hfn n).1.1.continuous_iteratedDeriv 1 (by simp)) hdcont
    · intro n x hx
      rw [(cutoffColumn_hasDerivAt t (cutoffScale n) F hdiff x).deriv]
      have hb := cutoff_derivative_boundary_bound t (cutoffScale n) A M ht
        (cutoffScale_pos n) hA hM hDA F hdiff hMF hl hr x hx
      have hc : ‖windowCutoff t (cutoffScale n) x • deriv F x‖ ≤ M :=
        (cutoffColumn_norm_le t (cutoffScale n) (deriv F) x).trans (hMF x hx)
      calc
        _ ≤ ‖deriv (windowCutoff t (cutoffScale n)) x • F x +
            windowCutoff t (cutoffScale n) x • deriv F x‖ + ‖deriv F x‖ := norm_sub_le _ _
        _ ≤ ‖deriv (windowCutoff t (cutoffScale n)) x • F x‖ +
            ‖windowCutoff t (cutoffScale n) x • deriv F x‖ + ‖deriv F x‖ :=
          by
            have ha := norm_add_le (deriv (windowCutoff t (cutoffScale n)) x • F x)
              (windowCutoff t (cutoffScale n) x • deriv F x)
            linarith
        _ ≤ _ := by linarith [hMF x hx]
    · intro x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [cutoff_eventually_identity t x hx] with n hn
      rw [(cutoffColumn_hasDerivAt t (cutoffScale n) F hdiff x).deriv, hn.1, hn.2]
      simp
  have he : Tendsto (fun n => energyVector t (fn n)) atTop (𝓝 (energyVector t F)) := by
    have hp : Tendsto
        (fun n => fun i : Fin 2 => if i = 0 then windowL2 t (deriv (fn n)) else
          (1 / 2 : ℂ) • windowL2 t (fn n)) atTop
        (𝓝 (fun i : Fin 2 => if i = 0 then windowL2 t (deriv F) else
          (1 / 2 : ℂ) • windowL2 t F)) := by
      apply tendsto_pi_nhds.mpr
      intro i
      fin_cases i
      · simpa using hderiv
      · simpa using tendsto_const_nhds.smul hfun
    simpa only [Function.comp_def, energyVector, iteratedDeriv_one] using
      (PiLp.continuous_toLp 2 (fun _ : Fin 2 => WindowL2 t)).continuousAt.tendsto.comp hp
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto he
    (Eventually.of_forall (fun n => supported_energy_mem t (fn n) (hfn n)))

theorem actual_column_energy_membership (t : ℝ) (ht : 0 < t) :
    ∀ ρ : CriticalZeros, energyVector t (greenColumn t ρ) ∈ energySubspace t := by
  intro ρ
  exact smooth_dirichlet_energy_mem t ht _ (greenColumn_smooth t ρ)
    (dirichletProblemOneColumn_neg t _ ht.ne') (dirichletProblemOneColumn_pos t _ ht.ne')


end ConnesGreen

theorem solution (t : ℝ) (ht : 0 < t) :
    ∀ ρ : ConnesRZFrontier.CriticalZeros,
      ConnesGreen.energyVector t (ConnesGreen.greenColumn t ρ) ∈ ConnesGreen.energySubspace t :=
  ConnesGreen.actual_column_energy_membership t ht
