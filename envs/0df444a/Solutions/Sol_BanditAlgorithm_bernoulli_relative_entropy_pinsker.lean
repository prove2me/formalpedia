-- Prove2me | solution 1 for BanditAlgorithm.bernoulli_relative_entropy_pinsker
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-28T20:52:37.566942+00:00
-- url     : https://prove2.me/submissions/1fc42537-363b-41fe-b45d-a5f17940da47

import Definitions.Def_bernoulliRelativeEntropy
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Set

namespace BanditAlgorithm

/-!
Lattimore--Szepesvári, *Bandit Algorithms*, Lemma 10.2(b), printed p. 134,
and Exercise 10.1, printed p. 141.  The exercise fixes `p` and studies
`g(x) = d(p,x) - 2(p-x)^2`; its derivative has the sign of `x-p`.
-/

private noncomputable def bernoulliPinskerAux (p x : ℝ) : ℝ :=
  p * (Real.log p - Real.log x) +
    (1 - p) * (Real.log (1 - p) - Real.log (1 - x)) -
      2 * (p - x) ^ 2

private lemma hasDerivAt_bernoulliPinskerAux
    {p x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    HasDerivAt (bernoulliPinskerAux p)
      ((x - p) / (x * (1 - x)) - 4 * (x - p)) x := by
  have hlogx : HasDerivAt Real.log x⁻¹ x :=
    Real.hasDerivAt_log hx0
  have honeSub : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) x :=
    (hasDerivAt_id' x).const_sub 1
  have hlogOneSub :
      HasDerivAt (fun y : ℝ ↦ Real.log (1 - y))
        ((1 - x)⁻¹ * (-1)) x :=
    (Real.hasDerivAt_log (sub_ne_zero.mpr hx1.symm)).comp x honeSub
  have hfirst :
      HasDerivAt
        (fun y : ℝ ↦ p * (Real.log p - Real.log y))
        (p * (0 - x⁻¹)) x :=
    ((hasDerivAt_const x (Real.log p)).sub hlogx).const_mul p
  have hsecond :
      HasDerivAt
        (fun y : ℝ ↦
          (1 - p) * (Real.log (1 - p) - Real.log (1 - y)))
        ((1 - p) * (0 - (1 - x)⁻¹ * (-1))) x :=
    ((hasDerivAt_const x (Real.log (1 - p))).sub hlogOneSub).const_mul
      (1 - p)
  have hsquare :
      HasDerivAt (fun y : ℝ ↦ -2 * (p - y) ^ 2)
        (-2 * (2 * (p - x) * (-1))) x :=
    by
      refine ((((hasDerivAt_id' x).const_sub p).pow 2).const_mul (-2)).congr_deriv ?_
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  unfold bernoulliPinskerAux
  have h := (hfirst.add hsecond).add hsquare
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · field_simp [hx0, sub_ne_zero.mpr hx1.symm]
    ring
  · filter_upwards with y
    simp only [Pi.add_apply]
    ring

private lemma bernoulliPinskerAux_continuousAt
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (bernoulliPinskerAux p) p := by
  rcases eq_or_ne p 0 with rfl | hp0
  · have h :
        ContinuousAt (fun x : ℝ ↦ -Real.log (1 - x) - 2 * x ^ 2) 0 := by
      fun_prop (disch := norm_num)
    have heq :
        bernoulliPinskerAux 0 =
          (fun x : ℝ ↦ -Real.log (1 - x) - 2 * x ^ 2) := by
      funext x
      simp [bernoulliPinskerAux]
    rw [heq]
    exact h
  rcases eq_or_ne p 1 with rfl | hp1
  · have h :
        ContinuousAt (fun x : ℝ ↦ -Real.log x - 2 * (1 - x) ^ 2) 1 := by
      fun_prop (disch := norm_num)
    have heq :
        bernoulliPinskerAux 1 =
          (fun x : ℝ ↦ -Real.log x - 2 * (1 - x) ^ 2) := by
      funext x
      simp [bernoulliPinskerAux]
    rw [heq]
    exact h
  · unfold bernoulliPinskerAux
    have hpOne : 1 - p ≠ 0 := sub_ne_zero.mpr hp1.symm
    fun_prop

private lemma bernoulliPinskerAux_eq_entropy_sub
    {p q : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hq : q ∈ Ioo (0 : ℝ) 1) :
    bernoulliPinskerAux p q =
      bernoulliRelativeEntropy p q - 2 * (p - q) ^ 2 := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [bernoulliPinskerAux, bernoulliRelativeEntropy]
  rcases eq_or_ne p 1 with rfl | hp1
  · simp [bernoulliPinskerAux, bernoulliRelativeEntropy]
  have hq0 : q ≠ 0 := ne_of_gt hq.1
  have hq1 : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq.2)
  have hpOne : 1 - p ≠ 0 := sub_ne_zero.mpr hp1.symm
  rw [bernoulliPinskerAux, bernoulliRelativeEntropy,
    Real.log_div hp0 hq0, Real.log_div hpOne hq1]

private lemma bernoulliPinskerAux_deriv_nonpos
    {p x : ℝ} (hxp : x < p) (hx : x ∈ Ioo (0 : ℝ) 1) :
    deriv (bernoulliPinskerAux p) x ≤ 0 := by
  have hden : 0 < x * (1 - x) := mul_pos hx.1 (sub_pos.mpr hx.2)
  have hcoef : 0 ≤ 1 / (x * (1 - x)) - 4 := by
    rw [sub_nonneg, le_div_iff₀ hden]
    nlinarith [sq_nonneg (2 * x - 1)]
  rw [(hasDerivAt_bernoulliPinskerAux
    (ne_of_gt hx.1) (ne_of_lt hx.2)).deriv]
  have heq :
      (x - p) / (x * (1 - x)) - 4 * (x - p) =
        (x - p) * (1 / (x * (1 - x)) - 4) := by
    field_simp [ne_of_gt hden]
  rw [heq]
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxp.le) hcoef

private lemma bernoulliPinskerAux_deriv_nonneg
    {p x : ℝ} (hpx : p < x) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 ≤ deriv (bernoulliPinskerAux p) x := by
  have hden : 0 < x * (1 - x) := mul_pos hx.1 (sub_pos.mpr hx.2)
  have hcoef : 0 ≤ 1 / (x * (1 - x)) - 4 := by
    rw [sub_nonneg, le_div_iff₀ hden]
    nlinarith [sq_nonneg (2 * x - 1)]
  rw [(hasDerivAt_bernoulliPinskerAux
    (ne_of_gt hx.1) (ne_of_lt hx.2)).deriv]
  have heq :
      (x - p) / (x * (1 - x)) - 4 * (x - p) =
        (x - p) * (1 / (x * (1 - x)) - 4) := by
    field_simp [ne_of_gt hden]
  rw [heq]
  exact mul_nonneg (sub_nonneg.mpr hpx.le) hcoef

end BanditAlgorithm

open BanditAlgorithm

theorem solution (p q : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    2 * (p - q) ^ 2 ≤ BanditAlgorithm.bernoulliRelativeEntropy p q := by
  have hdiffLeft :
      DifferentiableOn ℝ (bernoulliPinskerAux p) (Ioo 0 p) := by
    intro x hx
    exact (hasDerivAt_bernoulliPinskerAux
      (ne_of_gt hx.1)
      (ne_of_lt (hx.2.trans_le hp.2))).differentiableAt.differentiableWithinAt
  have hdiffRight :
      DifferentiableOn ℝ (bernoulliPinskerAux p) (Ioo p 1) := by
    intro x hx
    exact (hasDerivAt_bernoulliPinskerAux
      (ne_of_gt (hp.1.trans_lt hx.1))
      (ne_of_lt hx.2)).differentiableAt.differentiableWithinAt
  have hmin :
      IsMinOn (bernoulliPinskerAux p) (Ioo 0 1) p :=
    isMinOn_Ioo_of_deriv
      (bernoulliPinskerAux_continuousAt hp)
      hdiffLeft hdiffRight
      (fun x hx ↦ bernoulliPinskerAux_deriv_nonpos
        hx.2 ⟨hx.1, hx.2.trans_le hp.2⟩)
      (fun x hx ↦ bernoulliPinskerAux_deriv_nonneg
        hx.1 ⟨hp.1.trans_lt hx.1, hx.2⟩)
  have haux : bernoulliPinskerAux p p ≤ bernoulliPinskerAux p q :=
    hmin hq
  have hself : bernoulliPinskerAux p p = 0 := by
    simp [bernoulliPinskerAux]
  rw [hself, bernoulliPinskerAux_eq_entropy_sub hp hq] at haux
  linarith
