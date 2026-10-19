-- Prove2me | solution 1 for CohnElkies.upperShortShellDamping_global_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/0c86fa97-c9e9-4357-b2cc-051f63b820e6

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upper_shortShellDensity_damping_le
import Theorems.Thm_CohnElkies_upper_intervalIntegral_one_add_inv_sq

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ δ T : ℝ}
    (hε : 0 < ε) (hℓ : 0 ≤ ℓ) (hδ : 0 ≤ δ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Set.Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a) :
    upperShortShellDamping ε ℓ δ T ≤
      ℓ * upperShellShortCoefficient ε *
        Real.exp (δ * shortEndpoint ε) *
          min (T ^ 2) 1 := by
  let a₀ : ℝ := shortCutoff ε
  let A : ℝ := shortEndpoint ε
  let K : ℝ := Real.exp (δ * A) * min (T ^ 2) 1
  have ha₀ : 0 < a₀ := by
    try dsimp [a₀, shortCutoff]
    positivity
  have hA : 0 < A := ha₀.trans_le horder
  have hK : 0 ≤ K := by
    try dsimp [K]
    exact mul_nonneg (Real.exp_pos _).le
      (le_min (sq_nonneg T) (by norm_num))
  have hshort :
      ContinuousOn (shortShellDensity ε) (Set.Icc a₀ A) := by
    have hn : Continuous (fun a : ℝ =>
      shortMargin ε a * Real.exp (-2 * a)) := by
      unfold shortMargin
      fun_prop
    have hd : Continuous (fun a : ℝ =>
      2 * a ^ 2 * Real.cosh a) := by
      fun_prop
    unfold shortShellDensity
    apply (hn.continuousOn.div hd.continuousOn ?_).neg
    intro a ha
    have hapos : 0 < a := ha₀.trans_le ha.1
    exact
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hapos))
        (Real.cosh_pos a)).ne'
  have hcosh : Continuous
      (fun a : ℝ => Real.cosh ((1 + δ) * a)) := by
    fun_prop
  have hosc : Continuous
      (fun a : ℝ => 1 - Real.cos (a * T)) := by
    fun_prop
  have hleft : ContinuousOn
      (fun a : ℝ =>
        (-shortShellDensity ε a) *
          Real.cosh ((1 + δ) * a) *
            (1 - Real.cos (a * T)))
        (Set.Icc a₀ A) :=
    (hshort.neg.mul hcosh.continuousOn).mul
      hosc.continuousOn
  have hinv : ContinuousOn
      (fun a : ℝ => (a ^ 2)⁻¹)
        (Set.Icc a₀ A) := by
    apply (continuous_id.pow 2).continuousOn.inv₀
    intro a ha
    have hapos : 0 < a := ha₀.trans_le ha.1
    exact (sq_pos_of_pos hapos).ne'
  have hright : ContinuousOn
      (fun a : ℝ => K * (1 + (a ^ 2)⁻¹))
        (Set.Icc a₀ A) :=
    continuousOn_const.mul
      (continuousOn_const.add hinv)
  have hpoint :
      ∀ a ∈ Set.Icc a₀ A,
        (-shortShellDensity ε a) *
            Real.cosh ((1 + δ) * a) *
              (1 - Real.cos (a * T)) ≤
          K * (1 + (a ^ 2)⁻¹) := by
    intro a ha
    have hapos : 0 < a := ha₀.trans_le ha.1
    exact upper_shortShellDensity_damping_le
      hε hδ hapos ha.2
      (hmargin a ha) T
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) horder
    (hleft.intervalIntegrable_of_Icc horder)
    (hright.intervalIntegrable_of_Icc horder)
    hpoint
  have hevaluate :
      (∫ a in a₀..A, K * (1 + (a ^ 2)⁻¹)) =
        K * (A - a₀ + a₀⁻¹ - A⁻¹) := by
    rw [intervalIntegral.integral_const_mul,
      upper_intervalIntegral_one_add_inv_sq ha₀ horder]
  rw [hevaluate] at hmono
  have hcoefficient :
      A - a₀ + a₀⁻¹ - A⁻¹ ≤ A + a₀⁻¹ := by
    have hAinv : 0 ≤ A⁻¹ := (inv_pos.mpr hA).le
    nlinarith
  change
    ℓ * (∫ a in a₀..A,
      (-shortShellDensity ε a) *
        Real.cosh ((1 + δ) * a) *
          (1 - Real.cos (a * T))) ≤
      ℓ * upperShellShortCoefficient ε *
        Real.exp (δ * A) * min (T ^ 2) 1
  calc
    ℓ * (∫ a in a₀..A,
        (-shortShellDensity ε a) *
          Real.cosh ((1 + δ) * a) *
            (1 - Real.cos (a * T))) ≤
        ℓ * (K * (A - a₀ + a₀⁻¹ - A⁻¹)) :=
      mul_le_mul_of_nonneg_left hmono hℓ
    _ ≤ ℓ * (K * (A + a₀⁻¹)) := by
      gcongr
    _ = ℓ * upperShellShortCoefficient ε *
        Real.exp (δ * A) * min (T ^ 2) 1 := by
      unfold upperShellShortCoefficient
      try dsimp [a₀, A, K]
      ring
end CohnElkies
