-- Prove2me | solution 1 for CohnElkies.upperShortShellVariance_global_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/3ac0e908-08ab-4b42-815c-72c3a906fa08

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upper_shortShellDensity_variance_le

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
    {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 ≤ δ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    upperShortShellVariance ε δ ≤
      (1 / 2 : ℝ) * upperShellShortCoefficient ε *
        Real.exp (δ * shortEndpoint ε) := by
  let a₀ : ℝ := shortCutoff ε
  let A : ℝ := shortEndpoint ε
  let K : ℝ := (1 / 2 : ℝ) * Real.exp (δ * A)
  have ha₀ : 0 < a₀ := by
    try dsimp [a₀, shortCutoff]
    positivity
  have hA : 0 < A := ha₀.trans_le horder
  have hK : 0 ≤ K := by
    try dsimp [K]
    positivity
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
    positivity
  have hcosh : Continuous
      (fun a : ℝ => Real.cosh ((1 + δ) * a)) := by
    fun_prop
  have hleft : ContinuousOn
      (fun a : ℝ =>
        (-shortShellDensity ε a) * a ^ 2 *
          Real.cosh ((1 + δ) * a))
        (Set.Icc a₀ A) :=
    (hshort.neg.mul
      (continuous_id.pow 2).continuousOn).mul
        hcosh.continuousOn
  have hpoint :
      ∀ a ∈ Set.Icc a₀ A,
        (-shortShellDensity ε a) * a ^ 2 *
          Real.cosh ((1 + δ) * a) ≤ K := by
    intro a ha
    exact upper_shortShellDensity_variance_le hε hδ
      (ha₀.trans_le ha.1) ha.2
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) horder
    (hleft.intervalIntegrable_of_Icc horder)
    ((continuous_const : Continuous
      (fun _ : ℝ => K)).intervalIntegrable _ _)
    hpoint
  have hinv : 0 ≤ a₀⁻¹ := (inv_pos.mpr ha₀).le
  change
    (∫ a in a₀..A,
      (-shortShellDensity ε a) * a ^ 2 *
        Real.cosh ((1 + δ) * a)) ≤
      (1 / 2 : ℝ) * upperShellShortCoefficient ε *
        Real.exp (δ * A)
  calc
    (∫ a in a₀..A,
      (-shortShellDensity ε a) * a ^ 2 *
        Real.cosh ((1 + δ) * a)) ≤
      (A - a₀) * K := by
        simpa using! hmono
    _ ≤ (A + a₀⁻¹) * K := by
      apply mul_le_mul_of_nonneg_right _ hK
      nlinarith
    _ = (1 / 2 : ℝ) * upperShellShortCoefficient ε *
        Real.exp (δ * A) := by
      unfold upperShellShortCoefficient
      try dsimp [A, a₀, K]
      ring
end CohnElkies
