-- Prove2me | solution 1 for CohnElkies.upperShortShellThirdMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/ddea38c4-037d-4933-9e9c-9264fa756c6f

import Mathlib
import Definitions.Def_SpherePacking

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
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Set.Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a) :
    upperShortShellThirdMoment ε δ ≤
      shortEndpoint ε * upperShortShellVariance ε δ := by
  let a₀ : ℝ := shortCutoff ε
  let A : ℝ := shortEndpoint ε
  have ha₀ : 0 < a₀ := by
    try dsimp [a₀, shortCutoff]
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
  have hbase : ContinuousOn (fun a : ℝ =>
      (-shortShellDensity ε a) * a ^ 2 *
        Real.cosh ((1 + δ) * a)) (Set.Icc a₀ A) :=
    (hshort.neg.mul
      (continuous_id.pow 2).continuousOn).mul
        hcosh.continuousOn
  have hthird : ContinuousOn (fun a : ℝ =>
      (-shortShellDensity ε a) * a ^ 3 *
        Real.cosh ((1 + δ) * a)) (Set.Icc a₀ A) :=
    (hshort.neg.mul
      (continuous_id.pow 3).continuousOn).mul
        hcosh.continuousOn
  have hright : ContinuousOn (fun a : ℝ =>
      A * ((-shortShellDensity ε a) * a ^ 2 *
        Real.cosh ((1 + δ) * a))) (Set.Icc a₀ A) :=
    continuousOn_const.mul hbase
  have hpoint :
      ∀ a ∈ Set.Icc a₀ A,
        (-shortShellDensity ε a) * a ^ 3 *
            Real.cosh ((1 + δ) * a) ≤
          A * ((-shortShellDensity ε a) * a ^ 2 *
            Real.cosh ((1 + δ) * a)) := by
    intro a ha
    have hapos : 0 < a := ha₀.trans_le ha.1
    have hmargin' : 0 ≤ shortMargin ε a := by
      apply hmargin
      exact ha
    have hdensity : 0 ≤ -shortShellDensity ε a := by
      unfold shortShellDensity
      have hn : 0 ≤ shortMargin ε a * Real.exp (-2 * a) :=
        mul_nonneg hmargin' (Real.exp_pos _).le
      have hd : 0 < 2 * a ^ 2 * Real.cosh a := by
        positivity
      simpa using! div_nonneg hn hd.le
    have hbasenonneg :
        0 ≤ (-shortShellDensity ε a) * a ^ 2 *
          Real.cosh ((1 + δ) * a) :=
      mul_nonneg
        (mul_nonneg hdensity (sq_nonneg a))
        (Real.cosh_pos _).le
    calc
      (-shortShellDensity ε a) * a ^ 3 *
          Real.cosh ((1 + δ) * a) =
        a * ((-shortShellDensity ε a) * a ^ 2 *
          Real.cosh ((1 + δ) * a)) := by
            ring
      _ ≤ A *
          ((-shortShellDensity ε a) * a ^ 2 *
            Real.cosh ((1 + δ) * a)) :=
        mul_le_mul_of_nonneg_right ha.2 hbasenonneg
  have hmono := intervalIntegral.integral_mono_on
    (μ := volume) horder
    (hthird.intervalIntegrable_of_Icc horder)
    (hright.intervalIntegrable_of_Icc horder)
    hpoint
  simpa [upperShortShellThirdMoment,
    upperShortShellVariance, a₀, A,
    intervalIntegral.integral_const_mul] using! hmono
end CohnElkies
