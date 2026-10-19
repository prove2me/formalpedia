-- Prove2me | solution 1 for CohnElkies.eventually_upperSaddleThirdMoment_le_variance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/5fe93455-3ffa-40e1-842c-fa3e55c404e1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_upper_netShellVariance_bounds
import Theorems.Thm_CohnElkies_eventually_upper_netShellThirdMoment_bound
import Theorems.Thm_CohnElkies_upperGammaVariance_bounds
import Theorems.Thm_CohnElkies_upperPositiveShellVariance_pos
import Theorems.Thm_CohnElkies_upperGammaThirdMoment_le_two_mul_variance

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
    : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        ∀ ℓ : ℝ, 1 ≤ ℓ →
          ∀ δ : ℝ, ε / 2 ≤ δ →
            upperSaddleThirdMoment ε ℓ δ ≤
              (2 + (100 / 99 : ℝ) *
                upperSaddleShellThirdCoefficient ε) *
                  upperSaddleVariance ε ℓ δ := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_netShellVariance_bounds,
    eventually_upper_netShellThirdMoment_bound]
    with ε hε horder hnet hthird
  change 0 < ε at hε
  intro ℓ hℓ δ hδ
  have hℓpositive : 0 < ℓ := by linarith
  have hδnonnegative : 0 ≤ δ := by
    nlinarith
  have hη : 2 ≤ 2 + δ := by
    linarith
  have hηpositive : 0 < 2 + δ := by
    linarith
  have hgamma :=
    upperGammaThirdMoment_le_two_mul_variance
      hℓ hη
  obtain ⟨hnetlower, hnetupper⟩ :=
    hnet δ hδ
  have hpositiveShell :=
    upperPositiveShellVariance_pos hε hδnonnegative
  have hnetnonnegative :
      0 ≤ upperNetShellVariance ε δ := by
    nlinarith
  have hgammavariance :
      0 ≤ upperGammaVariance ℓ (2 + δ) := by
    have h := (upperGammaVariance_bounds
      hℓpositive hηpositive).1
    have hpositive : 0 < 1 / (2 * (2 + δ)) := by
      positivity
    exact hpositive.le.trans h
  have hshortEndpoint : 0 ≤ shortEndpoint ε := by
    have hcutoff : 0 < shortCutoff ε := by
      unfold shortCutoff
      positivity
    exact (hcutoff.trans_le horder).le
  have hB : 0 ≤ shellLocation ε := by
    unfold shellLocation
    positivity
  have hC : 0 ≤ upperSaddleShellThirdCoefficient ε := by
    unfold upperSaddleShellThirdCoefficient
    positivity
  have htransfer :
      upperPositiveShellVariance ε δ ≤
        (100 / 99 : ℝ) *
          upperNetShellVariance ε δ := by
    nlinarith
  have hthirdshell :
      upperNetShellThirdMoment ε δ ≤
        (100 / 99 : ℝ) *
          upperSaddleShellThirdCoefficient ε *
            upperNetShellVariance ε δ := by
    calc
      upperNetShellThirdMoment ε δ ≤
          upperSaddleShellThirdCoefficient ε *
            upperPositiveShellVariance ε δ := by
        simpa [upperSaddleShellThirdCoefficient] using! hthird δ hδ
      _ ≤ upperSaddleShellThirdCoefficient ε *
            ((100 / 99 : ℝ) *
              upperNetShellVariance ε δ) :=
        mul_le_mul_of_nonneg_left htransfer hC
      _ = (100 / 99 : ℝ) *
          upperSaddleShellThirdCoefficient ε *
            upperNetShellVariance ε δ := by
        ring
  unfold upperSaddleThirdMoment upperSaddleVariance
  nlinarith [mul_nonneg hC hgammavariance,
    mul_nonneg hC hnetnonnegative]
end CohnElkies
