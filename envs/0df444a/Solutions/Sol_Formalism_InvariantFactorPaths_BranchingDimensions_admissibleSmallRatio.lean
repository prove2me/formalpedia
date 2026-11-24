-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.admissibleSmallRatio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:49.141237+00:00
-- url     : https://prove2.me/submissions/dc3cab1d-e2e8-40a6-81f2-992754d76638

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementN
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AdmissibleSmallRatio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution : AdmissibleSmallRatio := by
  intro p k Ns D1 L1 R R' a Y Qn be hp hk hNs hY ha hQn hL1 hbe h7 h8
  have hP : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hP0 : (0:ℝ) < p := by linarith
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hNs' : (1:ℝ) ≤ Ns := by exact_mod_cast hNs
  have hY0 : (0:ℝ) < Y := by linarith
  have hk0 : (0:ℝ) < k := by linarith
  have hNs0 : (0:ℝ) < Ns := by linarith
  have hR : (0:ℝ) < (p:ℝ)^R := pow_pos hP0 _
  have hR' : (0:ℝ) < (p:ℝ)^R' := pow_pos hP0 _
  have hD1 : (0:ℝ) < (p:ℝ)^D1 := pow_pos hP0 _
  have hL : (0:ℝ) < (p:ℝ)^L1 := pow_pos hP0 _
  have hT : (0:ℝ) < Qn * (p:ℝ)^R' / (p:ℝ)^R := by positivity
  have sA : be / (Qn * (p:ℝ)^R' / (p:ℝ)^R) ≤
      (4 * a / (p:ℝ)^(R+D1+L1+1)) / (Qn * (p:ℝ)^R' / (p:ℝ)^R) :=
    div_le_div_of_nonneg_right hbe hT.le
  have sB : (4 * a / (p:ℝ)^(R+D1+L1+1)) / (Qn * (p:ℝ)^R' / (p:ℝ)^R) =
      4 * a / ((p:ℝ)^D1 * (p:ℝ)^L1 * p * (Qn * (p:ℝ)^R')) := by
    rw [show R+D1+L1+1 = R + D1 + L1 + 1 from rfl, pow_succ, pow_add, pow_add]
    field_simp
  have ha7 : a < (p:ℝ)^R' * (8 * p * Y * (k:ℝ)^2 * Ns * ((p:ℝ)^D1 * Qn)) := by
    rwa [div_lt_iff₀ (by positivity)] at h7
  have sC : 4 * a / ((p:ℝ)^D1 * (p:ℝ)^L1 * p * (Qn * (p:ℝ)^R')) <
      32 * Y * (k:ℝ)^2 * Ns / (p:ℝ)^L1 := by
    rw [div_lt_div_iff₀ (by positivity) hL]
    have := mul_lt_mul_of_pos_left ha7 (show (0:ℝ) < 4 * (p:ℝ)^L1 by positivity)
    nlinarith
  have hPL : (p:ℝ)^L1 = (p:ℝ)^(L1-1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  have s2 : 32 * Y * (k:ℝ)^2 * Ns / (p:ℝ)^L1 ≤ 1 / (4 * p * Y) := by
    rw [div_le_div_iff₀ hL (by positivity), hPL]
    have := mul_le_mul_of_nonneg_right h8 hP0.le
    nlinarith
  have s1 : be / (Qn * (p:ℝ)^R' / (p:ℝ)^R) < 32 * Y * (k:ℝ)^2 * Ns / (p:ℝ)^L1 := by
    rw [sB] at sA
    exact lt_of_le_of_lt sA sC
  have s3 : 1 / (4 * p * Y) ≤ 1 / (4 * Y) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  exact ⟨s1, s2, by linarith⟩
end Formalism.InvariantFactorPaths.BranchingDimensions
