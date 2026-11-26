-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_movingLow_admissible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:36.934076+00:00
-- url     : https://prove2.me/submissions/3b50c94b-1e5a-4acd-a2d8-a08cc8ddaa07

import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Theorems.Thm_FirstPassageLinearTransport_tendsto_movingLowTolerance
import Theorems.Thm_FirstPassageLinearTransport_tendsto_movingLowRatio
import Theorems.Thm_FirstPassageLinearTransport_tendsto_movingLowLambda
import Theorems.Thm_FirstPassageLinearTransport_tendsto_movingLowCorrectionGap
import Theorems.Thm_FirstPassageLinearTransport_two_mul_a0_sub_one_pos
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {K₀ K₁ : ℝ} (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) :
    ∀ᶠ L : ℕ in atTop,
      0 < movingLowTolerance K₀ L ∧
      movingLowTolerance K₀ L < driftGap ∧
      0 < movingLowRatio K₀ L ∧ movingLowRatio K₀ L < 1 ∧
      0 < movingLowLambda K₁ L ∧ movingLowLambda K₁ L < 1 ∧
      0 < a0 + movingLowTolerance K₀ L -
        2 * movingLowLambda K₁ L * movingLowTolerance K₀ L := by
  have htolPos := (tendsto_movingLowTolerance K₀).eventually
    (Ioi_mem_nhds driftGap_pos)
  have hratioPos := (tendsto_movingLowRatio K₀).eventually
    (Ioi_mem_nhds zero_lt_one)
  have hlamPos := (tendsto_movingLowLambda K₁).eventually
    (Ioi_mem_nhds zero_lt_one)
  have hcorrPos := (tendsto_movingLowCorrectionGap K₀ K₁).eventually
    (Ioi_mem_nhds two_mul_a0_sub_one_pos)
  filter_upwards [htolPos, hratioPos, hlamPos, hcorrPos,
      eventually_ge_atTop (1 : ℕ)] with L htol hratio hlam hcorr hL
  have hLR : 0 < (L : ℝ) := by positivity
  have htolLt : movingLowTolerance K₀ L < driftGap := by
    unfold movingLowTolerance
    have : 0 < K₀ / (L : ℝ) := div_pos hK₀ hLR
    linarith
  have hratioLt : movingLowRatio K₀ L < 1 := by
    unfold movingLowRatio
    have : 0 < K₀ / (2 * (L : ℝ)) := div_pos hK₀ (by positivity)
    linarith
  have hlamLt : movingLowLambda K₁ L < 1 := by
    unfold movingLowLambda
    have : 0 < K₁ / (L : ℝ) := div_pos hK₁ hLR
    linarith
  exact ⟨htol, htolLt, hratio, hratioLt, hlam, hlamLt, hcorr⟩
end FirstPassageLinearTransport
