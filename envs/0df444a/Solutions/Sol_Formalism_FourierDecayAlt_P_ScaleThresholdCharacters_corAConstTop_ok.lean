-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.corAConstTop_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:40.513796+00:00
-- url     : https://prove2.me/submissions/29b3e2b6-630f-4d3b-a55b-a88b1956bef5

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScaleThresholdCharacters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ScaleThresholdCharacters
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.ScaleThresholdCharacters
theorem _root_.solution : CorAConstTop := by
  have hRZ : ∀ (Rw ZZ BB TT : ℝ), 0 < TT → 0 ≤ Rw → Rw ≤ Real.exp (1 / 2) → 0 ≤ ZZ →
      ZZ ≤ Real.exp (1 / 2) * BB * TT ^ (-(1 / 2 : ℝ)) →
      Rw * ZZ ≤ Real.exp (3 / 2) * (BB * TT ^ (-(1 / 2 : ℝ))) := by
    intro Rw ZZ BB TT hTT hR hR' hZ hZ'
    have hp := Real.exp_pos (1 / 2)
    have hBs : 0 ≤ BB * TT ^ (-(1 / 2 : ℝ)) := by
      have h0 : 0 ≤ Real.exp (1 / 2) * (BB * TT ^ (-(1 / 2 : ℝ))) := by
        rw [← mul_assoc]; exact hZ.trans hZ'
      exact (mul_nonneg_iff_of_pos_left hp).mp h0
    calc Rw * ZZ ≤ Real.exp (1 / 2) * (Real.exp (1 / 2) * (BB * TT ^ (-(1 / 2 : ℝ)))) :=
          mul_le_mul hR' (by rw [← mul_assoc]; exact hZ') hZ hp.le
      _ = Real.exp 1 * (BB * TT ^ (-(1 / 2 : ℝ))) := by rw [← mul_assoc, ← Real.exp_add]; norm_num
      _ ≤ Real.exp (3 / 2) * (BB * TT ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by norm_num)) hBs
  refine ⟨?_, ?_⟩
  · intro n ell Rw ZZ BB TT hell hn hTT hR hR' hZ hZ'
    have h := hRZ Rw ZZ BB TT hTT hR hR' hZ hZ'
    calc ((1 / 2) * (4 / ell) ^ n) ^ 2 * Rw * ZZ = (1 / 4) * ((4 / ell) ^ n) ^ 2 * (Rw * ZZ) := by ring
      _ ≤ (1 / 4) * ((4 / ell) ^ n) ^ 2 * (Real.exp (3 / 2) * (BB * TT ^ (-(1 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = Real.exp (3 / 2) * (1 / 4) * (4 / ell) ^ (2 * n) * BB * TT ^ (-(1 / 2 : ℝ)) := by
          rw [show 2 * n = n * 2 by ring, pow_mul]; ring
  · intro Rw ZZ BB TT hTT hR hR' hZ hZ'
    have h := hRZ Rw ZZ BB TT hTT hR hR' hZ hZ'
    linarith [h, show Real.exp (3 / 2) * (BB * TT ^ (-(1 / 2 : ℝ))) =
      Real.exp (3 / 2) * BB * TT ^ (-(1 / 2 : ℝ)) by ring]
end Formalism.FourierDecayAlt.P.ScaleThresholdCharacters
