-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dilation_matrix_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:41:25.896229+00:00
-- url     : https://prove2.me/submissions/1fadf568-f69d-4635-84c0-a7bb1d048422

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cc_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cc_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dil_bound1
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dil_bound2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B.DilCC := by
  intro k r Wp Wq _ _ _ _ A hA
  refine ⟨((4 : ℝ) ^ r) ^ A * (4 ^ r) ^ 5 +
    ((4 : ℝ) ^ r) ^ A * (((4 : ℕ) : ℝ) * ((4 ^ r) ^ (4 + 1) * (8 * 4 ^ r)) + 2 * r), ?_⟩
  intro t ht F c hF
  obtain ⟨h1, h2⟩ := Set.mem_prod.mp ht
  have hc := cc_nonneg hF
  have hδ : 0 ≤ |t.1 - 1| + |t.2 - 1| := by positivity
  have a1 : (0 : ℝ) ≤ ((4 : ℝ) ^ r) ^ A * (4 ^ r) ^ 5 := by positivity
  have a2 : (0 : ℝ) ≤ ((4 : ℝ) ^ r) ^ A * (((4 : ℕ) : ℝ) * ((4 ^ r) ^ (4 + 1) * (8 * 4 ^ r)) + 2 * r) := by
    positivity
  constructor
  · refine cc_mono (dil_bound1 h1 h2 hA hF) ?_
    have := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right a2 :
      ((4 : ℝ) ^ r) ^ A * (4 ^ r) ^ 5 ≤ _) hc
    linarith
  · refine cc_mono (dil_bound2 h1 h2 hA hF) ?_
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left a1 :
      ((4 : ℝ) ^ r) ^ A * (((4 : ℕ) : ℝ) * ((4 ^ r) ^ (4 + 1) * (8 * 4 ^ r)) + 2 * r) ≤ _) hδ) hc
    exact this
end Formalism.FourierDecayAlt.P
