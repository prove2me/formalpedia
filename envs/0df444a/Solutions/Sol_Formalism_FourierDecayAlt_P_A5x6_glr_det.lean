-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x6.glr_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:21.459582+00:00
-- url     : https://prove2.me/submissions/39747879-b9e5-48bc-a790-06b0cb5936fd

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_pt_det_isUnit
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_det_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x6
namespace Formalism.FourierDecayAlt.P.A5x6
theorem _root_.solution {K : Type} [CommRing K] (R : Subring K) (h : Point K) (hh : InGLR R h) :
    (pt h.1 h.2).det ∈ R ∧ (pt h.1 h.2)⁻¹.det ∈ R ∧ (pt h.1 h.2).det * (pt h.1 h.2)⁻¹.det = 1 := by
  obtain ⟨h1, h2⟩ := hh
  refine ⟨det_mem R _ h1, det_mem R _ h2, ?_⟩
  rw [Matrix.det_nonsing_inv, Ring.mul_inverse_cancel _ (pt_det_isUnit h)]
end Formalism.FourierDecayAlt.P.A5x6
