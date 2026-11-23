-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.J1.recursion_gives_densityData_after
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:46:51.520997+00:00
-- url     : https://prove2.me/submissions/1c28b1fa-2cd7-42c5-b3a9-17c465ee742c

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexOrder ComplexConjugate
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
theorem _root_.solution : RecursionGivesUniformBoundsAfter := by
  intro hA C₁ C₄ h1 h4
  obtain ⟨C, C', hC⟩ := hA C₁ C₄ h1 h4
  refine ⟨C, C', ?_⟩
  intro E W _ D Θ jn H _ _ _ Vt c hR hC' hr h0 P _ B hI hδ hS
  unfold RecHypAfter at hR
  obtain ⟨hK, hf, hΘ, hSz, hG, hKr, hWd, hA2, hEb, hDA, hEW, hP, hEL, hEB, hLS, hEE, hCut, hA4⟩ := hR
  have hp : ∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i) = 1 :=
    Finset.prod_eq_one (fun i hi => by rw [h0 i hi, add_zero])
  have hb := hC E W D Θ jn H Vt c hK hf hΘ hC' hr hSz hG hKr hWd hA2 hEb hDA hEW hP hEL hEB hLS hEE
    hCut hA4
  rw [hp, mul_one] at hb
  unfold S3.MassData.InTheoremA
  rw [hI, hδ]
  exact hS _ hb
end Formalism.FourierDecayAlt.P.RecursionWithDensities.J1
