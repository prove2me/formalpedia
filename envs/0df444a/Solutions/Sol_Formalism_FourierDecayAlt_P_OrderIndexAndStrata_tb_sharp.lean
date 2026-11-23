-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrderIndexAndStrata.tb_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:02.00374+00:00
-- url     : https://prove2.me/submissions/37bfd7b2-e101-4db3-b1bb-a5284a86816b

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrderIndexAndStrata
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni)
open Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.OrderIndexAndStrata
theorem _root_.solution : tb.GS = (1 + tb.δ) * tb.e1 * tb.tt * (tb.d * tb.d' / tb.Dstar) ∧ tb.Gam1 = 3 ∧
    tb.GS = 4/5 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [MassData.Pos, MassData.InTwoA, MassData.InForm, MassData.InKernel, MassData.InMass, MassData.InDens, MassData.InTheoremA, MassData.InJacMod, MassData.InNu, MassData.InInfinity, MassData.InVolumes, MassData.InLevelS, MassData.InMasses, MassData.InColumns, MassData.InOrdinary, MassData.InTyped, MassData.InIndices, MassData.tt, MassData.Gam1, MassData.ga, MassData.AA, MassData.MM, MassData.μK, MassData.unitLevelVolume, MassData.Smod, MassData.c0, MassData.c0', MassData.μS, MassData.μSpp, MassData.μS', MassData.μSpp', MassData.Dstar, MassData.μKpp, MassData.GS, tb, Finset.univ_unique, Finset.prod_singleton]
end Formalism.FourierDecayAlt.P.OrderIndexAndStrata
