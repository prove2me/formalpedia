-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrderIndexAndStrata.tb_all
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:01.420675+00:00
-- url     : https://prove2.me/submissions/31b70055-e0fd-463c-8e60-fa21eb72e8d9

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
theorem _root_.solution : tb.Pos ∧ tb.InTwoA ∧ tb.InForm ∧ tb.InKernel ∧ tb.InMass ∧ tb.InDens ∧ tb.InTheoremA ∧
    tb.InJacMod ∧ tb.InNu ∧ tb.InInfinity ∧ tb.InVolumes ∧ tb.InLevelS ∧ tb.InMasses ∧ tb.InColumns ∧
    tb.InOrdinary ∧ tb.InTyped ∧ tb.InIndices := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [MassData.Pos, MassData.InTwoA, MassData.InForm, MassData.InKernel, MassData.InMass, MassData.InDens, MassData.InTheoremA, MassData.InJacMod, MassData.InNu, MassData.InInfinity, MassData.InVolumes, MassData.InLevelS, MassData.InMasses, MassData.InColumns, MassData.InOrdinary, MassData.InTyped, MassData.InIndices, MassData.tt, MassData.Gam1, MassData.ga, MassData.AA, MassData.MM, MassData.μK, MassData.unitLevelVolume, MassData.Smod, MassData.c0, MassData.c0', MassData.μS, MassData.μSpp, MassData.μS', MassData.μSpp', MassData.Dstar, MassData.μKpp, MassData.GS, tb, Finset.univ_unique, Finset.prod_singleton]
end Formalism.FourierDecayAlt.P.OrderIndexAndStrata
