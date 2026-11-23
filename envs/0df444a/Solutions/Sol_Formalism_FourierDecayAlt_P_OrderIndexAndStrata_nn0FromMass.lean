-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrderIndexAndStrata.nn0FromMass
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:08.224637+00:00
-- url     : https://prove2.me/submissions/9c91a088-4147-4583-9b41-0ca9cbacc0e9

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
theorem _root_.solution : DensityFromMassFormula := by
  intro P _ B hB
  obtain ⟨hp, hμKo, -, -, -, hU00o, -, -, -, -, -, -, hvolZZ, -, hal, -, -, -, -, -, -, -, -, -, -,
    hCoo, -⟩ := hB
  have hU : 0 < B.unitLevelVolume :=
    mul_pos hU00o (Finset.prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.2.2)
  have hK : 0 < B.μK := mul_pos hμKo (Finset.prod_pos fun p _ => (hp p).2.2.2.2.2.1)
  have h1 := hU.ne'
  have h2 := hK.ne'
  have h3 := hal.ne'
  have h4 := hvolZZ.ne'
  have h5 := hCoo.ne'
  simp only [MassData.nn0, MassData.AA]
  field_simp <;> ring
end Formalism.FourierDecayAlt.P.OrderIndexAndStrata
