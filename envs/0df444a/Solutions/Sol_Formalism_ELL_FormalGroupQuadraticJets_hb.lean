-- Prove2me | solution 1 for Formalism.ELL.FormalGroupQuadraticJets.hb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:59.389116+00:00
-- url     : https://prove2.me/submissions/b334a893-bcb8-4bde-a3e2-84b276fbd06a

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupQuadraticJets
open Formalism.G.LogCR
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
namespace Formalism.ELL.FormalGroupQuadraticJets
theorem _root_.solution : ∀ j, MvPowerSeries.constantCoeff
    ((![PowerSeries.X, (0 : PowerSeries K)] : Fin 2 → PowerSeries K) j) = 0 := by
  intro j
  fin_cases j
  · exact MvPowerSeries.constantCoeff_X _
  · simp
end Formalism.ELL.FormalGroupQuadraticJets
