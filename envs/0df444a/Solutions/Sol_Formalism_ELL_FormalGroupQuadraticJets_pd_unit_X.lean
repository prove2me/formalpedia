-- Prove2me | solution 1 for Formalism.ELL.FormalGroupQuadraticJets.pd_unit_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:43.89625+00:00
-- url     : https://prove2.me/submissions/d8b77e59-c198-499f-a8d9-9e38cf75f71d

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
theorem _root_.solution : MvPowerSeries.pderiv K () (PowerSeries.X : PowerSeries K) = 1 := by
  show MvPowerSeries.pderiv K () (MvPowerSeries.X ()) = 1
  simp [MvPowerSeries.pderiv_X]
end Formalism.ELL.FormalGroupQuadraticJets
