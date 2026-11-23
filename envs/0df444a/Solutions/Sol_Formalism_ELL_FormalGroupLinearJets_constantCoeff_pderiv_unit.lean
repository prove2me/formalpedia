-- Prove2me | solution 1 for Formalism.ELL.FormalGroupLinearJets.constantCoeff_pderiv_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:09.738285+00:00
-- url     : https://prove2.me/submissions/1eace711-98de-4a47-ac93-c5e020fc10f6

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupLinearJets
variable {K : Type u} [CommRing K]
namespace Formalism.ELL.FormalGroupLinearJets
theorem _root_.solution (f : PowerSeries K) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv K () f) = coeff 1 f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp [PowerSeries.coeff]
end Formalism.ELL.FormalGroupLinearJets
