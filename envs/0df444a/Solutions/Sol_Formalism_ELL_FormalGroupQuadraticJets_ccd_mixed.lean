-- Prove2me | solution 1 for Formalism.ELL.FormalGroupQuadraticJets.ccd_mixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:43.315191+00:00
-- url     : https://prove2.me/submissions/c5837141-6a54-440e-bc42-0831da60a317

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_ccd_single

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
variable {K : Type*} [CommRing K]
namespace Formalism.ELL.FormalGroupQuadraticJets
theorem _root_.solution (F : MvPowerSeries (Fin 2) K) :
    ccd 1 (MvPowerSeries.pderiv K 0 F) = ccd 0 (MvPowerSeries.pderiv K 1 F) := by
  rw [ccd_single, ccd_single, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv,
    add_comm (Finsupp.single (1 : Fin 2) 1)]
  simp
end Formalism.ELL.FormalGroupQuadraticJets
