-- Prove2me | solution 1 for Formalism.ELL.FormalGroupQuadraticJets.linearCoeff_one_subst_X0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:49.044018+00:00
-- url     : https://prove2.me/submissions/82476a9f-6918-4f7a-9cff-eee544be6a4e

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_pderiv_one_subst_X0

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
theorem _root_.solution (g : PowerSeries K) :
    ccd 1 (g.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K)) = 0 := by
  unfold ccd
  rw [pderiv_one_subst_X0]
  simp
end Formalism.ELL.FormalGroupQuadraticJets
