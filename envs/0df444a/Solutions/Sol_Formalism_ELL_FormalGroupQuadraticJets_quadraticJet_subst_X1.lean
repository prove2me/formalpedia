-- Prove2me | solution 1 for Formalism.ELL.FormalGroupQuadraticJets.quadraticJet_subst_X1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:49.468398+00:00
-- url     : https://prove2.me/submissions/690a53e3-8ab9-47d6-b42b-66786ce9646e

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_pderiv_zero_subst_X1

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
    Q (g.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K)) = 0 := by
  unfold Q
  rw [pderiv_zero_subst_X1]
  simp
end Formalism.ELL.FormalGroupQuadraticJets
