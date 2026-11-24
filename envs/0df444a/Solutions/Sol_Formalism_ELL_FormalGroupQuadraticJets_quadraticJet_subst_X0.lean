-- Prove2me | solution 1 for Formalism.ELL.FormalGroupQuadraticJets.quadraticJet_subst_X0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:49.05795+00:00
-- url     : https://prove2.me/submissions/6521bc2f-8944-487b-a2af-47345653b8eb

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_pderiv_one_subst_X0
import Theorems.Thm_Formalism_G_LogCR_pderiv_psubst


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
    Q (g.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K)) = 0 := by
  unfold Q
  rw [pderiv_psubst (MvPowerSeries.constantCoeff_X _)]
  simp [MvPowerSeries.pderiv_X, pderiv_one_subst_X0]
end Formalism.ELL.FormalGroupQuadraticJets
