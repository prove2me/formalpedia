-- Prove2me | solution 1 for Formalism.ELL.FormalGroupQuadraticJets.linearCoeff_zero_subst_X1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:49.031089+00:00
-- url     : https://prove2.me/submissions/6fde0c72-97c9-4ab8-a77f-482139d189d0

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
    ccd 0 (g.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K)) = 0 := by
  unfold ccd
  rw [pderiv_zero_subst_X1]
  simp
end Formalism.ELL.FormalGroupQuadraticJets
