-- Prove2me | solution 1 for Formalism.L2.Th1.A.CubeR.map_formal_group_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:13:26.848797+00:00
-- url     : https://prove2.me/submissions/62021559-acfa-4a38-88e5-6b4684dda0c4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_pair_vector_map
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_hasSubst2
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_hasSubst2
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_fgl_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.CubeR
open Univ CurveSer
local notation "cc" => MvPowerSeries.constantCoeff
variable {σ : Type*} {A : Type u} {B : Type v} [CommRing A] [CommRing B]
namespace Formalism.L2.Th1.A.CubeR
theorem _root_.solution (φ : A →+* B) (W : WeierstrassCurve A) {a b : MvPowerSeries σ A}
    (ha : cc a = 0) (hb : cc b = 0) :
    MvPowerSeries.map φ (MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ A) (fgl W))
      = MvPowerSeries.subst
          (![MvPowerSeries.map φ a, MvPowerSeries.map φ b] : Fin 2 → MvPowerSeries σ B)
          (fgl (W.map φ)) := by
  rw [MvPowerSeries.map_subst (hasSubst2 ha hb), pair_vector_map, Fgl1.fgl_map]
end Formalism.L2.Th1.A.CubeR
