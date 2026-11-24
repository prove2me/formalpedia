-- Prove2me | solution 1 for Formalism.L2.Th1.A.CubeR.pair_vector_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:19:19.375556+00:00
-- url     : https://prove2.me/submissions/ba8c5cd4-1023-41f7-baba-e78feca0010a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero

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
theorem _root_.solution (φ : A →+* B) (a b : MvPowerSeries σ A) :
    (fun i => MvPowerSeries.map φ ((![a, b] : Fin 2 → MvPowerSeries σ A) i))
      = ![MvPowerSeries.map φ a, MvPowerSeries.map φ b] := by
  funext i; fin_cases i <;> rfl
end Formalism.L2.Th1.A.CubeR
