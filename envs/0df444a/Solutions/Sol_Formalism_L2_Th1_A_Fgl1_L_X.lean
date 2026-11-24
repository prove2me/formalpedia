-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl1.L_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:19:32.82745+00:00
-- url     : https://prove2.me/submissions/f1814cf9-3823-4fd1-af86-d07a2a8b08e5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries

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
open Formalism.L2.Th1.A.Fgl1
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
namespace Formalism.L2.Th1.A.Fgl1
theorem _root_.solution (i j : Fin 2) :
    (L i) (MvPowerSeries.X j : MvPowerSeries (Fin 2) R) = if i = j then 1 else 0 := by
  simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero]
end Formalism.L2.Th1.A.Fgl1
