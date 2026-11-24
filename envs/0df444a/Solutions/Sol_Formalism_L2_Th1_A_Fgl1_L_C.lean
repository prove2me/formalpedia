-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl1.L_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:19:31.670795+00:00
-- url     : https://prove2.me/submissions/74b1d58a-f52f-46d0-8a78-e6d305c6c43b

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
theorem _root_.solution (a : R) (i : Fin 2) : (L i) (MvPowerSeries.C a : MvPowerSeries (Fin 2) R) = 0 := by
  simp [MvPowerSeries.coeff_C]
end Formalism.L2.Th1.A.Fgl1
