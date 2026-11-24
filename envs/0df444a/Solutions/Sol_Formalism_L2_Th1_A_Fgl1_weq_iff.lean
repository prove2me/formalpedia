-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl1.weq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:20:13.853675+00:00
-- url     : https://prove2.me/submissions/ba870dcd-d6a1-4b5b-87ff-3a66fba91213

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
open Formalism.ELL.WeierstrassChordSeries
namespace Formalism.L2.Th1.A.Fgl1
theorem _root_.solution (W : WeierstrassCurve R) (s v : MvPowerSeries (Fin 2) R) :
    Formalism.ELL.WEqAt W s v ↔ G (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃)
      (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) s v = 0 := by
  unfold Formalism.ELL.WEqAt G
  simp only [MvPowerSeries.smul_eq_C_mul]
  constructor
  · intro h
    linear_combination (-1 : MvPowerSeries (Fin 2) R) * h
  · intro h
    linear_combination (-1 : MvPowerSeries (Fin 2) R) * h
end Formalism.L2.Th1.A.Fgl1
