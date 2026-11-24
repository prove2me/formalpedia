-- Prove2me | solution 1 for Formalism.L2.Th1.A.Univ.mv_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:20:28.258171+00:00
-- url     : https://prove2.me/submissions/9165a7b0-4b50-4081-b912-6fb2be19c60e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_P2M_Formalism_L2_Th1_A_Univ___injective_04fee711be81
import Theorems.Thm_Formalism_L2_Th1_A_Univ_mv_map_injective

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
open Formalism.L2.Th1.A.Univ
namespace Formalism.L2.Th1.A.Univ
theorem _root_.solution {σ : Type*} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    {A B : MvPowerSeries σ Z} (h : MvPowerSeries.map ι A = MvPowerSeries.map ι B) :
    MvPowerSeries.map (φ_of W) A = MvPowerSeries.map (φ_of W) B := by
  rw [mv_map_injective ι ι_injective h]
end Formalism.L2.Th1.A.Univ
