-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl1.Wi_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:29:31.31663+00:00
-- url     : https://prove2.me/submissions/ad49294f-2699-4978-9907-6b0e62e3344a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_wSer_low
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_coeff_Wi
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_coeff_Wi


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
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
namespace Formalism.L2.Th1.A.Fgl1
theorem _root_.solution (i j : Fin 2) : (L j) (Wi W i) = 0 := by
  have h0 : coeff 0 (wSer W) = 0 := (wSer_low W).1
  have h1 : coeff 1 (wSer W) = 0 := (wSer_low W).2.1
  rw [coeff_Wi]
  split_ifs
  · simp only [Finsupp.single_apply]
    split_ifs <;> simp [h0, h1]
  · rfl
end Formalism.L2.Th1.A.Fgl1
