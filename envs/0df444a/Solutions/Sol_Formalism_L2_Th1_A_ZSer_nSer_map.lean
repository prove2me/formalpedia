-- Prove2me | solution 1 for Formalism.L2.Th1.A.ZSer.nSer_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:29:59.076948+00:00
-- url     : https://prove2.me/submissions/0e80da13-b02a-43c2-a1a1-8aa65659894f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_SubstPairSubst
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_FF_map
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_nSer_zero
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_nSer_succ
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_nSer_cc

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
open Formalism.L2.Th1.A.ZSer
local notation "FF[" W "](" a ", " b ")" =>
  MvPowerSeries.subst (![a, b] : Fin 2 → PowerSeries _) (fgl W)
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
namespace Formalism.L2.Th1.A.ZSer
theorem _root_.solution {S : Type v} [CommRing S] (φ : R →+* S) (n : ℕ) :
    PowerSeries.map φ (nSer W n) = nSer (W.map φ) n := by
  induction n with
  | zero => rw [nSer_zero, nSer_zero, map_zero]
  | succ n ih =>
    rw [nSer_succ, nSer_succ, FF_map W φ constantCoeff_X (nSer_cc W n), ih, PowerSeries.map_X]
end Formalism.L2.Th1.A.ZSer
