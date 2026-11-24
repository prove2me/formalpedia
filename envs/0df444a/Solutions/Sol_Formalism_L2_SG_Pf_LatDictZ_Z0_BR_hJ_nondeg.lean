-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.BR.hJ_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:03:26.247798+00:00
-- url     : https://prove2.me/submissions/19b8c0ab-8002-4ac6-af4a-e09f2db9dc18

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_UnimodOfSelfDual
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_hJ_single
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.BR
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA PIW.AdelClassFin
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.BR
theorem _root_.solution {J : Matrix (Fin n) (Fin n) E} (hdet : J.det ≠ 0) (x : Fin n → E)
    (hx : ∀ y, hJ J x y = 0) : x = 0 := by
  have h0 : Matrix.vecMul (fun i => starRingEnd E (x i)) J = 0 := by
    funext j; rw [← hJ_single]; exact hx _
  have h1 := Matrix.eq_zero_of_vecMul_eq_zero hdet h0
  funext i
  have := congrFun h1 i
  simpa using this
end Formalism.L2.SG.Pf.LatDictZ.Z0.BR
