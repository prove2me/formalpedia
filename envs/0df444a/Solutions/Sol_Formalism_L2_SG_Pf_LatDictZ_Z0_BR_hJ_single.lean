-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.BR.hJ_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:39:24.432857+00:00
-- url     : https://prove2.me/submissions/77b0fabe-5d7a-4f0e-8300-3b1ff04cf981

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_UnimodOfSelfDual
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_hJ_apply
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
theorem _root_.solution (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (j : Fin n) :
    hJ J x (Pi.single j 1) = (Matrix.vecMul (fun i => starRingEnd E (x i)) J) j := by
  rw [hJ_apply, Formalism.UG.hform, Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp
end Formalism.L2.SG.Pf.LatDictZ.Z0.BR
