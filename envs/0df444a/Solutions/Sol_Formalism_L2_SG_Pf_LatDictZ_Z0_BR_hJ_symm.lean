-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.BR.hJ_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:02:27.917556+00:00
-- url     : https://prove2.me/submissions/871d7b85-6e24-4c7e-a311-8dcca6d22a26

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_UnimodOfSelfDual
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
theorem _root_.solution {J : Matrix (Fin n) (Fin n) E} (hJh : Formalism.UG.IsHerm (starRingEnd E) J) :
    (hJ J).IsSymm := by
  have hJij : ∀ i j, starRingEnd E (J j i) = J i j := fun i j => by
    have := congrFun (congrFun hJh i) j
    simpa [Formalism.UG.cT] using this
  refine ⟨fun x y => ?_⟩
  change starRingEnd E (Formalism.UG.hform (starRingEnd E) J x y) = Formalism.UG.hform (starRingEnd E) J y x
  simp only [Formalism.UG.hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_self_apply, hJij]
  ring
end Formalism.L2.SG.Pf.LatDictZ.Z0.BR
