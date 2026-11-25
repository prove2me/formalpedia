-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.denomO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:56:11.942816+00:00
-- url     : https://prove2.me/submissions/3e18bd4b-a96e-4369-9c34-8a384ebb8e03

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZGlueA
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_iv_OF
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_P2M_PIW_AdelClassFin_lattice_intersection__c78dcf3d0364
import Theorems.Thm_PIW_AdelClassFin_lattice_denominator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z5
open Formalism.MainNotions.S PIW.AdelClassFin Formalism.L2.SG.Pf.LatDictZ
variable (I : AutInst)
namespace Formalism.L2.SG.Pf.LatDictZ.Z5
theorem _root_.solution (w : Fin I.n → I.E) :
    ∃ m : ℕ, 0 < m ∧ algebraMap (𝓞 I.F) (𝓞 I.E) (m : 𝓞 I.F) • w ∈ I.L := by
  obtain ⟨m, hm, h⟩ := lattice_denominator I (iv I w)
  refine ⟨m, hm, lattice_intersection' I _ ?_⟩
  rw [iv_OF]
  simpa using h
end Formalism.L2.SG.Pf.LatDictZ.Z5
