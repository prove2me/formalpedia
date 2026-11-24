-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z3.mem_iff_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:01:37.302187+00:00
-- url     : https://prove2.me/submissions/9cfa9675-3787-4998-8ccb-253ee2ac6160

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc
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
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z3
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {P : Submodule K V} {S : Subring K} {M M₁ M₂ : AddSubgroup V}
namespace Formalism.L2.SG.Pf.LatDictZ.Z3
theorem _root_.solution {Q : Submodule K V} (hc : IsCompl P Q)
    (hsp : ∀ w ∈ M, ∃ w₁ ∈ M, w₁ ∈ P ∧ w - w₁ ∈ Q) (x : V) :
    x ∈ M ↔ (((Submodule.prodEquivOfIsCompl P Q hc).symm x).1 : V) ∈ M ∧
      (((Submodule.prodEquivOfIsCompl P Q hc).symm x).2 : V) ∈ M := by
  constructor
  · intro hx
    obtain ⟨w₁, hw₁M, hw₁P, hw₁⟩ := hsp x hx
    have e : (Submodule.prodEquivOfIsCompl P Q hc).symm x = (⟨w₁, hw₁P⟩, ⟨x - w₁, hw₁⟩) := by
      rw [LinearEquiv.symm_apply_eq, Submodule.coe_prodEquivOfIsCompl']
      simp
    rw [e]
    exact ⟨hw₁M, M.sub_mem hx hw₁M⟩
  · rintro ⟨h1, h2⟩
    have e := (Submodule.prodEquivOfIsCompl P Q hc).apply_symm_apply x
    rw [Submodule.coe_prodEquivOfIsCompl'] at e
    rw [← e]
    exact M.add_mem h1 h2
end Formalism.L2.SG.Pf.LatDictZ.Z3
