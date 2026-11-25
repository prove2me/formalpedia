-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z3.semiGenusZLoc_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:48.42528+00:00
-- url     : https://prove2.me/submissions/6a86fbb8-4c76-413f-8141-4d70e3372dcd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_mem_orth
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_isCompl_orth
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_isSelfDualMod_res
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_res_nondeg
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_glue
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_zOnly
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
namespace Formalism.L2.SG.Pf.LatDictZ.Z3
theorem _root_.solution (h1 : SemiGenusLoc) (h2 : PrimPlaneLoc) : SemiGenusZLoc := by
  intro K _ _ _ V _ _ _ h hK hs hd p hp r s z M₁ M₂ hM₁ hM₂ hsz hag hsp₁ hsp₂ hz₁ hz₂ hp₁ hp₂
  have horth : ∀ x, (∀ a, h (s a) x = 0) → x ∈ orth h (Submodule.span K (Set.range s)) := by
    intro x hx
    rw [mem_orth]
    intro q hq
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact hx a
    | zero => simp
    | add y y' _ _ ihy ihy' => rw [map_add, LinearMap.add_apply, ihy, ihy', add_zero]
    | smul c y _ ihy => rw [map_smulₛₗ, LinearMap.smul_apply, ihy, smul_zero]
  have hspl : ∀ {M : AddSubgroup V}, (∀ w ∈ M, ∃ w₁ ∈ M, w₁ ∈ Submodule.span K (Set.range s) ∧
      ∀ a, h (s a) (w - w₁) = 0) → Splits h (Submodule.span K (Set.range s)) M := by
    intro M hM w hw
    obtain ⟨w₁, hw₁M, hw₁U, hw₁⟩ := hM w hw
    exact ⟨w₁, hw₁M, hw₁U, horth _ hw₁⟩
  have hS₁ := hspl hsp₁
  have hS₂ := hspl hsp₂
  have hc := isCompl_orth hs hd hM₁ hS₁
  have hzW : z ∈ orth h (Submodule.span K (Set.range s)) := horth z hsz
  obtain ⟨g', hg'i, hg'z, hg'M⟩ := zOnly h1 h2 hK (hs.domRestrict _) (res_nondeg hs hd hM₁ hS₁) hp
    (⟨z, hzW⟩ : orth h (Submodule.span K (Set.range s))) _ _ (isSelfDualMod_res hM₁ hS₁)
    (isSelfDualMod_res hM₂ hS₂) hz₁ hz₂ (fun c hc' => hp₁ c hc') (fun c hc' => hp₂ c hc')
  obtain ⟨g, hg, hgU, hgW, hgM⟩ := glue hs hc hS₁ hS₂ hag g' (fun x y => hg'i x y) (fun x => hg'M x)
  refine ⟨g, hg, fun a => hgU _ (Submodule.subset_span ⟨a, rfl⟩), ?_, hgM⟩
  have e := hgW ⟨z, hzW⟩
  rw [hg'z] at e
  exact e
end Formalism.L2.SG.Pf.LatDictZ.Z3
