-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z3.isSelfDualMod_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:23:10.411868+00:00
-- url     : https://prove2.me/submissions/d62d134e-c152-4c2f-aac3-e4903b195c37

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_mem_orth
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_mem_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z3
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {P : Submodule K V} {S : Subring K} {M M₁ M₂ : AddSubgroup V}
namespace Formalism.L2.SG.Pf.LatDictZ.Z3
theorem _root_.solution (hM : IsSelfDualMod S h M) (hsp : Splits h P M) :
    IsSelfDualMod S (h.domRestrict₁₂ (orth h P) (orth h P))
      (M.comap (orth h P).subtype.toAddMonoidHom) where
  smul_mem a ha m hm := by
    rw [mem_res, Submodule.coe_smul]
    exact hM.smul_mem a ha _ (mem_res.mp hm)
  int x hx y hy := by
    rw [LinearMap.domRestrict₁₂_apply]
    exact hM.int _ (mem_res.mp hx) _ (mem_res.mp hy)
  dual x hx := by
    rw [mem_res]
    apply hM.dual
    intro m hm
    obtain ⟨w₁, hw₁M, hw₁P, hw₁⟩ := hsp m hm
    have e : h m x = h w₁ x + h (m - w₁) x := by
      rw [map_sub, LinearMap.sub_apply]
      ring
    have e1 : h w₁ x = 0 := mem_orth.mp x.2 w₁ hw₁P
    have e2 := hx ⟨m - w₁, hw₁⟩ (mem_res.mpr (M.sub_mem hm hw₁M))
    rw [LinearMap.domRestrict₁₂_apply] at e2
    rw [e, e1, zero_add]
    exact e2
  span x := by
    obtain ⟨t, ht0, htx⟩ := hM.span x
    exact ⟨t, ht0, mem_res.mpr (by rw [Submodule.coe_smul]; exact htx)⟩
end Formalism.L2.SG.Pf.LatDictZ.Z3
