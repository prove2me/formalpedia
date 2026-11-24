-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z3.isSelfDualMod_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:00:35.269844+00:00
-- url     : https://prove2.me/submissions/bcacd652-570d-482a-a9c0-a584f27ca87a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc

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
theorem _root_.solution (F : V ≃ₗ[K] V) (hF : ∀ x y, h (F x) (F y) = h x y)
    (hM : IsSelfDualMod S h M) : IsSelfDualMod S h (M.comap F.symm.toLinearMap.toAddMonoidHom) where
  smul_mem a ha m hm := by
    change F.symm (a • m) ∈ M
    rw [map_smul]
    exact hM.smul_mem a ha _ hm
  int x hx y hy := by
    have e := hF (F.symm x) (F.symm y)
    rw [F.apply_symm_apply, F.apply_symm_apply] at e
    rw [e]
    exact hM.int _ hx _ hy
  dual x hx := by
    change F.symm x ∈ M
    apply hM.dual
    intro m hm
    have e := hF m (F.symm x)
    rw [F.apply_symm_apply] at e
    rw [← e]
    apply hx
    change F.symm (F m) ∈ M
    rw [F.symm_apply_apply]
    exact hm
  span x := by
    obtain ⟨t, ht0, htx⟩ := hM.span (F.symm x)
    exact ⟨t, ht0, by change F.symm (t • x) ∈ M; rw [map_smul]; exact htx⟩
end Formalism.L2.SG.Pf.LatDictZ.Z3
