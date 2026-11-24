-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.selfDual_restr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:21:54.757838+00:00
-- url     : https://prove2.me/submissions/9b05884f-e363-428b-809e-c637d16b9a0d

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SelfDualRestr
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGB_mem_iff_split

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V]
variable {S : Subring K}
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : ∀ u v, star (h u v) = h v u) {M : AddSubgroup V}
    (hM : IsSelfDualMod S h M) {X : V} (hXM : X ∈ M) (hXu : IsUnitIn S (h X X)) :
    IsSelfDualMod S (restr h (LinearMap.ker (h X)))
      (M.comap ((LinearMap.ker (h X)).subtype : LinearMap.ker (h X) →ₗ[K] V).toAddMonoidHom) where
  smul_mem := fun a ha m hm => by
    change ((a • m : LinearMap.ker (h X)) : V) ∈ M
    rw [Submodule.coe_smul]
    exact hM.smul_mem a ha _ hm
  int := fun x hx y hy => hM.int _ hx _ hy
  dual := fun x hx => by
    change (x : V) ∈ M
    apply hM.dual
    intro m hm
    have hpm : ((proj h X hXu.1 m : LinearMap.ker (h X)) : V) ∈ M := ((mem_iff_split hM hXM hXu m).1 hm).2
    have e : h m x = h (proj h X hXu.1 m) x := by
      conv_lhs => rw [decomp h X hXu.1 m]
      rw [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, LinearMap.mem_ker.1 x.2,
        smul_zero, zero_add]
    rw [e]
    exact hx (proj h X hXu.1 m) hpm
  span := fun x => by
    obtain ⟨t, ht, htx⟩ := hM.span (x : V)
    exact ⟨t, ht, by change ((t • x : LinearMap.ker (h X)) : V) ∈ M; rw [Submodule.coe_smul]; exact htx⟩
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
