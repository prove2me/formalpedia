-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.selfDual_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:00:38.96201+00:00
-- url     : https://prove2.me/submissions/e6a14e82-5751-4847-9b8b-866b351faea2

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SelfDualRestr

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
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V} (hM : IsSelfDualMod S h M)
    (g : V ≃ₗ[K] V) (hg : ∀ x y, h (g x) (g y) = h x y) :
    IsSelfDualMod S h (M.comap (g.symm : V →ₗ[K] V).toAddMonoidHom) where
  smul_mem := fun a ha m hm => by
    change g.symm (a • m) ∈ M
    rw [map_smul]; exact hM.smul_mem a ha _ hm
  int := fun x hx y hy => by
    have := hM.int _ hx _ hy
    change h (g.symm x) (g.symm y) ∈ S at this
    rwa [← hg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
  dual := fun x hx => by
    change g.symm x ∈ M
    apply hM.dual
    intro m hm
    have := hx (g m) (by change g.symm (g m) ∈ M; rwa [LinearEquiv.symm_apply_apply])
    rw [← hg m (g.symm x), LinearEquiv.apply_symm_apply]
    exact this
  span := fun x => by
    obtain ⟨t, ht, htx⟩ := hM.span (g.symm x)
    exact ⟨t, ht, by change g.symm (t • x) ∈ M; rwa [map_smul]⟩
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
