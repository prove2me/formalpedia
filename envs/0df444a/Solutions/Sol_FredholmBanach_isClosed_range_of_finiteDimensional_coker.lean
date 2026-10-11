-- Prove2me | solution 1 for FredholmBanach.isClosed_range_of_finiteDimensional_coker
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T17:52:03.233403+00:00
-- url     : https://prove2.me/submissions/092dd49c-46b3-47bc-88a2-eb256c454635

import Definitions.Def_FredholmBanach_Setting
import Mathlib.Analysis.Normed.Operator.Perturbation.StrictByFinite
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Operator.Banach

open Topology

theorem solution {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (u : E →L[𝕜] F) (hu : FiniteDimensional 𝕜 (F ⧸ u.range)) :
    IsClosed (u.range : Set F) ∧ IsStrictMap u := by
  -- an algebraic complement `G` of the range; it is finite-dimensional
  obtain ⟨G, hG⟩ := Submodule.exists_isCompl (LinearMap.range u.toLinearMap)
  haveI : FiniteDimensional 𝕜 G :=
    LinearEquiv.finiteDimensional (Submodule.quotientEquivOfIsCompl _ G hG)
  have hGc : G.ClosedComplemented := Submodule.ClosedComplemented.of_finiteDimensional G
  -- the induced map `E → F ⧸ G` is surjective
  have hsurj : Function.Surjective (G.mkQL ∘L u) := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective G y
    have hy : y ∈ LinearMap.range u.toLinearMap ⊔ G := by rw [hG.sup_eq_top]; trivial
    obtain ⟨a, ⟨x, rfl⟩, g, hg, rfl⟩ := Submodule.mem_sup.mp hy
    refine ⟨x, ?_⟩
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, Submodule.mkQL_apply]
    rw [map_add, Submodule.mkQ_apply G g, (Submodule.Quotient.mk_eq_zero G).mpr hg, add_zero]
    rfl
  -- transport to a closed (hence complete) topological complement `S ≃L F ⧸ G`
  obtain ⟨S, hGS⟩ := hGc.exists_isTopCompl
  let Φ : (F ⧸ G) ≃L[𝕜] S := G.quotientEquivOfIsTopCompl S hGS
  haveI : CompleteSpace S := hGS.symm.isClosed.completeSpace_coe
  have hq0 : IsStrictMap ((Φ : (F ⧸ G) →L[𝕜] S) ∘L (G.mkQL ∘L u)) :=
    (ContinuousLinearMap.isQuotientMap _ (Φ.surjective.comp hsurj)).isStrictMap
  have hq : IsStrictMap (G.mkQL ∘L u) :=
    (Φ.toHomeomorph.comp_isStrictMap_iff).mp hq0
  have key := (u.isStrictMap_isClosed_range_iff_quotient G hGc).mpr
    ⟨hq,
      by rw [LinearMap.range_eq_top.mpr hsurj]; exact isClosed_univ⟩
  exact ⟨key.2, key.1⟩
