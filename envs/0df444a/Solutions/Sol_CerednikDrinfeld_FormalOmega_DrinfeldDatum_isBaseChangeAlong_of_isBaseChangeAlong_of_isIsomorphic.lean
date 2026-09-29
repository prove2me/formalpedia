-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/886d0445-7ca9-5c3d-a31a-e43c387a6781

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem B24ISO.map_mk {R : Type} [CommRing R] (S : Submonoid R) {M N : Type} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) (m : M) (s : S) :
    LocalizedModule.map S g (LocalizedModule.mk m s) = LocalizedModule.mk (g m) s :=
  IsLocalizedModule.map_LocalizedModules S g m s

theorem B24ISO.span_comp {R : Type} [CommRing R] {σ : Type} {N P : Type} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (τ : σ → N) (e : N ≃ₗ[R] P) (h : Submodule.span R (Set.range τ) = ⊤) :
    Submodule.span R (Set.range fun t => e (τ t)) = ⊤ := by
  have : (Set.range fun t => e (τ t)) = e '' Set.range τ := by
    ext p; simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]
  rw [this, show (⇑e '' Set.range τ) = e.toLinearMap '' Set.range τ from rfl, Submodule.span_image, h, Submodule.map_top,
    LinearEquiv.range]

theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    {Q : DrinfeldDatum (K := K) π B} {Q' Q'' : DrinfeldDatum (K := K) π B'}
    (h : Q.IsBaseChangeAlong f Q') (e : Q'.IsIsomorphic Q'') : Q.IsBaseChangeAlong f Q'' := by
  obtain ⟨W⟩ := h
  obtain ⟨E⟩ := e
  refine ⟨{
    N₀_eq := fun x' => (E.N₀_eq x').symm.trans (W.N₀_eq x')
    N₁_eq := fun x' => (E.N₁_eq x').symm.trans (W.N₁_eq x')
    τ₀ := E.τ₀.toLinearMap.comp W.τ₀
    τ₁ := E.τ₁.toLinearMap.comp W.τ₁
    span_range_τ₀ := ?_
    span_range_τ₁ := ?_
    τ₁_Pi₀ := fun t => ?_
    τ₀_Pi₁ := fun t => ?_
    u₀_eq := ?_
    u₁_eq := ?_ }⟩
  · exact B24ISO.span_comp W.τ₀ E.τ₀ W.span_range_τ₀
  · exact B24ISO.span_comp W.τ₁ E.τ₁ W.span_range_τ₁
  · show E.τ₁ (W.τ₁ (Q.Pi₀ t)) = Q''.Pi₀ (E.τ₀ (W.τ₀ t))
    rw [W.τ₁_Pi₀, E.τ₁_Pi₀]
  · show E.τ₀ (W.τ₀ (Q.Pi₁ t)) = Q''.Pi₁ (E.τ₁ (W.τ₁ t))
    rw [W.τ₀_Pi₁, E.τ₀_Pi₁]
  · intro x' v hv hv'' t s hs H
    have hv' : v ∈ Q'.N₀ x' := by rw [E.N₀_eq]; exact hv''
    rw [E.τ₀_u₀ x' v hv' hv'', W.u₀_eq x' v hv hv' t s hs H]
    exact B24ISO.map_mk _ _ _ _
  · intro x' v hv hv'' t s hs H
    have hv' : v ∈ Q'.N₁ x' := by rw [E.N₁_eq]; exact hv''
    rw [E.τ₁_u₁ x' v hv' hv'', W.u₁_eq x' v hv hv' t s hs H]
    exact B24ISO.map_mk _ _ _ _

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic (solution)
