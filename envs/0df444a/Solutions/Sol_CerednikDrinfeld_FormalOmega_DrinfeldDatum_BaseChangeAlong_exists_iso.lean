-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.BaseChangeAlong.exists_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/a9ce7b30-ca7f-55e4-9f22-5b95dbeedd0d

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_BaseChangeAlong_exists_iso

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace B25H3

theorem exists_equiv {B : Type} [CommRing B] {B' : Type} [CommRing B'] (φ : B →+* B')
    (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module B' T'] [Module.Invertible B' T']
    (T'' : Type) [AddCommGroup T''] [Module B' T''] [Module.Invertible B' T'']
    (τ' : T →ₛₗ[φ] T') (τ'' : T →ₛₗ[φ] T'')
    (h' : Submodule.span B' (Set.range τ') = ⊤) (h'' : Submodule.span B' (Set.range τ'') = ⊤) :
    ∃ e : T' ≃ₗ[B'] T'', ∀ t, e (τ' t) = τ'' t := by
  letI : Algebra B B' := φ.toAlgebra
  letI : Module B T' := Module.compHom T' φ
  letI : Module B T'' := Module.compHom T'' φ
  haveI : IsScalarTower B B' T' := ⟨fun b c t => by
    show (b • c) • t = (φ b) • (c • t); rw [Algebra.smul_def, mul_smul]; rfl⟩
  haveI : IsScalarTower B B' T'' := ⟨fun b c t => by
    show (b • c) • t = (φ b) • (c • t); rw [Algebra.smul_def, mul_smul]; rfl⟩
  let σ' : T →ₗ[B] T' :=
    { toFun := τ'
      map_add' := fun a b => map_add τ' a b
      map_smul' := fun b t => by rw [LinearMap.map_smulₛₗ]; rfl }
  let σ'' : T →ₗ[B] T'' :=
    { toFun := τ''
      map_add' := fun a b => map_add τ'' a b
      map_smul' := fun b t => by rw [LinearMap.map_smulₛₗ]; rfl }
  have hs' : Function.Surjective (σ'.liftBaseChange B') := by
    rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange, ← top_le_iff, ← h']
    exact Submodule.span_mono (by rintro _ ⟨t, rfl⟩; exact ⟨t, rfl⟩)
  have hs'' : Function.Surjective (σ''.liftBaseChange B') := by
    rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange, ← top_le_iff, ← h'']
    exact Submodule.span_mono (by rintro _ ⟨t, rfl⟩; exact ⟨t, rfl⟩)
  let e' := LinearEquiv.ofBijective _ (Module.Invertible.bijective_of_surjective hs')
  let e'' := LinearEquiv.ofBijective _ (Module.Invertible.bijective_of_surjective hs'')
  refine ⟨e'.symm.trans e'', fun t => ?_⟩
  have h1 : e' ((1 : B') ⊗ₜ[B] t) = τ' t := by
    rw [LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul]; rfl
  have h2 : e'' ((1 : B') ⊗ₜ[B] t) = τ'' t := by
    rw [LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul]; rfl
  rw [LinearEquiv.trans_apply, ← h1, LinearEquiv.symm_apply_apply, h2]

theorem exists_mk {B : Type} [CommRing B] (S : Submonoid B) {M : Type} [AddCommGroup M] [Module B M]
    (m : LocalizedModule S M) : ∃ (t : M) (s : S), m = LocalizedModule.mk t s := by
  induction m using LocalizedModule.induction_on with
  | h t s => exact ⟨t, s, rfl⟩

end B25H3

open B25H3 in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (g : B →ₐ[𝒪] B')
    {Q : DrinfeldDatum (K := K) π B} {Q' Q'' : DrinfeldDatum (K := K) π B'}
    (W : Q.BaseChangeAlong g Q') (W' : Q.BaseChangeAlong g Q'') :
    ∃ e : Q'.Iso Q'', (∀ t, e.τ₀ (W.τ₀ t) = W'.τ₀ t) ∧ (∀ t, e.τ₁ (W.τ₁ t) = W'.τ₁ t) := by
  obtain ⟨e₀, he₀⟩ := exists_equiv (g : B →+* B') Q.T₀ Q'.T₀ Q''.T₀ W.τ₀ W'.τ₀ W.span_range_τ₀ W'.span_range_τ₀
  obtain ⟨e₁, he₁⟩ := exists_equiv (g : B →+* B') Q.T₁ Q'.T₁ Q''.T₁ W.τ₁ W'.τ₁ W.span_range_τ₁ W'.span_range_τ₁
  refine ⟨{ N₀_eq := fun x' => by rw [W.N₀_eq, W'.N₀_eq], N₁_eq := fun x' => by rw [W.N₁_eq, W'.N₁_eq],
            τ₀ := e₀, τ₁ := e₁, τ₁_Pi₀ := ?_, τ₀_Pi₁ := ?_, τ₀_u₀ := ?_, τ₁_u₁ := ?_ }, he₀, he₁⟩
  ·
    have key : e₁.toLinearMap ∘ₗ Q'.Pi₀ = Q''.Pi₀ ∘ₗ e₀.toLinearMap := by
      apply LinearMap.ext_on W.span_range_τ₀
      rintro _ ⟨t, rfl⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
      rw [← W.τ₁_Pi₀, he₁, W'.τ₁_Pi₀, he₀]
    intro t
    exact congrArg (fun f => f t) (congrArg DFunLike.coe key)
  · have key : e₀.toLinearMap ∘ₗ Q'.Pi₁ = Q''.Pi₁ ∘ₗ e₁.toLinearMap := by
      apply LinearMap.ext_on W.span_range_τ₁
      rintro _ ⟨t, rfl⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
      rw [← W.τ₀_Pi₁, he₀, W'.τ₀_Pi₁, he₁]
    intro t
    exact congrArg (fun f => f t) (congrArg DFunLike.coe key)
  · intro x' v hv hv'
    have hvQ : v ∈ Q.N₀ (DrinfeldDatum.pointUnder g x') := by rw [← W.N₀_eq]; exact hv
    obtain ⟨t, s, H⟩ := exists_mk _ (Q.u₀ (DrinfeldDatum.pointUnder g x')
      ((1 : locRing B (DrinfeldDatum.pointUnder g x')) ⊗ₜ[𝒪] (⟨v, hvQ⟩ : ↥(Q.N₀ (DrinfeldDatum.pointUnder g x')))))
    have h1 := W.u₀_eq x' v hvQ hv t s s.2 H
    have h2 := W'.u₀_eq x' v hvQ hv' t s s.2 H
    rw [h1, h2, LocalizedModule.map_mk]
    exact congrArg (fun m => LocalizedModule.mk m _) (he₀ t).symm
  · intro x' v hv hv'
    have hvQ : v ∈ Q.N₁ (DrinfeldDatum.pointUnder g x') := by rw [← W.N₁_eq]; exact hv
    obtain ⟨t, s, H⟩ := exists_mk _ (Q.u₁ (DrinfeldDatum.pointUnder g x')
      ((1 : locRing B (DrinfeldDatum.pointUnder g x')) ⊗ₜ[𝒪] (⟨v, hvQ⟩ : ↥(Q.N₁ (DrinfeldDatum.pointUnder g x')))))
    have h1 := W.u₁_eq x' v hvQ hv t s s.2 H
    have h2 := W'.u₁_eq x' v hvQ hv' t s s.2 H
    rw [h1, h2, LocalizedModule.map_mk]
    exact congrArg (fun m => LocalizedModule.mk m _) (he₁ t).symm

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_BaseChangeAlong_exists_iso
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_BaseChangeAlong_exists_iso (solution)
