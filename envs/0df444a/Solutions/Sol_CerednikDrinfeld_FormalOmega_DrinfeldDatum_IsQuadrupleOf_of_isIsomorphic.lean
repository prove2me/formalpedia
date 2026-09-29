-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.of_isIsomorphic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8585ad61-3224-59c0-9d16-10a5dd68e556

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_of_isIsomorphic

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega TensorProduct

noncomputable section

namespace P2mKcQuadrupleIsoInv

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem ker_eq_map_transport {C : Type} [CommRing C] [Algebra 𝒪 C] {M₁ M₂ : FullLattice 𝒪 K} (h : M₁.1 = M₂.1)
    {P₁ P₂ : Type} [AddCommGroup P₁] [Module C P₁] [AddCommGroup P₂] [Module C P₂]
    (u₁ : latticeBaseChange 𝒪 K C M₁ →ₗ[C] P₁) (u₂ : latticeBaseChange 𝒪 K C M₂ →ₗ[C] P₂) (φ : P₁ →ₗ[C] P₂)
    (hφ : Function.Injective φ) (hcomm : ∀ z, u₂ (transportEquiv C h z) = φ (u₁ z)) :
    LinearMap.ker u₂ = (LinearMap.ker u₁).map (transportEquiv C h).toLinearMap := by
  ext z
  constructor
  · intro hz
    refine ⟨(transportEquiv C h).symm z, ?_, LinearEquiv.apply_symm_apply _ _⟩
    rw [LinearMap.mem_ker] at hz
    show (transportEquiv C h).symm z ∈ LinearMap.ker u₁
    rw [LinearMap.mem_ker]
    apply hφ
    rw [← hcomm, LinearEquiv.apply_symm_apply, hz, map_zero]
  · rintro ⟨w, hw, rfl⟩
    have hw' : u₁ w = 0 := hw
    rw [LinearMap.mem_ker, LinearEquiv.coe_coe, hcomm, hw', map_zero]

theorem ext_one_tmul {C : Type} [CommRing C] [Algebra 𝒪 C] {M : FullLattice 𝒪 K} {P : Type} [AddCommGroup P] [Module C P]
    (u u' : latticeBaseChange 𝒪 K C M →ₗ[C] P) (h : ∀ v : ↥M.1, u ((1 : C) ⊗ₜ[𝒪] v) = u' ((1 : C) ⊗ₜ[𝒪] v)) : u = u' := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul c v =>
    have hc : (c ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K C M) = c • ((1 : C) ⊗ₜ[𝒪] v) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [hc, map_smul, map_smul, h]

variable {π}

theorem ker_transfer (x : PrimeSpectrum B) {N N' : Submodule 𝒪 (Fin 2 → K)} (hN : IsFullLattice N) (hN' : IsFullLattice N')
    (hNN' : N = N') {T T' : Type} [AddCommGroup T] [Module B T] [AddCommGroup T'] [Module B T'] (τ : T ≃ₗ[B] T')
    (u : latticeBaseChange 𝒪 K (locRing B x) ⟨N, hN⟩ →ₗ[locRing B x] stalk B x T)
    (u' : latticeBaseChange 𝒪 K (locRing B x) ⟨N', hN'⟩ →ₗ[locRing B x] stalk B x T')
    (hu : ∀ (v : Fin 2 → K) (hv : v ∈ N) (hv' : v ∈ N'),
      u' ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥N')) =
        LocalizedModule.map x.asIdeal.primeCompl τ.toLinearMap (u ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥N))))
    (dloc : DeligneDatum (K := K) π (locRing B x)) (hker : LinearMap.ker u = dloc.line ⟨N, hN⟩) :
    LinearMap.ker u' = dloc.line ⟨N', hN'⟩ := by
  have h1 : (⟨N, hN⟩ : FullLattice 𝒪 K).1 = (⟨N', hN'⟩ : FullLattice 𝒪 K).1 := hNN'
  rw [DeligneDatum.line_transport π dloc h1, ← hker]
  refine ker_eq_map_transport h1 u u'
    ((LocalizedModule.map x.asIdeal.primeCompl τ.toLinearMap).restrictScalars (locRing B x)) ?_ ?_
  · exact LocalizedModule.map_injective _ _ τ.injective
  · intro z

    have key : u' ∘ₗ (transportEquiv (locRing B x) h1).toLinearMap =
        ((LocalizedModule.map x.asIdeal.primeCompl τ.toLinearMap).restrictScalars (locRing B x)) ∘ₗ u := by
      apply ext_one_tmul
      intro v
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, transportEquiv_tmul,
        LinearMap.restrictScalars_apply]
      have hv' : (v : Fin 2 → K) ∈ N' := hNN' ▸ v.2
      have hofEq : (LinearEquiv.ofEq _ _ h1 v : ↥(⟨N', hN'⟩ : FullLattice 𝒪 K).1) = ⟨v, hv'⟩ := Subtype.ext rfl
      rw [hofEq, hu v v.2 hv']
    exact congrArg (fun F : latticeBaseChange 𝒪 K (locRing B x) ⟨N, hN⟩ →ₗ[locRing B x] stalk B x T' => F z) key

end P2mKcQuadrupleIsoInv

end

open P2mKcQuadrupleIsoInv in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    {Q Q' : DrinfeldDatum (K := K) π B} {d : DeligneDatum (K := K) π B}
    (h : Q.IsQuadrupleOf d) (e : Q.IsIsomorphic Q') : Q'.IsQuadrupleOf d := by
  obtain ⟨e⟩ := e
  intro x
  obtain ⟨hedge, hk₀, hk₁⟩ := h x
  have hL₀ : Q'.L₀ x = Q.L₀ x := Subtype.ext (e.N₀_eq x).symm
  have hL₁ : Q'.L₁ x = Q.L₁ x := Subtype.ext (e.N₁_eq x).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hL₀, hL₁]; exact hedge
  · exact ker_transfer x (Q.full₀ x) (Q'.full₀ x) (e.N₀_eq x) e.τ₀ (Q.u₀ x) (Q'.u₀ x)
      (fun v hv hv' => e.τ₀_u₀ x v hv hv') _ hk₀
  · exact ker_transfer x (Q.full₁ x) (Q'.full₁ x) (e.N₁_eq x) e.τ₁ (Q.u₁ x) (Q'.u₁ x)
      (fun v hv hv' => e.τ₁_u₁ x v hv hv') _ hk₁

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_of_isIsomorphic
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_of_isIsomorphic (solution)
