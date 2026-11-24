-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.relIndex_nSub_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:52.372532+00:00
-- url     : https://prove2.me/submissions/1e15d565-2c0c-4d0c-8e89-174245ce1338

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqOfMap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_relIndex_eq_of_map
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_endL_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_equiv_of_mem_endL
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_nSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_nSub_le_glSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_smul_anti
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {A₀ B₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ c₀ : ℕ, ∀ c ≥ c₀, ∃ k₀ : ℕ, ∀ k ≥ k₀, nSub (locF 𝔭 B₀) 𝔭 (k + c) ≤ nSub (locF 𝔭 A₀) 𝔭 k ∧
      endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) ≤ endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀) ∧
      (nSub (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (nSub (locF 𝔭 A₀) 𝔭 k) =
        (endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀)).relIndex
          (endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀)) := by
  obtain ⟨r, hr⟩ := exists_endL_le hB₀ hA₀ h𝔭
  obtain ⟨k₁, hk₁⟩ := nSub_le_glSub hA₀ hB₀ h𝔭
  refine ⟨r, fun c hc => ⟨max k₁ 1, fun k hk => ?_⟩⟩
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk

  have hle : endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) ≤
      endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀) := by
    intro D hD
    refine hr k ?_
    intro x hx
    exact smul_anti 𝔭 _ (by omega) (hD x hx)

  have hlift : ∀ D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀),
      ∃ X ∈ nSub (locF 𝔭 A₀) 𝔭 k, (X : V →ₗ[K] V) - LinearMap.id = D := by
    intro D hD
    have hD1 : D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀) := by
      intro x hx
      have := smul_anti 𝔭 (locF 𝔭 A₀) hk1 (hD x hx)
      rwa [pow_one] at this
    obtain ⟨X, hX, hXg⟩ := exists_equiv_of_mem_endL hA₀ h𝔭 hD1
    refine ⟨X, mem_nSub.2 ⟨hXg, fun x hx => ?_⟩, ?_⟩
    · rw [hX, add_sub_cancel_left]
      exact hD x hx
    · ext v
      simp [hX]
  have hnsub : nSub (locF 𝔭 B₀) 𝔭 (k + c) ≤ nSub (locF 𝔭 A₀) 𝔭 k := by
    intro X hXm
    obtain ⟨hXB, hX⟩ := mem_nSub.1 hXm
    have hD : (X : V →ₗ[K] V) - LinearMap.id ∈ endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) := by
      intro x hx
      simpa using hX x hx
    obtain ⟨X', hX'm, hX'⟩ := hlift _ (hle hD)
    have hXX : X' = X := by
      ext v
      have := LinearMap.congr_fun hX' v
      simpa using this
    rw [← hXX]
    exact hX'm
  refine ⟨hnsub, hle, ?_⟩
  refine relIndex_eq_of_map _ _ _ _ (fun X => (X : V →ₗ[K] V) - LinearMap.id) (fun X hX => ?_)
    (fun D hD => ?_) (fun x hx y hy => ?_)
  · intro v hv
    simpa using (mem_nSub.1 hX).2 v hv
  · obtain ⟨X, hXm, hX⟩ := hlift D hD
    exact ⟨X, hXm, hX⟩
  · have hxB : x ∈ glSub (locF 𝔭 B₀) := hk₁ k (le_trans (le_max_left _ _) hk) hx
    have hyB : y ∈ glSub (locF 𝔭 B₀) := hk₁ k (le_trans (le_max_left _ _) hk) hy
    have hxyB : x⁻¹ * y ∈ glSub (locF 𝔭 B₀) := mul_mem (inv_mem hxB) hyB
    have e1 : ∀ v : V, x (x⁻¹ v) = v := fun v => by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    rw [mem_nSub]
    constructor
    · rintro ⟨_, h⟩ v hv
      have h' := apply_mem_smul hxB _ (h v hv)
      have e2 : x ((x⁻¹ * y) v - v) = y v - x v := by
        rw [map_sub, LinearEquiv.mul_apply, e1]
      rw [e2] at h'
      simpa using h'
    · intro h
      refine ⟨hxyB, fun v hv => ?_⟩
      have h' := apply_mem_smul (inv_mem hxB) _ (h v hv)
      have e2 : x⁻¹ ((((y : V →ₗ[K] V) - LinearMap.id) - ((x : V →ₗ[K] V) - LinearMap.id) :
          V →ₗ[K] V) v) =
          (x⁻¹ * y) v - v := by
        simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, sub_sub_sub_cancel_right,
          map_sub, LinearEquiv.mul_apply]
        rw [← LinearEquiv.mul_apply x⁻¹ x, inv_mul_cancel]
        rfl
      rw [e2] at h'
      exact h'
end Formalism.HermitianLattices.Ext.L3.D2
