-- Prove2me | solution 1 for GarrettFA.continuous_id_of_isInitTopology
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:10:41.701367+00:00
-- url     : https://prove2.me/submissions/3ba2eb39-adb1-4222-80f6-45455727e323

import Mathlib
import Definitions.Def_GarrettFA_IsInitTopology

open Topology

namespace GAId
open GarrettFA

lemma key1 {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [t : TopologicalSpace V] [h1 : IsTopologicalAddGroup V]
    [h2 : ContinuousSMul 𝕜 V] [h3 : LocallyConvexSpace ℝ V] (N : Set V) (hN : N ∈ 𝓝 (0 : V)) :
    ∃ U : Set V, U ∈ 𝓝 (0 : V) ∧ Balanced 𝕜 U ∧ Convex ℝ U ∧ U ⊆ N := by
  obtain ⟨s, ⟨hs0, hsc⟩, hsN⟩ := (LocallyConvexSpace.convex_basis_zero ℝ V).mem_iff.mp hN
  refine ⟨{x | ∀ a : 𝕜, ‖a‖ ≤ 1 → a • x ∈ s}, ?_, ?_, ?_, ?_⟩
  · apply Filter.mem_of_superset (balancedCore_mem_nhds_zero (𝕜 := 𝕜) hs0)
    intro x hx a ha
    exact balancedCore_subset s ((balancedCore_balanced s).smul_mem ha hx)
  · intro b hb
    rintro _ ⟨x, hx, rfl⟩ a ha
    rw [smul_smul]
    exact hx _ (by rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb)
  · have : {x : V | ∀ a : 𝕜, ‖a‖ ≤ 1 → a • x ∈ s} =
        ⋂ (a : 𝕜) (_ : ‖a‖ ≤ 1), ((a • LinearMap.id : V →ₗ[𝕜] V).restrictScalars ℝ) ⁻¹' s := by
      ext x; simp
    rw [this]
    exact convex_iInter fun a => convex_iInter fun _ => hsc.linear_preimage _
  · intro x hx; have := hx 1 (by simp); rw [one_smul] at this; exact hsN this

lemma key2 {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    [t : TopologicalSpace V] [hT2 : T2Space V] [g1 : IsTopologicalAddGroup V] [g2 : ContinuousSMul 𝕜 V]
    (W : Submodule 𝕜 V) [FiniteDimensional 𝕜 W]
    {F : Type*} [AddCommGroup F] [Module 𝕜 F] [tF : TopologicalSpace F]
    [hF1 : IsTopologicalAddGroup F] [hF2 : ContinuousSMul 𝕜 F] (g : V →ₗ[𝕜] F)
    (U : Set F) (hU : U ∈ 𝓝 (0 : F)) : {y : W | g (y : V) ∈ U} ∈ 𝓝 (0 : W) := by
  have hc : Continuous (g.comp W.subtype) := LinearMap.continuous_of_finiteDimensional _
  have hU' : U ∈ 𝓝 ((g.comp W.subtype) 0) := by rw [map_zero]; exact hU
  exact hc.continuousAt hU'

theorem main {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] (τ : TopologicalSpace V) (h₁ : @IsTopologicalAddGroup V τ _)
    (h₂ : @ContinuousSMul 𝕜 V _ _ τ) (h₃ : @LocallyConvexSpace ℝ V _ _ _ _ τ)
    [tV : TopologicalSpace V] [gV : IsTopologicalAddGroup V] [sV : ContinuousSMul 𝕜 V]
    [hT : T2Space V] (hV : IsInitTopology 𝕜 V) :
    @Continuous V V tV τ id := by
  rw [continuous_id_iff_le]
  have h0 : @nhds V tV 0 ≤ @nhds V τ 0 := by
    intro N hN
    obtain ⟨U, hU, hb, hc, hUN⟩ := key1 (t := τ) (h1 := h₁) (h2 := h₂) (h3 := h₃) N hN
    apply Filter.mem_of_superset _ hUN
    apply hV.mem_nhds_of_balanced_convex U hb hc
    intro W hW
    haveI := hW
    exact key2 (t := tV) (hT2 := hT) (g1 := gV) (g2 := sV) W (tF := τ) (hF1 := h₁)
      (hF2 := h₂) (LinearMap.id : V →ₗ[𝕜] V) U hU
  rw [le_iff_nhds]
  intro x
  have e1 := @nhds_translation_add_neg V tV _ gV x
  have e2 := @nhds_translation_add_neg V τ _ h₁ x
  rw [← e1, ← e2]
  exact Filter.comap_mono h0

end GAId

open GarrettFA in
theorem solution {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] (τ : TopologicalSpace V) (h₁ : @IsTopologicalAddGroup V τ _)
    (h₂ : @ContinuousSMul 𝕜 V _ _ τ) (h₃ : @LocallyConvexSpace ℝ V _ _ _ _ τ)
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V] [T2Space V]
    (hV : IsInitTopology 𝕜 V) :
    @Continuous V V _ τ id :=
  GAId.main τ h₁ h₂ h₃ hV
