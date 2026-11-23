-- Prove2me | solution 1 for EquivarianceConvolution.equivariant_image_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T21:12:32.015934+00:00
-- url     : https://prove2.me/submissions/c0c63f59-90f9-43cb-9f4c-50c51c9b3983

import Mathlib
import Definitions.Def_EquivarianceConvolution_Basic

open scoped BigOperators
namespace EquivarianceConvolution


theorem equivariant_image_irreducible {G U V : Type*} [Group G] [Fintype G]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ G U) (T' : Representation ℂ G V) (φ : U →ₗ[ℂ] V)
    (hφ : IsEquivariantLinear T T' φ) (W : Submodule ℂ U) (hW : IsIrreducibleSubspace T W)
    (hne : W.map φ ≠ ⊥) :
    IsIrreducibleSubspace T' (W.map φ) ∧ AreEquivalentSubreps T W T' (W.map φ) := by
  obtain ⟨hWne, hWinv, hWirr⟩ := hW
  have hinv' : IsInvariantSubspace T' (W.map φ) := by
    intro g v hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨T g w, hWinv g w hw, hφ g w⟩
  have hKinv : IsInvariantSubspace T (W ⊓ LinearMap.ker φ) := by
    rintro g w ⟨hw, hk⟩
    refine ⟨hWinv g w hw, ?_⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hk ⊢
    rw [hφ, hk, map_zero]
  have hinj : ∀ w ∈ W, φ w = 0 → w = 0 := by
    rcases hWirr _ inf_le_left hKinv with hK | hK
    · intro w hw h0
      have : w ∈ W ⊓ LinearMap.ker φ := ⟨hw, h0⟩
      rw [hK] at this
      exact (Submodule.mem_bot _).mp this
    · exfalso; apply hne
      rw [eq_bot_iff]
      rintro v ⟨w, hw, rfl⟩
      exact (Submodule.mem_bot _).mpr (LinearMap.mem_ker.mp ((inf_eq_left.mp hK) hw))
  refine ⟨⟨hne, hinv', ?_⟩, ?_⟩
  · intro W' hle hW'
    have hinv2 : IsInvariantSubspace T (W ⊓ W'.comap φ) := by
      rintro g w ⟨hw, hc⟩
      refine ⟨hWinv g w hw, ?_⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap] at hc ⊢
      rw [hφ]; exact hW' g _ hc
    rcases hWirr _ inf_le_left hinv2 with h | h
    · left
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨w, hw, rfl⟩ := hle hv
      have : w ∈ W ⊓ W'.comap φ := ⟨hw, hv⟩
      rw [h] at this
      rw [(Submodule.mem_bot _).mp this, map_zero]; exact Submodule.zero_mem _
    · right
      refine le_antisymm hle ?_
      rintro v ⟨w, hw, rfl⟩
      have : w ∈ W ⊓ W'.comap φ := by rw [h]; exact hw
      exact this.2
  · have hψ : Function.Injective (φ.domRestrict W) := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro w hw
      rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hw
      have := hinj w w.2 hw
      exact (Submodule.mem_bot _).mpr (Subtype.ext this)
    let e := (LinearEquiv.ofInjective _ hψ).trans
      (LinearEquiv.ofEq _ _ (LinearMap.range_domRestrict W φ))
    refine ⟨e, fun g w w' hw' => ?_⟩
    change φ w' = T' g (φ w)
    rw [hw', hφ]


end EquivarianceConvolution

open EquivarianceConvolution in
theorem solution {G U V : Type*} [Group G] [Fintype G]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ G U) (T' : Representation ℂ G V) (φ : U →ₗ[ℂ] V)
    (hφ : IsEquivariantLinear T T' φ) (W : Submodule ℂ U) (hW : IsIrreducibleSubspace T W)
    (hne : W.map φ ≠ ⊥) :
    IsIrreducibleSubspace T' (W.map φ) ∧ AreEquivalentSubreps T W T' (W.map φ) := by
  obtain ⟨hWne, hWinv, hWirr⟩ := hW
  have hinv' : IsInvariantSubspace T' (W.map φ) := by
    intro g v hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨T g w, hWinv g w hw, hφ g w⟩
  have hKinv : IsInvariantSubspace T (W ⊓ LinearMap.ker φ) := by
    rintro g w ⟨hw, hk⟩
    refine ⟨hWinv g w hw, ?_⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hk ⊢
    rw [hφ, hk, map_zero]
  have hinj : ∀ w ∈ W, φ w = 0 → w = 0 := by
    rcases hWirr _ inf_le_left hKinv with hK | hK
    · intro w hw h0
      have : w ∈ W ⊓ LinearMap.ker φ := ⟨hw, h0⟩
      rw [hK] at this
      exact (Submodule.mem_bot _).mp this
    · exfalso; apply hne
      rw [eq_bot_iff]
      rintro v ⟨w, hw, rfl⟩
      exact (Submodule.mem_bot _).mpr (LinearMap.mem_ker.mp ((inf_eq_left.mp hK) hw))
  refine ⟨⟨hne, hinv', ?_⟩, ?_⟩
  · intro W' hle hW'
    have hinv2 : IsInvariantSubspace T (W ⊓ W'.comap φ) := by
      rintro g w ⟨hw, hc⟩
      refine ⟨hWinv g w hw, ?_⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap] at hc ⊢
      rw [hφ]; exact hW' g _ hc
    rcases hWirr _ inf_le_left hinv2 with h | h
    · left
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨w, hw, rfl⟩ := hle hv
      have : w ∈ W ⊓ W'.comap φ := ⟨hw, hv⟩
      rw [h] at this
      rw [(Submodule.mem_bot _).mp this, map_zero]; exact Submodule.zero_mem _
    · right
      refine le_antisymm hle ?_
      rintro v ⟨w, hw, rfl⟩
      have : w ∈ W ⊓ W'.comap φ := by rw [h]; exact hw
      exact this.2
  · have hψ : Function.Injective (φ.domRestrict W) := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro w hw
      rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hw
      have := hinj w w.2 hw
      exact (Submodule.mem_bot _).mpr (Subtype.ext this)
    let e := (LinearEquiv.ofInjective _ hψ).trans
      (LinearEquiv.ofEq _ _ (LinearMap.range_domRestrict W φ))
    refine ⟨e, fun g w w' hw' => ?_⟩
    change φ w' = T' g (φ w)
    rw [hw', hφ]

