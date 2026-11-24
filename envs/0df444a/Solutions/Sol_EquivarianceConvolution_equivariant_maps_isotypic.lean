-- Prove2me | solution 1 for EquivarianceConvolution.equivariant_maps_isotypic
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:17:15.81181+00:00
-- url     : https://prove2.me/submissions/11d93c40-574a-4237-8fd2-668f62250d8b

import Mathlib
import Definitions.Def_EquivarianceConvolution_Basic

set_option autoImplicit false

open scoped BigOperators

open EquivarianceConvolution

/-- Schur-type step: an equivariant map sends a subspace of type `ρ` (with `ρ` irreducible)
either to `0` or to a subspace of type `ρ`. -/
private lemma map_ofType {G U V : Type*} [Group G]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ G U) (T' : Representation ℂ G V) (φ : U →ₗ[ℂ] V)
    (hφ : IsEquivariantLinear T T' φ) {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : IsIrrep ρ) (W : Submodule ℂ U) (hW : IsOfType T W ρ) :
    W.map φ = ⊥ ∨ IsOfType T' (W.map φ) ρ := by
  obtain ⟨hinv, e, he⟩ := hW
  set f : W →ₗ[ℂ] V := φ ∘ₗ W.subtype with hf
  -- the kernel of `φ|_W`, transported to `ℂ^n`, is `ρ`-invariant
  set W0 : Submodule ℂ (Fin n → ℂ) := (LinearMap.ker f).map (e : W →ₗ[ℂ] (Fin n → ℂ)) with hW0
  have hW0inv : ∀ g ∈ (Set.univ : Set G), ∀ v ∈ W0, Matrix.mulVec (ρ g) v ∈ W0 := by
    intro g _ v hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    let w' : W := ⟨T g w, hinv g w w.2⟩
    have hw' : e w' = Matrix.mulVec (ρ g) (e w) := he g w w' rfl
    refine Submodule.mem_map.mpr ⟨w', ?_, hw'⟩
    rw [LinearMap.mem_ker] at hw ⊢
    simp only [hf, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at hw ⊢
    show φ (T g w) = 0
    rw [hφ, hw, map_zero]
  rcases hρ.2 W0 hW0inv with h0 | htop
  · -- `φ|_W` is injective: its image is of type `ρ`
    right
    have hinj : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot]
      rw [eq_bot_iff] at h0 ⊢
      intro w hw
      have : e w ∈ W0 := Submodule.mem_map.mpr ⟨w, hw, rfl⟩
      have h := h0 this
      rw [Submodule.mem_bot] at h ⊢
      exact e.map_eq_zero_iff.mp h
    have hrange : LinearMap.range f = W.map φ := by
      rw [hf, LinearMap.range_comp, Submodule.range_subtype]
    let e1 : W ≃ₗ[ℂ] LinearMap.range f := LinearEquiv.ofInjective f hinj
    let e2 : LinearMap.range f ≃ₗ[ℂ] W.map φ := LinearEquiv.ofEq _ _ hrange
    refine ⟨?_, (e1.trans e2).symm.trans e, ?_⟩
    · intro g z hz
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hz
      rw [← hφ]
      exact Submodule.mem_map_of_mem (hinv g u hu)
    · intro g z z' hzz'
      set w : W := (e1.trans e2).symm z with hwdef
      have hzw : (z : V) = φ w := by
        have : (e1.trans e2) w = z := by rw [hwdef]; exact LinearEquiv.apply_symm_apply _ _
        rw [← this]; rfl
      let w' : W := ⟨T g w, hinv g w w.2⟩
      have hz'w' : (e1.trans e2) w' = z' := by
        apply Subtype.ext
        show φ (T g w) = (z' : V)
        rw [hzz', hφ, hzw]
      have hsymm : (e1.trans e2).symm z' = w' := by
        rw [← hz'w']; exact LinearEquiv.symm_apply_apply _ _
      simp only [LinearEquiv.trans_apply]
      rw [hsymm, ← hwdef]
      exact he g w w' rfl
  · -- `φ|_W = 0`
    left
    rw [eq_bot_iff]
    rintro _ ⟨u, hu, rfl⟩
    rw [Submodule.mem_bot]
    have hmem : e ⟨u, hu⟩ ∈ W0 := by rw [htop]; exact Submodule.mem_top
    obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.mp hmem
    have : w = ⟨u, hu⟩ := e.injective hwe
    rw [LinearMap.mem_ker, this] at hw
    exact hw

theorem solution {G U V : Type*} [Group G] [Fintype G]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ G U) (T' : Representation ℂ G V) (φ : U →ₗ[ℂ] V)
    (hφ : IsEquivariantLinear T T' φ) {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : IsIrrep ρ) :
    (isotypicPart T ρ).map φ ≤ isotypicPart T' ρ := by
  unfold isotypicPart
  rw [Submodule.map_iSup]
  refine iSup_le fun W => ?_
  rw [Submodule.map_iSup]
  refine iSup_le fun hW => ?_
  rcases map_ofType T T' φ hφ ρ hρ W hW with h | h
  · rw [h]; exact bot_le
  · exact le_iSup₂_of_le (W.map φ) h le_rfl
