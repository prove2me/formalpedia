-- Prove2me | solution 1 for Formalism.Q3.hostEmb_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:11:22.964156+00:00
-- url     : https://prove2.me/submissions/94d1a9ff-35a9-4e19-b015-9541d11ee5a7

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostEmb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Finset
noncomputable section
open Formalism Formalism.Q3
open Classical
namespace Formalism.Q3
theorem _root_.solution (hC : HostConj) (hH : HostGalois) : HostEmb := by
  intro q hq E _ _ α hα φ₀
  obtain ⟨hGal, hfin, hbij, hmul⟩ := hH q hq E α hα
  have := hGal
  have hconj := (hC q hq E α hα).1
  set F : Gal(E/ℚ) → (E →+* ℂ) := fun σ => φ₀.comp σ.toAlgHom.toRingHom with hF
  have hinj : Function.Injective F := by
    intro σ τ h
    apply AlgEquiv.ext
    intro x
    have := congrArg (fun f : E →+* ℂ => f x) h
    exact φ₀.injective this
  have hcard : Fintype.card Gal(E/ℚ) = Fintype.card (E →+* ℂ) := by
    rw [NumberField.Embeddings.card, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
  have hFbij : Function.Bijective F :=
    (Fintype.bijective_iff_injective_and_card F).mpr ⟨hinj, hcard⟩
  have hcc : ∀ σ τ : Gal(E/ℚ), galSign α τ = cc →
      F (τ * σ) = ComplexEmbedding.conjugate (F σ) := by
    intro σ τ hτ
    have h1 := (hconj φ₀ τ).mpr hτ
    ext y
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact h1 (σ y)
  refine ⟨hFbij, hcc, ?_⟩
  intro Φ
  obtain ⟨τc, hτc⟩ := hbij.2 cc
  have hmem : ∀ σ, F σ ∈ (univ.filter (fun σ : Gal(E/ℚ) => galSign α σ ∈ Φ)).image F ↔
      galSign α σ ∈ Φ := by
    intro σ
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨s, hs, he⟩
      rwa [← hinj he]
    · intro h
      exact ⟨σ, h, rfl⟩
  constructor
  · intro hΦ ψ
    obtain ⟨σ, rfl⟩ := hFbij.2 ψ
    rw [← hcc σ τc hτc, hmem, hmem, hmul, hτc]
    exact hΦ _
  · intro hT g
    obtain ⟨σ, rfl⟩ := hbij.2 g
    have := hT (F σ)
    rw [← hcc σ τc hτc, hmem, hmem, hmul, hτc] at this
    exact this
end Formalism.Q3
