-- Prove2me | solution 1 for Formalism.G0.LengthLayersP.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:12.621243+00:00
-- url     : https://prove2.me/submissions/96c85aa7-84bc-4b1e-9855-1ffb058c36e7

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Theorems.Thm_Formalism_G0_LengthLayersP_length_quot_eq_add
import Theorems.Thm_Formalism_G0_LengthLayersP_mem_pw
import Theorems.Thm_Formalism_G0_LengthLayersP_length_le_of_span_eq_top
import Theorems.Thm_Formalism_G0_LengthLayersP_layer
import Theorems.Thm_Formalism_G0_LengthLayersP_pw_le_span
import Theorems.Thm_Formalism_G0_LengthLayersP_allBut_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.G0
namespace LengthLayersP
section General
variable {O : Type} [CommRing O]
end General
section DVR
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
end DVR
section Main
variable {O : Type} [CommRing O]
end Main
private theorem length_pw_quot_le_sum_of_allButLE {O M : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] (π : O) (hπ : Irreducible π) (P : Submodule O M)
    (τ S Stop β₀ : ℕ) (g : ℕ → ℕ)
    (hg : ∀ β ≤ β₀, AllButLE π ⊤ P (g β) (τ + β * S))
    (hstop : AllButLE π ⊤ P 0 (τ + Stop)) :
    ∀ d, d ≤ β₀ → Module.length O ↥(pw π (M ⧸ P) (τ + (β₀ - d) * S)) ≤
      ((S * ∑ β ∈ Finset.Ico (β₀ - d) β₀, g β + Stop * g β₀ : ℕ) : ℕ∞) := by
  have hz := allBut_zero π P _ hstop
  intro d
  induction d with
  | zero =>
    intro _
    rw [Nat.sub_zero, Finset.Ico_self, Finset.sum_empty, mul_zero, zero_add]
    obtain ⟨C, hCc, hCs⟩ := pw_le_span π P _ _ (hg β₀ le_rfl)
    have hl := layer π hπ ⊥ (pw π (M ⧸ P) (τ + β₀ * S)) bot_le C (g β₀) Stop hCc hCs ?_
    · have h0 : Module.length O ↥(⊥ : Submodule O (M ⧸ P)) = 0 := Module.length_eq_zero
      rw [h0, zero_add] at hl
      rw [mul_comm Stop (g β₀)]
      exact hl
    · intro v hv
      obtain ⟨y, rfl⟩ := mem_pw.mp hv
      obtain ⟨x, rfl⟩ := P.mkQ_surjective y
      have h0 : π ^ (τ + Stop) • P.mkQ x = 0 := by
        rw [← map_smul]
        exact (Submodule.Quotient.mk_eq_zero P).mpr (hz x)
      rw [Submodule.mem_bot, smul_smul, ← pow_add,
        show Stop + (τ + β₀ * S) = β₀ * S + (τ + Stop) by ring, pow_add, ← smul_smul, h0,
        smul_zero]
  | succ d ih =>
    intro hd
    have hk : β₀ - d = (β₀ - (d + 1)) + 1 := by omega
    have ih' := ih (by omega)
    rw [hk] at ih'
    set k := β₀ - (d + 1) with hkdef
    obtain ⟨C, hCc, hCs⟩ := pw_le_span π P _ _ (hg k (by omega))
    have hUV : pw π (M ⧸ P) (τ + (k + 1) * S) ≤ pw π (M ⧸ P) (τ + k * S) := by
      intro u hu
      obtain ⟨y, rfl⟩ := mem_pw.mp hu
      refine mem_pw.mpr ⟨π ^ S • y, ?_⟩
      rw [smul_smul, ← pow_add, show τ + k * S + S = τ + (k + 1) * S by ring]
    have hs : ∀ v ∈ pw π (M ⧸ P) (τ + k * S), π ^ S • v ∈ pw π (M ⧸ P) (τ + (k + 1) * S) := by
      intro v hv
      obtain ⟨y, rfl⟩ := mem_pw.mp hv
      refine mem_pw.mpr ⟨y, ?_⟩
      rw [smul_smul, ← pow_add, show S + (τ + k * S) = τ + (k + 1) * S by ring]
    have hl := layer π hπ _ _ hUV C (g k) S hCc hCs hs
    have hsum : ∑ β ∈ Finset.Ico k β₀, g β = g k + ∑ β ∈ Finset.Ico (k + 1) β₀, g β :=
      Finset.sum_eq_sum_Ico_succ_bot (by omega) g
    calc Module.length O ↥(pw π (M ⧸ P) (τ + k * S))
        ≤ Module.length O ↥(pw π (M ⧸ P) (τ + (k + 1) * S)) + ((g k * S : ℕ) : ℕ∞) := hl
      _ ≤ ((S * ∑ β ∈ Finset.Ico (k + 1) β₀, g β + Stop * g β₀ : ℕ) : ℕ∞) +
            ((g k * S : ℕ) : ℕ∞) := add_le_add ih' le_rfl
      _ = ((S * ∑ β ∈ Finset.Ico k β₀, g β + Stop * g β₀ : ℕ) : ℕ∞) := by
          rw [hsum]; push_cast; ring
end LengthLayersP
end Formalism.G0
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.LengthLayersP
namespace Formalism.G0.LengthLayersP
theorem _root_.solution : LengthLayers := by
  unfold LengthLayers
  intro O M _ _ _ _ _ _ _ π hπ P τ S Stop β₀ g hg hstop
  set N := P ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule O M) with hN
  have hNV : N ≤ pw π M τ := inf_le_right
  rw [length_quot_eq_add hNV]
  have hA : Module.length O ↥((pw π M τ).map N.mkQ) ≤ Module.length O ↥(pw π (M ⧸ P) τ) := by
    let f : M ⧸ N →ₗ[O] M ⧸ P := N.mapQ P LinearMap.id (fun x hx => hx.1)
    have hf : ∀ x ∈ (pw π M τ).map N.mkQ, f x ∈ pw π (M ⧸ P) τ := by
      intro x hx
      obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨y, rfl⟩ := mem_pw.mp hm
      exact mem_pw.mpr ⟨P.mkQ y, rfl⟩
    refine Module.length_le_of_injective (f.restrict hf) ((injective_iff_map_eq_zero _).mpr ?_)
    rintro ⟨x, hx⟩ h0
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hx
    have h1 : f (N.mkQ m) = 0 := congrArg Subtype.val h0
    have h2 : m ∈ P := (Submodule.Quotient.mk_eq_zero P).mp h1
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero N).mpr ⟨h2, hm⟩
  have hB : Module.length O (M ⧸ pw π M τ) ≤ ((Module.finrank O M * τ : ℕ) : ℕ∞) := by
    classical
    let b := Module.Free.chooseBasis O M
    let D : Finset (M ⧸ pw π M τ) := Finset.univ.image (fun i => (pw π M τ).mkQ (b i))
    have hDc : D.card ≤ Module.finrank O M := by
      rw [Module.finrank_eq_card_chooseBasisIndex]
      exact Finset.card_image_le
    have hD : ∀ x ∈ D, π ^ τ • x = 0 := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      rw [← map_smul]
      exact (Submodule.Quotient.mk_eq_zero _).mpr (mem_pw.mpr ⟨b i, rfl⟩)
    have htop : Submodule.span O (D : Set (M ⧸ pw π M τ)) = ⊤ := by
      have e : (D : Set (M ⧸ pw π M τ)) = (pw π M τ).mkQ '' Set.range b := by
        ext y
        simp [D]
      rw [e, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_mkQ]
    calc Module.length O (M ⧸ pw π M τ) ≤ ((D.card * τ : ℕ) : ℕ∞) :=
          length_le_of_span_eq_top π hπ τ D hD htop
      _ ≤ _ := by exact_mod_cast Nat.mul_le_mul_right τ hDc
  have hC := length_pw_quot_le_sum_of_allButLE π hπ P τ S Stop β₀ g hg hstop β₀ le_rfl
  rw [Nat.sub_self, zero_mul, add_zero, ← Finset.range_eq_Ico] at hC
  calc Module.length O ↥((pw π M τ).map N.mkQ) + Module.length O (M ⧸ pw π M τ)
      ≤ ((S * ∑ β ∈ Finset.range β₀, g β + Stop * g β₀ : ℕ) : ℕ∞) +
          ((Module.finrank O M * τ : ℕ) : ℕ∞) := add_le_add (hA.trans hC) hB
    _ = _ := by push_cast; ring
end Formalism.G0.LengthLayersP
