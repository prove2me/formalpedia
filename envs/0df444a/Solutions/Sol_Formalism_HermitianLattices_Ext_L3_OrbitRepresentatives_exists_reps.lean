-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives.exists_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:42:17.949186+00:00
-- url     : https://prove2.me/submissions/f9d3e378-5ecc-4438-a25c-691ff1e4dd5a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomMapOfEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AdjoinMemGenusIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardStabilizerAutSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_OrbitRepresentatives_exists_orbit_reps
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_OrbitRepresentatives_card_stabilizer_autSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_finite_autL_of_ortho
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_finite_repSet_of_ortho
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_sum_inv_card_stab


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {I : Submodule (𝓞 K) V} {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) :
    ∃ T : Finset V, (∀ t ∈ T, t ∈ L ∧ h t t = 1) ∧
      (∀ x, x ∈ L → h x x = 1 → ∃ t ∈ T, ∃ a ∈ Formalism.ThetaLiftIndependence.autL h L, a t = x) ∧
      (∀ t₁ ∈ T, ∀ t₂ ∈ T, (∃ a ∈ Formalism.ThetaLiftIndependence.autL h L, a t₁ = t₂) → t₁ = t₂) ∧
      (repCount h L 1 : ℝ) / ((Nat.card (Formalism.ThetaLiftIndependence.autL h L) : ℕ) : ℝ) =
        ∑ t ∈ T, ((Nat.card {g : V ≃ₗ[K] V // g ∈ Formalism.ThetaLiftIndependence.autL h L ∧ g t = t} : ℕ) : ℝ)⁻¹ := by
  classical
  unfold Formalism.HermitianLattices.Ext.L3.repCount
  have hfin := finite_repSet_of_ortho hK hs hI hL 1
  haveI : Finite (autSub h L) := by
    have := (finite_autL_of_ortho hK hs hI hL).to_subtype
    exact this
  haveI : Finite ({x : V | x ∈ L ∧ h x x = 1} : Set V) := hfin.to_subtype
  have hA : ∀ g : autSub h L, ∀ x ∈ ({x : V | x ∈ L ∧ h x x = 1} : Set V),
      g • x ∈ ({x : V | x ∈ L ∧ h x x = 1} : Set V) := by
    rintro ⟨g, hgI, hgL⟩ x ⟨hxL, hxx⟩
    have hgI' : ∀ x y, h (g x) (g y) = h x y := hgI
    refine ⟨?_, ?_⟩
    · show g x ∈ L
      rw [← hgL]
      unfold Formalism.HermitianLatticesTheory.gmap
      exact Submodule.mem_map_of_mem hxL
    · show h (g x) (g x) = 1
      rw [hgI' x x, hxx]
  obtain ⟨T, hTA, hT⟩ := exists_orbit_reps (G := autSub h L) _ hfin hA
  refine ⟨T, hTA, ?_, ?_, ?_⟩
  · intro x hxL hxx
    obtain ⟨t, ⟨htT, g, hg⟩, -⟩ := hT x ⟨hxL, hxx⟩
    exact ⟨t, htT, g.1, g.2, hg⟩
  · rintro t₁ h₁ t₂ h₂ ⟨a, ha, hat⟩
    obtain ⟨t, -, huniq⟩ := hT t₂ (hTA t₂ h₂)
    have e1 := huniq t₁ ⟨h₁, ⟨a, ha⟩, hat⟩
    have e2 := huniq t₂ ⟨h₂, 1, one_smul _ _⟩
    rw [e1, e2]
  · have key := sum_inv_card_stab (G := autSub h L) _ hA T hTA hT
    have e : ∀ t ∈ T, ((Nat.card (MulAction.stabilizer (autSub h L) t) : ℕ) : ℝ)⁻¹ =
        ((Nat.card {g : V ≃ₗ[K] V // g ∈ Formalism.ThetaLiftIndependence.autL h L ∧ g t = t} : ℕ) : ℝ)⁻¹ :=
      fun t _ => by rw [card_stabilizer_autSub]
    rw [← Finset.sum_congr rfl e]
    exact key
end Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives
