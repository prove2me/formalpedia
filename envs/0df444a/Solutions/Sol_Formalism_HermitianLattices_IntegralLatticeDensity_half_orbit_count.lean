-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.half_orbit_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:39.638085+00:00
-- url     : https://prove2.me/submissions/5ecfe2ac-f472-4ebd-8693-c7247ca9d388

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_TaylorLogMetric
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.IntegralLatticeDensity
open Finset Formalism.LogVandermondeBounds.TaylorLogMetric
private theorem orbit_even_card_half_filter_zero {α : Type} (φ c : Equiv.Perm α) (κ : α → ZMod 2) (O : Finset α)
    {inst : DecidablePred (fun τ => κ τ = 0)} {deq : DecidableEq α}
    (hφ : ∀ τ, κ (φ τ) = κ τ + 1) (hc : ∀ τ, κ (c τ) = κ τ + 1) (hO : ∀ τ, φ τ ∈ O ↔ τ ∈ O) :
    Even O.card ∧ 2 * (O.filter (fun τ => κ τ = 0)).card = O.card ∧
      2 * ((O.image c).filter (fun τ => κ τ = 0)).card = O.card := by
  have h1 : (O.filter (fun τ => κ τ = 0)).card = (O.filter (fun τ => ¬ κ τ = 0)).card := by
    apply Finset.card_nbij' (fun τ => φ τ) (fun τ => φ.symm τ)
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_filter] at hτ ⊢
      refine ⟨(hO τ).2 hτ.1, ?_⟩
      rw [hφ, hτ.2]
      decide
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_filter] at hτ ⊢
      have e := hφ (φ.symm τ)
      rw [Equiv.apply_symm_apply] at e
      refine ⟨(hO _).1 (by rw [Equiv.apply_symm_apply]; exact hτ.1), ?_⟩
      have h2 := hτ.2
      generalize κ (φ.symm τ) = y at e ⊢
      generalize κ τ = x at e h2
      revert x y
      decide
    · intro τ _
      simp
    · intro τ _
      simp
  have h3 := Finset.card_filter_add_card_filter_not (s := O) (fun τ => κ τ = 0)
  have h4 : ((O.image c).filter (fun τ => κ τ = 0)).card
      = (O.filter (fun τ => ¬ κ τ = 0)).card := by
    symm
    apply Finset.card_nbij' (fun τ => c τ) (fun τ => c.symm τ)
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_image] at hτ ⊢
      refine ⟨⟨τ, hτ.1, rfl⟩, ?_⟩
      have h2 := hτ.2
      rw [hc]
      generalize κ τ = x at h2 ⊢
      revert x
      decide
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_image] at hτ ⊢
      obtain ⟨⟨a, ha, rfl⟩, h2⟩ := hτ
      rw [Equiv.symm_apply_apply]
      refine ⟨ha, ?_⟩
      rw [hc] at h2
      generalize κ a = x at h2 ⊢
      revert x
      decide
    · intro τ _
      simp
    · intro τ _
      simp
  exact ⟨⟨(O.filter (fun τ => κ τ = 0)).card, by omega⟩, by omega, by omega⟩
end Formalism.HermitianLattices.IntegralLatticeDensity
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.IntegralLatticeDensity
open Finset Formalism.LogVandermondeBounds.TaylorLogMetric
namespace Formalism.HermitianLattices.IntegralLatticeDensity
theorem _root_.solution : OrbitHalf := by
  unfold OrbitHalf
  intro Emb _ φ c κ τ₀ hφ hc
  exact orbit_even_card_half_filter_zero φ c κ _ hφ hc
    (fun τ => by simp [Finset.mem_filter, Equiv.Perm.sameCycle_apply_right])
end Formalism.HermitianLattices.IntegralLatticeDensity
