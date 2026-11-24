-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.sum_reps_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:14:07.842427+00:00
-- url     : https://prove2.me/submissions/e4db6f69-1433-4740-ac6e-388b6b292217

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Mv
variable {k : Type*} [Field k] {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]
namespace Formalism.L2.PairingIndexBounds.Mv
theorem _root_.solution {G : Type*} [AddCommGroup G] (M N : AddSubgroup G) (S : Finset G) (hS : IsRepsG M N S)
    (f : G → k) (hadd : ∀ x y, f (x + y) = f x * f y) (hM : ∀ x ∈ M, f x = 1) (g₀ : G) (hg₀ : g₀ ∈ N)
    (hne : f g₀ ≠ 1) : ∑ x ∈ S, f x = 0 := by
  obtain ⟨hSN, hSinj, hSsurj⟩ := hS
  choose! σ hσ using hSsurj
  have hfσ : ∀ y ∈ N, f (σ y) = f y := by
    intro y hy
    have h1 : y = (y - σ y) + σ y := by abel
    conv_rhs => rw [h1, hadd, hM _ (hσ y hy).2, one_mul]
  have key : ∑ x ∈ S, f g₀ * f x = ∑ x ∈ S, f x := by
    refine Finset.sum_nbij (fun x => σ (g₀ + x)) ?_ ?_ ?_ ?_
    · intro x hx
      exact (hσ _ (N.add_mem hg₀ (hSN x hx))).1
    · intro x hx y hy hxy
      have hx' := (hσ _ (N.add_mem hg₀ (hSN x hx))).2
      have hy' := (hσ _ (N.add_mem hg₀ (hSN y hy))).2
      simp only at hxy
      rw [hxy] at hx'
      apply hSinj x hx y hy
      have := M.sub_mem hx' hy'
      have e : g₀ + x - σ (g₀ + y) - (g₀ + y - σ (g₀ + y)) = x - y := by abel
      rwa [e] at this
    · intro y hy
      have hyN : y - g₀ ∈ N := N.sub_mem (hSN y hy) hg₀
      have h1 := hσ _ hyN
      refine ⟨σ (y - g₀), h1.1, ?_⟩
      have h2 := hσ _ (N.add_mem hg₀ (hSN _ h1.1))
      simp only
      symm
      apply hSinj y hy _ h2.1
      have := M.add_mem h1.2 h2.2
      have e : y - g₀ - σ (y - g₀) + (g₀ + σ (y - g₀) - σ (g₀ + σ (y - g₀))) = y - σ (g₀ + σ (y - g₀)) := by abel
      rwa [e] at this
    · intro x hx
      rw [hfσ _ (N.add_mem hg₀ (hSN x hx)), hadd]
  rw [← Finset.mul_sum] at key
  have h2 : (f g₀ - 1) * ∑ x ∈ S, f x = 0 := by rw [sub_mul, key, one_mul, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h
end Formalism.L2.PairingIndexBounds.Mv
