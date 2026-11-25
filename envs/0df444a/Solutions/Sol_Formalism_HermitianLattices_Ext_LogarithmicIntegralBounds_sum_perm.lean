-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.sum_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:59:37.608341+00:00
-- url     : https://prove2.me/submissions/512953ca-12d0-46a0-9494-029870be860e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqOrth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution {R : Type*} [AddCommMonoid R] (M c : ℕ) (hc : c.Coprime M) (S S' : Finset ℕ)
    (hS : ∀ b ∈ S, b < M) (hmap : ∀ b ∈ S, (c * b) % M ∈ S') (hcard : S'.card ≤ S.card) (f : ℕ → R) :
    ∑ b ∈ S', f b = ∑ b ∈ S, f ((c * b) % M) := by
  have hinj : ∀ x ∈ S, ∀ y ∈ S, (c * x) % M = (c * y) % M → x = y := by
    intro x hx y hy hxy
    have h1 : c * x ≡ c * y [MOD M] := hxy
    have h2 : x ≡ y [MOD M] := Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.symm hc) h1
    have h3 : x % M = y % M := h2
    rwa [Nat.mod_eq_of_lt (hS x hx), Nat.mod_eq_of_lt (hS y hy)] at h3
  have himg : S.image (fun b => (c * b) % M) = S' := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      exact hmap b hb
    · rw [Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)]
      exact hcard
  rw [← himg, Finset.sum_image (fun x hx y hy h => hinj x hx y hy h)]
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
