-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.previousAnchor_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:36:43.382574+00:00
-- url     : https://prove2.me/submissions/d62cf4cc-50ed-4fb7-8a07-5f15ed72a89c

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_relativeCuts
public import Theorems.Thm_DeciSigma1_Holes_Fresh_le_previousAnchor
public import Theorems.Thm_DeciSigma1_Holes_Fresh_previousAnchor_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_previousAnchor_spec


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {A : Finset ℕ} {s e q : ℕ}
    (hs : s = 0 ∨ s ∈ A) (hsq : s < q) (hqe : q ≤ e) :
    previousAnchor A q = s + previousAnchor (relativeCuts A s e) (q - s) := by
  apply le_antisymm
  · apply previousAnchor_le
    intro a ha haq
    by_cases has : a ≤ s
    · omega
    · have hr : a - s ∈ relativeCuts A s e := mem_relativeCuts.mpr
        ⟨by omega, by omega, by convert ha using 1; omega⟩
      have := le_previousAnchor hr (show a - s < q - s by omega)
      omega
  · have hbase : s ≤ previousAnchor A q := by
      rcases hs with rfl | hs
      · omega
      · exact le_previousAnchor hs hsq
    by_cases hex : ∃ p ∈ relativeCuts A s e, p < q - s
    · obtain ⟨hp, hpq⟩ := previousAnchor_spec hex
      obtain ⟨hp0, hpe, hpa⟩ := mem_relativeCuts.mp hp
      exact le_previousAnchor hpa (by omega)
    · have : previousAnchor (relativeCuts A s e) (q - s) = 0 := by
        apply Nat.eq_zero_of_le_zero
        apply previousAnchor_le
        intro p hp hpq
        exact False.elim (hex ⟨p, hp, hpq⟩)
      omega
end DeciSigma1.Holes.Fresh
