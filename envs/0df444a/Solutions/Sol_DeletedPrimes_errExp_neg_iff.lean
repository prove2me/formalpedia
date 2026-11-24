-- Prove2me | solution 1 for DeletedPrimes.errExp_neg_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:15:27.867906+00:00
-- url     : https://prove2.me/submissions/f0566b0e-f068-4acb-bf04-ee9b6bb53425

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
import Theorems.Thm_DeletedPrimes_argmaxExp_mem
import Theorems.Thm_DeletedPrimes_errExp_le_maxExp
import Theorems.Thm_DeletedPrimes_errExp_argmax
import Theorems.Thm_DeletedPrimes_maxExp_neg_iff

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {α κ : ℝ} (h0 : 0 < α) (h1 : α < 1) (hκ : 0 ≤ κ) :
    (∀ τ ∈ Set.Icc 0 κ, errExp k α κ τ < 0) ↔ κ < kappaK k α := by
  constructor
  · intro h
    have := h _ (argmaxExp_mem hk h0 h1 hκ)
    rw [errExp_argmax hk h0 h1 hκ] at this
    exact (maxExp_neg_iff hk h0 h1).1 this
  · intro h τ hτ
    exact lt_of_le_of_lt (errExp_le_maxExp hk h0 h1 hκ hτ.1 hτ.2) ((maxExp_neg_iff hk h0 h1).2 h)
end DeletedPrimes
