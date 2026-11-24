-- Prove2me | solution 1 for Erdos1219.sum_shift_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:43:25.710137+00:00
-- url     : https://prove2.me/submissions/53174a10-f2cc-4fcb-a64c-639f5ca8b65e

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas

set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
namespace Erdos1219
theorem _root_.solution (a : ℕ → Cardinal.{u}) :
    Cardinal.sum (fun k => a (k + 1)) ≤ Cardinal.sum a := by
  show #(Σ k : ℕ, (a (k + 1)).out) ≤ #(Σ k : ℕ, (a k).out)
  refine mk_le_of_injective
    (f := fun p : (Σ k : ℕ, (a (k + 1)).out) => (⟨p.1 + 1, p.2⟩ : Σ k : ℕ, (a k).out)) ?_
  rintro ⟨k, x⟩ ⟨k', x'⟩ h
  simp only [Sigma.mk.injEq, add_left_inj] at h
  obtain ⟨rfl, h2⟩ := h
  rw [heq_iff_eq] at h2
  subst h2
  rfl
end Erdos1219
