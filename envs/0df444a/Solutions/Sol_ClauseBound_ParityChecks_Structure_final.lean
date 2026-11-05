-- Prove2me | solution 1 for ClauseBound.ParityChecks.Structure.final
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:21:57.231197+00:00
-- url     : https://prove2.me/submissions/035f03d4-d090-497f-a61e-9c7a15f4d73f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_ClauseBound_ParityChecks_Structure
import Theorems.Thm_ClauseBound_ParityChecks_Structure_ev_nonneg
import Theorems.Thm_ClauseBound_ParityChecks_Structure_Upar_final

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Structure
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace ClauseBound.ParityChecks.Structure
theorem _root_.solution (V : X → Finset E) (nb r : ℕ) (Λ : ℕ → Finset E)
    (hnn : 0 ≤ Upar V nb r (r - 1) Λ ∅ ∧ 0 ≤ Uinc nb r (r - 1) Λ (∅ : Finset E) ∧ 0 ≤ Urow nb r (r - 1) Λ (∅ : Finset E) ∧
      0 ≤ Ucol nb r (r - 1) Λ (∅ : Finset E))
    (hs : IsState r (r - 1) Λ (∅ : Finset E)) (hU : Ups V nb r (r - 1) Λ ∅ < 1) : Good V nb r Λ := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by have := hs.j_lt; omega⟩
  rw [Nat.add_sub_cancel] at hnn hU
  obtain ⟨-, n2, n3, n4⟩ := hnn
  have u1 : Upar V nb (r + 1) r Λ ∅ < 1 := by
    unfold Ups at hU
    linarith
  rw [Upar_final] at u1
  have hterm : ∀ ξ ∈ (univ : Finset X), 0 ≤ (omega V nb ξ : ℤ) * ∏ j' ∈ range (r + 1), ev #(Λ j' ∩ V ξ) := fun ξ _ =>
    mul_nonneg (Int.natCast_nonneg _) (prod_nonneg fun _ _ => ev_nonneg _)
  have h0 : ∑ ξ, (omega V nb ξ : ℤ) * ∏ j' ∈ range (r + 1), ev #(Λ j' ∩ V ξ) = 0 := by
    have h1 : ∑ ξ, (omega V nb ξ : ℤ) * ∏ j' ∈ range (r + 1), ev #(Λ j' ∩ V ξ) < 1 := by exact_mod_cast u1
    have h2 := sum_nonneg hterm
    omega
  intro ξ hξ
  by_contra hno
  have h1 := (sum_eq_zero_iff_of_nonneg hterm).1 h0 ξ (mem_univ ξ)
  have h2 : ∏ j' ∈ range (r + 1), ev #(Λ j' ∩ V ξ) = 1 := prod_eq_one fun j' hj' => by
    have : Even #(Λ j' ∩ V ξ) := Nat.not_odd_iff_even.1 fun ho => hno ⟨j', mem_range.1 hj', ho⟩
    rw [ev, if_pos this]
  have h3 : 0 < omega V nb ξ := Nat.choose_pos hξ
  rw [h2, mul_one] at h1
  omega
end ClauseBound.ParityChecks.Structure
