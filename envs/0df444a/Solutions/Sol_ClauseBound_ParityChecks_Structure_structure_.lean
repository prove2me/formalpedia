-- Prove2me | solution 1 for ClauseBound.ParityChecks.Structure.structure_
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:19:08.090976+00:00
-- url     : https://prove2.me/submissions/db9c7e41-e0d8-4f2c-9eab-77a89ddd706b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_ClauseBound_ParityChecks_Structure
import Theorems.Thm_ClauseBound_ParityChecks_Structure_pr_pos
import Theorems.Thm_ClauseBound_ParityChecks_Structure_lt_of_sum_lt

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Structure
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace ClauseBound.ParityChecks.Structure
theorem _root_.solution (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) (D : Finset E)
    (hnn : 0 ≤ Upar V nb r j Λ D ∧ 0 ≤ Uinc nb r j Λ D ∧ 0 ≤ Urow nb r j Λ D ∧ 0 ≤ Ucol nb r j Λ D)
    (hnb : 2 ≤ nb) (hE : 1 ≤ Fintype.card E) (hs : IsState r j Λ D) (hU : Ups V nb r j Λ D < 1) :
    ((∑ j' ∈ range r, #(Λ j') : ℕ) : ℚ) < 8 * pr nb * Fintype.card E * r ∧
    (∀ j' < r, (2 : ℚ) ^ #(Λ j') < 8 * r * (1 + pr nb) ^ Fintype.card E) ∧
    ∀ e : E, (2 : ℚ) ^ #{j' ∈ range r | e ∈ Λ j'} < 8 * Fintype.card E * (1 + pr nb) ^ r := by
  obtain ⟨n1, n2, n3, n4⟩ := hnn
  have hp := pr_pos hnb
  have hr : (0 : ℚ) < r := by exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le j) hs.j_lt
  have hm : (0 : ℚ) < Fintype.card E := by exact_mod_cast hE
  have h1p : (1 : ℚ) ≤ 1 + pr nb := by linarith
  unfold Ups at hU
  have u2 : Uinc nb r j Λ D < 1 := by linarith
  have u3 : Urow nb r j Λ D < 1 := by linarith
  have u4 : Ucol nb r j Λ D < 1 := by linarith
  refine ⟨?_, fun j' hj' => ?_, fun e => ?_⟩
  · unfold Uinc at u2
    rw [div_lt_one (by positivity)] at u2
    have : 0 ≤ pr nb * ((∑ j' ∈ range r, undRow j D j' : ℕ) : ℚ) := by positivity
    linarith
  · exact lt_of_sum_lt (range r) (fun j' => (2 : ℚ) ^ #(Λ j')) (fun j' => (1 + pr nb) ^ (Fintype.card E - undRow j D j')) (8 * r) _
      (by positivity) (fun _ _ => by positivity) (fun _ _ => by positivity)
      (fun _ _ => pow_le_pow_right₀ h1p (Nat.sub_le _ _)) u3 (mem_range.2 hj')
  · exact lt_of_sum_lt univ (fun e => (2 : ℚ) ^ #{j' ∈ range r | e ∈ Λ j'}) (fun e => (1 + pr nb) ^ (r - undCol r j D e))
      (8 * Fintype.card E) _ (by positivity) (fun _ _ => by positivity) (fun _ _ => by positivity)
      (fun _ _ => pow_le_pow_right₀ h1p (Nat.sub_le _ _)) u4 (mem_univ e)
end ClauseBound.ParityChecks.Structure
