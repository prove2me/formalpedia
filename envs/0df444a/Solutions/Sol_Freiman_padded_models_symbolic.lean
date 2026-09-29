-- Prove2me | solution 1 for Freiman.padded_models_symbolic
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:21:26.066097+00:00
-- url     : https://prove2.me/submissions/4d7bfc5e-9f8d-415c-8438-67018bc57d4e

import Definitions.Def_Freiman_paddedCopies
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_Freiman_padded_copies_exist
import Theorems.Thm_Freiman_padded_copies_centers
import Theorems.Thm_Freiman_padded_copies_upper_limsup
import Theorems.Thm_Freiman_hasFiniteLimsup_lower_of_subsequence
import Mathlib.Tactic.Linarith

open Freiman
set_option autoImplicit false

theorem solution (a : ℕ → ℤ → ℕ+) (d : ℕ+) (t : ℝ) (ε : ℕ → ℝ)
    (halphabet : ∃ M : ℕ, ∀ j : ℕ, ∀ i : ℤ, (a j i : ℕ) ≤ M)
    (hpad : ∀ j : ℕ, ∀ i : ℤ, j < i.natAbs → a j i = d)
    (hcentral : Filter.Tendsto (fun j : ℕ => localValue (a j) 0) Filter.atTop (nhds t))
    (hbound : ∀ j : ℕ, ∀ i : ℤ, localValue (a j) i ≤ t + ε j)
    (heps : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hbackground : Real.sqrt ((((d : ℕ) : ℝ) ^ 2) + 4) ≤ t) :
    t ∈ symbolicLagrangeSpectrum := by
  obtain ⟨b, hb⟩ := padded_copies_exist a d
  obtain ⟨p, hp, hplim⟩ := padded_copies_centers a b d t hb hcentral
  have hupper := padded_copies_upper_limsup a b d t ε hb hpad hbound heps hbackground
  have hlower := hasFiniteLimsup_lower_of_subsequence (fun n : ℕ => localValue b (n : ℤ)) t p hp hplim
  exact ⟨b, hupper, hlower⟩
