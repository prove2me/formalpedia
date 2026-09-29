-- Prove2me | solution 1 for Freiman.separated_peaks
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:21:13.936306+00:00
-- url     : https://prove2.me/submissions/eec5db5c-c97c-46b2-abd3-4e7e0e55b6ca

import Definitions.Def_Freiman_wordRealization
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_Freiman_finite_exception_alphabet
import Theorems.Thm_Freiman_separated_copies_exist
import Theorems.Thm_Freiman_separated_copies_alphabet
import Theorems.Thm_Freiman_separated_copies_centers
import Theorems.Thm_Freiman_localValue_eventual_upper_of_limit_bounds
import Theorems.Thm_Freiman_separated_copies_limit_bound
import Theorems.Thm_Freiman_hasFiniteLimsup_lower_of_subsequence
import Theorems.Thm_Freiman_lagrange_symbolic
import Mathlib.Tactic.Linarith

open Freiman
set_option autoImplicit false

theorem solution (a : ℤ → ℕ+) (t : ℝ)
    (hcenter : localValue a 0 = t)
    (hmax : ∀ i : ℤ, localValue a i ≤ t)
    (hfinite : ∃ N : ℕ, ∀ i : ℤ, N ≤ i.natAbs → (a i : ℕ) ≤ 3)
    (hcondition : Real.sqrt 21 ≤ t ∨ (AvoidsBlock a [3, 1, 3, 1, 3] ∧ (4 * Real.sqrt 462 / 19 : ℝ) ≤ t)) :
    t ∈ lagrangeSpectrum := by
  have ha : HasFiniteAlphabet a := finite_exception_alphabet a hfinite
  obtain ⟨N, hN⟩ := hfinite
  obtain ⟨b, hb⟩ := separated_copies_exist a N
  have hba := separated_copies_alphabet a b N hb ha
  obtain ⟨p, hp, hplim⟩ := separated_copies_centers a b N hb
  rw [hcenter] at hplim
  have hupper := localValue_eventual_upper_of_limit_bounds b t hba
    (fun u hu y hy => separated_copies_limit_bound a b N t hb hN hmax hcondition u hu y hy)
  have hlower := hasFiniteLimsup_lower_of_subsequence
    (fun n : ℕ => localValue b (n : ℤ)) t p hp hplim
  rw [lagrange_symbolic]
  exact ⟨b, hupper, hlower⟩
