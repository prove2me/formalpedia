-- Prove2me | solution 1 for ClassicalSchur.exists_schurColoring_of_coveredBySumFree
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-04T00:30:59.608557+00:00
-- url     : https://prove2.me/submissions/51ccf142-1fba-4cf5-b2ce-28c87ba311f4

-- Generated from lean/ClassicalSchur/Midpoint.lean
--   imports : 0 platform node(s), 2 definition bundle(s)
--   inlined : 0 file-scoped / sub-threshold helper(s)
--   rename  : exists_schurColoring_of_coveredBySumFree -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurColoring
import Mathlib

open Finset

open ClassicalSchur in
theorem solution {n N : ℕ} (hn : 0 < n)
    (h : CoveredBySumFree (Set.Icc 1 N) n) : ∃ c : ℕ → Fin n, SchurColoring N c := by
  obtain ⟨C, hC, hcov⟩ := h
  have hmem : ∀ x : ℕ, ∃ i : Fin n, 1 ≤ x → x ≤ N → x ∈ C i := by
    intro x
    by_cases hx : 1 ≤ x ∧ x ≤ N
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
      exact ⟨i, fun _ _ => hi⟩
    · exact ⟨⟨0, hn⟩, fun h1 h2 => absurd ⟨h1, h2⟩ hx⟩
  choose c hc using hmem
  refine ⟨c, fun x y hx hy hxy hxy' hsum => ?_⟩
  have m1 := hc x hx (by omega)
  have m2 := hc y hy (by omega)
  have m3 := hc (x + y) (by omega) hxy
  rw [← hxy'] at m2
  rw [hsum] at m3
  exact hC (c x) x m1 y m2 m3
