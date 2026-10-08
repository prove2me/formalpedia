-- Prove2me | solution 1 for ClassicalSchur.coveredBySumFree_of_schurColoring
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-04T00:30:58.935607+00:00
-- url     : https://prove2.me/submissions/eed7c5f8-6824-441c-b750-f9db32ff956b

-- Generated from lean/ClassicalSchur/Midpoint.lean
--   imports : 0 platform node(s), 2 definition bundle(s)
--   inlined : 0 file-scoped / sub-threshold helper(s)
--   rename  : coveredBySumFree_of_schurColoring -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurColoring
import Mathlib

open Finset

open ClassicalSchur in
theorem solution {n N : ℕ} {c : ℕ → Fin n}
    (hc : SchurColoring N c) : CoveredBySumFree (Set.Icc 1 N) n := by
  refine ⟨fun i => {x | 1 ≤ x ∧ x ≤ N ∧ c x = i}, fun i x hx y hy hxy => ?_, fun x hx => ?_⟩
  · obtain ⟨hx1, -, hxi⟩ := hx
    obtain ⟨hy1, -, hyi⟩ := hy
    obtain ⟨-, hxyN, hxyi⟩ := hxy
    exact hc x y hx1 hy1 hxyN (hxi.trans hyi.symm) (hxyi.trans hxi.symm)
  · exact Set.mem_iUnion.mpr ⟨c x, hx.1, hx.2, rfl⟩
