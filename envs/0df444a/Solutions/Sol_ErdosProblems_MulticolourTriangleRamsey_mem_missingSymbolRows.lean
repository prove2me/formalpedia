-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.mem_missingSymbolRows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/11f0bdfa-2423-4f62-b070-a7643fa3a0c1

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H m : ℕ)
    (T : Finset (Fin m → Fin H)) (symbol : Fin H)
    (row : (Fin m → Fin H) → Fin H) :
    row ∈ missingSymbolRows H m T symbol ↔
      ∀ column ∈ T, row column ≠ symbol := by
  classical
  rw [missingSymbolRows, Fintype.mem_piFinset]
  constructor
  · intro hrow column hcolumn
    simpa [hcolumn] using hrow column
  · intro hrow column
    by_cases hcolumn : column ∈ T
    · simpa [hcolumn] using hrow column hcolumn
    · simp [hcolumn]
end ErdosProblems.MulticolourTriangleRamsey
