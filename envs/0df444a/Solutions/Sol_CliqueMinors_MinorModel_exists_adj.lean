-- Prove2me | solution 1 for CliqueMinors.MinorModel.exists_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:39:55.409973+00:00
-- url     : https://prove2.me/submissions/effcd6a3-47d8-4097-8790-5ad322c4d173

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_reflTransGen_of_connected

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open Relation
namespace CliqueMinors
namespace MinorModel
theorem _root_.solution {G : SimpleGraph V} {r : ℕ}
    (M : MinorModel G (⊤ : SimpleGraph (Fin r))) (hr : 2 ≤ r) (i : Fin r) {v : V}
    (hv : v ∈ M.branch i) : ∃ u, G.Adj v u := by
  obtain ⟨j, hj⟩ : ∃ j : Fin r, j ≠ i := by
    by_cases h : (i : ℕ) = 0
    · exact ⟨⟨1, by omega⟩, fun h' => by simp [Fin.ext_iff] at h'; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h' => by simp [Fin.ext_iff] at h'; omega⟩
  obtain ⟨u, hu, w, _, huw⟩ := M.branch_adjacent i j (by simpa using hj.symm)
  rcases (reflTransGen_of_connected (M.branch_connected i) hv hu).cases_head with h | ⟨c, hc, _⟩
  · subst h; exact ⟨w, huw⟩
  · exact ⟨c, hc.2.2⟩
end MinorModel
end CliqueMinors
