-- Prove2me | solution 1 for CLRS.DFS.correctness_and_running_time
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:22:45.453121+00:00
-- url     : https://prove2.me/submissions/b8aa78ba-3d81-45e4-8b3c-0e3142764be3

import Theorems.Thm_CLRS_DFS_correctness_and_explicit_running_time

set_option autoImplicit false
open Algo2LeanGenerated CLRS.GraphTraversal CLRS.DFS

theorem solution :
    ∃ C : Nat, 0 < C ∧
      ∀ (before : Heap) (graph : ObjectRef) (g : Graph),
        GraphRep before graph g →
        ∃ (after : Heap) (result : ObjectRef),
          Algo.dfs.dfs.Call before graph after result ∧
          Post before after result g (fun i : Int => i) ∧
          work before after ≤ C * (1 + g.size + edgeCount g) := by
  refine ⟨8,by omega,?_⟩
  intro before graph g represented
  obtain ⟨after,result,call,post,cost⟩ :=
    CLRS.DFS.correctness_and_explicit_running_time before graph g represented
  refine ⟨after,result,call,post,?_⟩
  calc
    work before after ≤ 7 + 8*g.size + 2*edgeCount g := cost
    _ ≤ 8*(1+g.size+edgeCount g) := by omega
