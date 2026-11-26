-- Prove2me | solution 1 for CSeparatedNPComplete.perf_square_non_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:51:54.382798+00:00
-- url     : https://prove2.me/submissions/e0187ccb-6e50-407b-af67-9d8b74647d03

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : Nat} {s : Vec n}
    (hs : perf_square_vec s) : is_vec_leq 0 s := by
  intro i
  obtain ⟨k, hk⟩ := hs i
  rw [hk]
  positivity
end CSeparatedNPComplete
