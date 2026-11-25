-- Prove2me | solution 1 for CliqueMinors.isMinor_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:41:47.740037+00:00
-- url     : https://prove2.me/submissions/0db8fa9e-626a-4c7d-993c-b5c2cdf58495

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_induce_connected_mono

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open Relation
namespace CliqueMinors
theorem _root_.solution {G G' : SimpleGraph V} {H : SimpleGraph W} (hle : G' ≤ G)
    (h : IsMinor H G') : IsMinor H G := by
  obtain ⟨M⟩ := h
  refine ⟨⟨M.branch, M.branch_nonempty, fun w => induce_connected_mono hle (M.branch_connected w),
    M.branch_disjoint, fun w w' hww' => ?_⟩⟩
  obtain ⟨u, hu, v, hv, huv⟩ := M.branch_adjacent w w' hww'
  exact ⟨u, hu, v, hv, hle huv⟩
end CliqueMinors
