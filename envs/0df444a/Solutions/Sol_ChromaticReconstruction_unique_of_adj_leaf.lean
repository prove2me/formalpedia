-- Prove2me | solution 1 for ChromaticReconstruction.unique_of_adj_leaf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:44:30.155808+00:00
-- url     : https://prove2.me/submissions/bf8806ba-d2e9-45dd-b546-6d4076efca78

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
import Theorems.Thm_ChromaticReconstruction_card_le_two_of_adj_leaves
import Theorems.Thm_ChromaticReconstruction_degree_one_of_repeated

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] {S : SimpleGraph K}
namespace ChromaticReconstruction
theorem _root_.solution {w : K → ℕ} (hS : S.Connected) (hk : 3 ≤ Fintype.card K)
    (hMI : MIso S w) {x y : K} (hx : S.degree x = 1) (hxy : S.Adj x y) :
    Multiset.count (w y) (wts w) = 1 := by
  by_contra h
  have := card_le_two_of_adj_leaves hS hxy hx (degree_one_of_repeated hMI h)
  omega
end ChromaticReconstruction
