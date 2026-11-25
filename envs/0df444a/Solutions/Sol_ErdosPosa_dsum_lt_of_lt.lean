-- Prove2me | solution 1 for ErdosPosa.dsum_lt_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:32:01.734394+00:00
-- url     : https://prove2.me/submissions/56224543-743a-429e-8fb1-af4ac268eda1

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Definitions.Def_ErdosPosaLib_EPMaximal
public import Theorems.Thm_ErdosPosa_deg_mono


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution [Fintype V] {H K : SimpleGraph V} (hHK : H ≤ K) {u v : V} (huv : K.Adj u v)
    (hn : ¬ H.Adj u v) : dsum H < dsum K := by
  unfold dsum
  apply Finset.sum_lt_sum
  · intro w _; exact deg_mono hHK w
  · refine ⟨u, Finset.mem_univ _, ?_⟩
    apply Set.ncard_lt_ncard _ (Set.toFinite _)
    refine Set.ssubset_iff_subset_ne.2 ⟨fun w hw => hHK hw, fun h => hn ?_⟩
    have : v ∈ K.neighborSet u := huv
    rw [← h] at this
    exact this
end ErdosPosa
