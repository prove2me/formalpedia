-- Prove2me | solution 1 for FairChores.Outcome.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:09.824303+00:00
-- url     : https://prove2.me/submissions/177da251-1fd2-4e12-9a98-7125ae614c78

import Mathlib
import Definitions.Def_RequestProject_ChoresModel

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
namespace FairChores
namespace Outcome
theorem _root_.solution {o : Outcome T n} (hvalid : o.Valid p) (f : T → ℝ) :
    ∑ t, f t = (∑ t ∈ o.outsourced, f t) + ∑ j, ∑ t ∈ o.kept j, f t := by
  classical
  obtain ⟨hdo, hdk, hcov, -, -⟩ := hvalid
  have hdisj : Disjoint o.outsourced (Finset.univ.biUnion o.kept) := by
    refine Finset.disjoint_left.mpr fun x hx hx' => ?_
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hx'
    exact Finset.disjoint_left.mp (hdo j) hx hj
  have h1 : ∑ t, f t = ∑ t ∈ o.outsourced ∪ Finset.univ.biUnion o.kept, f t := by
    rw [hcov]
  rw [h1, Finset.sum_union hdisj, Finset.sum_biUnion (fun i _ j _ hij => hdk i j hij)]
end Outcome
end FairChores
