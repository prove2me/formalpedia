-- Prove2me | solution 1 for FairSelling.TPS_truncSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:51.791528+00:00
-- url     : https://prove2.me/submissions/55de5857-f117-4786-bef3-a47233967909

import Mathlib
import Definitions.Def_RequestProject_Selling
import Theorems.Thm_FairSelling_mem_TPSset_zero
import Theorems.Thm_FairSelling_TPSset_bddAbove
import Theorems.Thm_FairSelling_truncSum_mono

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) :
    truncSum n v p (TPS n v p) = TPS n v p := by
  unfold TPS;
  by_contra h;
  -- Since $TPSset n v p$ is nonempty and bounded above, it must have a supremum.
  obtain ⟨s, hs⟩ : ∃ s, sSup (TPSset n v p) = s ∧ s ∈ TPSset n v p := by
    refine' ⟨ _, rfl, _ ⟩;
    apply_rules [ IsClosed.csSup_mem ];
    · refine' isClosed_le continuous_id _;
      exact Continuous.div_const ( continuous_finset_sum _ fun _ _ => Continuous.max ( continuous_const ) ( Continuous.min ( continuous_const ) continuous_id' ) ) _;
    · exact ⟨ 0, mem_TPSset_zero v p hp ⟩;
    · exact TPSset_bddAbove v p;
  obtain ⟨t, ht⟩ : ∃ t, t ∈ TPSset n v p ∧ t > s := by
    simp_all +decide [ TPSset ];
    exact ⟨ truncSum n v p s, by linarith [ show truncSum n v p s ≤ truncSum n v p ( truncSum n v p s ) from by exact truncSum_mono v p hs.2 ], lt_of_le_of_ne hs.2 ( Ne.symm h ) ⟩;
  linarith [ le_csSup ( show BddAbove ( TPSset n v p ) from TPSset_bddAbove v p ) ht.1 ]
end FairSelling
