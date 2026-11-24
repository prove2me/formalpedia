-- Prove2me | solution 1 for FairSelling.exists_threequarter_MMS_three_nobig
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:10:57.486733+00:00
-- url     : https://prove2.me/submissions/58a76416-55d5-42c3-ab8c-cb6dd2850cfb

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_CanonicalStrict
import Theorems.Thm_FairSelling_canonical_partition_three_strict
import Theorems.Thm_FairSelling_exists_threequarter_MMS_three_of_canonical


set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (hL4 : LemmaFourCashSold G)
    (v : Fin 3 → G → ℝ) (p : G → ℝ) (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ i g, vbar (v i) p g < (3 / 4 : ℝ) * MMS 3 (v i) p) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  classical
  obtain ⟨a, -, hmax⟩ :=
    Finset.exists_max_image (f := fun i => MMS 3 (v i) p) Finset.univ ⟨0, Finset.mem_univ 0⟩
  obtain ⟨kept, sold, money, lo, hcan⟩ :=
    canonical_partition_three_strict (v a) p (hv a) hp (hnobig a)
  exact exists_threequarter_MMS_three_of_canonical hL4 v p hv hp hnobig a
    (fun i => hmax i (Finset.mem_univ i)) kept sold money lo hcan
end FairSelling
