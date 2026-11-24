-- Prove2me | solution 1 for FairSelling.exists_threequarter_MMS_three_of_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:09:04.962473+00:00
-- url     : https://prove2.me/submissions/348ccc04-5740-4797-94bc-0338ffd51da1

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
import Theorems.Thm_FairSelling_lemmaFourCash_of_sold
import Theorems.Thm_FairSelling_outcome_of_singleLossConfig
import Theorems.Thm_FairSelling_matching_phase_three

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (hL4 : LemmaFourCashSold G)
    (v : Fin 3 → G → ℝ) (p : G → ℝ) (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ i g, vbar (v i) p g < (3 / 4 : ℝ) * MMS 3 (v i) p)
    (a : Fin 3) (hmax : ∀ i, MMS 3 (v i) p ≤ MMS 3 (v a) p)
    (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (lo : Fin 3)
    (hcan : IsCanonicalStrict (v a) p ((3 / 4 : ℝ) * MMS 3 (v a) p) kept sold money lo) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  rcases matching_phase_three v p hv hp hnobig a hmax kept sold money lo hcan with h | h
  · exact h
  · exact outcome_of_singleLossConfig (lemmaFourCash_of_sold hL4) v p hv hp hnobig h
end FairSelling
