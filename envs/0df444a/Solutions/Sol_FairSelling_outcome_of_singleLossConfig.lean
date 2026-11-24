-- Prove2me | solution 1 for FairSelling.outcome_of_singleLossConfig
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:03:25.077326+00:00
-- url     : https://prove2.me/submissions/a405ec1c-2b00-48bd-83cb-5cdf7d33cfcd

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
import Theorems.Thm_FairSelling_fin3_others
import Theorems.Thm_FairSelling_finish_from_cash_reduction


set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (hL4 : LemmaFourCash G) (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ i g, vbar (v i) p g < (3 / 4 : ℝ) * MMS 3 (v i) p)
    (h : SingleLossConfig v p) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  obtain ⟨x, K, S, m, hKS, hm0, hmS, hScard, hKcard, hserved, hrest⟩ := h
  obtain ⟨y, z, hyx, hzx, hyz⟩ := fin3_others x
  have key : ∀ i, i ≠ x → (3 / 4 : ℝ) * MMS 3 (v i) p ≤
      MMS 2 (cashVal (Finset.univ \ (K ∪ S)) (v i))
        (cashPrice (Finset.univ \ (K ∪ S)) p ((∑ g ∈ S, p g) - m)) := by
    intro i hi
    rcases hrest i hi with h1 | ⟨h2, h3⟩
    · exact h1
    · exact hL4 (v i) p (hv i) hp (hnobig i) K S m hKS hm0 hmS hScard hKcard h3 h2
  exact finish_from_cash_reduction v p hv hp x y z (Ne.symm hyx) (Ne.symm hzx) hyz
    K S m ((∑ g ∈ S, p g) - m) hKS hm0 (by linarith) (by linarith) hserved
    (key y hyx) (key z hzx)
end FairSelling
