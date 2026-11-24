-- Prove2me | solution 1 for FairSelling.finish_from_cash_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:01:56.318693+00:00
-- url     : https://prove2.me/submissions/53636691-8b26-47b1-9639-e0764b59483d

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Theorems.Thm_FairSelling_compose_three_cash
import Theorems.Thm_FairSelling_cashPrice_nonneg
import Theorems.Thm_FairSelling_cashVal_nonneg
import Theorems.Thm_FairSelling_exists_MMS_two


set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (a b d : Fin 3) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (Ka Sa : Finset G) (ma cash : ℝ)
    (hKSa : Disjoint Ka Sa) (hma0 : 0 ≤ ma) (hcash0 : 0 ≤ cash)
    (hbudget : ma + cash ≤ ∑ g ∈ Sa, p g)
    (haU : (3/4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p Ka + ma)
    (hRb : (3/4 : ℝ) * MMS 3 (v b) p ≤
      MMS 2 (cashVal (Finset.univ \ (Ka ∪ Sa)) (v b))
        (cashPrice (Finset.univ \ (Ka ∪ Sa)) p cash))
    (hRd : (3/4 : ℝ) * MMS 3 (v d) p ≤
      MMS 2 (cashVal (Finset.univ \ (Ka ∪ Sa)) (v d))
        (cashPrice (Finset.univ \ (Ka ∪ Sa)) p cash)) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3/4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  obtain ⟨o2, ho2⟩ : ∃ o2 : Outcome (Option G) 2, o2.Valid (cashPrice (Finset.univ \ (Ka ∪ Sa)) p cash) ∧ ∀ i, MMS 2 (cashVal (Finset.univ \ (Ka ∪ Sa)) (v (if i = 0 then b else d))) (cashPrice (Finset.univ \ (Ka ∪ Sa)) p cash) ≤ util (cashVal (Finset.univ \ (Ka ∪ Sa)) (v (if i = 0 then b else d))) o2 i := by
    convert exists_MMS_two ( fun i => cashVal ( Finset.univ \ ( Ka ∪ Sa ) ) ( v ( if i = 0 then b else d ) ) ) ( cashPrice ( Finset.univ \ ( Ka ∪ Sa ) ) p cash ) _ _ using 1;
    · exact fun i g => cashVal_nonneg _ _ ( hv _ ) _;
    · exact fun g => cashPrice_nonneg _ _ hp _ hcash0 g;
  refine' compose_three_cash v p hp a b d hab had hbd Ka Sa ma cash hKSa hma0 hcash0 hbudget haU o2 ho2.1 _ _;
  · exact le_trans hRb ( ho2.2 0 );
  · exact le_trans hRd ( ho2.2 1 )
end FairSelling
