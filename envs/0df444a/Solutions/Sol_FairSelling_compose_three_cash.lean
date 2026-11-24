-- Prove2me | solution 1 for FairSelling.compose_three_cash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:00:26.395589+00:00
-- url     : https://prove2.me/submissions/1151c3ac-deb2-4d3a-89d4-bfbaea9b0dd3

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Theorems.Thm_FairSelling_dropCashOutcome_sold_disjoint
import Theorems.Thm_FairSelling_dropCashOutcome_kept_disjoint
import Theorems.Thm_FairSelling_dropCashOutcome_budget
import Theorems.Thm_FairSelling_util_dropCashOutcome
import Theorems.Thm_FairSelling_compose_three_with_reserve

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (a b d : Fin 3) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (Ka Sa : Finset G) (ma cash : ℝ)
    (hKSa : Disjoint Ka Sa) (hma0 : 0 ≤ ma) (hcash0 : 0 ≤ cash)
    (hbudget : ma + cash ≤ ∑ g ∈ Sa, p g)
    (haU : (3/4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p Ka + ma)
    (o2 : Outcome (Option G) 2)
    (ho2 : o2.Valid (cashPrice (Finset.univ \ (Ka ∪ Sa)) p cash))
    (hb : (3/4 : ℝ) * MMS 3 (v b) p ≤
      util (cashVal (Finset.univ \ (Ka ∪ Sa)) (v b)) o2 0)
    (hd : (3/4 : ℝ) * MMS 3 (v d) p ≤
      util (cashVal (Finset.univ \ (Ka ∪ Sa)) (v d)) o2 1) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3/4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  apply compose_three_with_reserve v p hp a b d hab had hbd Ka Sa ma cash hKSa hma0 hbudget haU (dropCashOutcome o2);
  any_goals rw [ util_dropCashOutcome ] ; assumption;
  · exact dropCashOutcome_sold_disjoint o2 ho2.1;
  · exact dropCashOutcome_kept_disjoint o2 ho2.2.1;
  · exact fun i => ho2.2.2.1 i;
  · convert dropCashOutcome_budget ( Finset.univ \ ( Ka ∪ Sa ) ) p cash o2 hcash0 ho2.2.2.2 using 1
end FairSelling
