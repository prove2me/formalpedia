-- Prove2me | solution 1 for FairSelling.outcome_of_matching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:47:27.414639+00:00
-- url     : https://prove2.me/submissions/8522c5a9-d0f3-40d9-9a16-964148a78859

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
import Theorems.Thm_FairSelling_outcome_of_bundles

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    {w : G → ℝ} {τ : ℝ} {kept : Fin 3 → Finset G} {sold : Finset G} {money : Fin 3 → ℝ}
    {lo : Fin 3} (hcan : IsCanonical w p τ kept sold money lo)
    (σ : Equiv.Perm (Fin 3))
    (hacc : ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ vbarSum (v i) p (kept (σ i)) + money (σ i)) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  obtain ⟨hdisj, hsold, hm0, hmsum, -, -⟩ := hcan
  refine outcome_of_bundles v p hp (fun i => kept (σ i)) sold (fun i => money (σ i))
    (fun i j hij => hdisj _ _ (fun h => hij (σ.injective h))) (fun i => hsold _)
    (fun i => hm0 _) ?_ hacc
  calc ∑ i, money (σ i) = ∑ k, money k := Equiv.sum_comp σ money
    _ ≤ ∑ g ∈ sold, p g := hmsum
end FairSelling
