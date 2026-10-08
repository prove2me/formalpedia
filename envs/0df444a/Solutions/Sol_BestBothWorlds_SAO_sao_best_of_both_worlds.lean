-- Prove2me | solution 1 for BestBothWorlds.SAO.sao_best_of_both_worlds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T03:41:09.829774+00:00
-- url     : https://prove2.me/submissions/eaec4a90-d34c-4aa3-a5ac-119a6f771ef2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Definitions.Def_BestBothWorlds_SAO_RunNotation
import Theorems.Thm_BestBothWorlds_SAO_sao_stochastic_regret
import Theorems.Thm_BestBothWorlds_SAO_sao_adversarial_regret

open MeasureTheory
-- selective open: the child names stay fully qualified in `#print axioms` (shadow gate)
open BestBothWorlds.SAO (gap mean probStoch sao pseudoRegret minGap Adversary probEvent regret)

theorem solution (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    (∀ (ν : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)],
      (∀ i, ν i (Set.Icc 0 1)ᶜ = 0) → (∃ i, 0 < gap (mean ν) i) →
        1 - δ ≤ probStoch n (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) ν (fun _ I =>
          pseudoRegret (mean ν) I ≤
            260 * K * (1 + Real.log K) * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) ^ 2 / minGap (mean ν))) ∧
    (∀ adv : Adversary K, adv.IsBounded →
      1 - δ ≤ probEvent n (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) adv (fun I =>
        regret adv I ≤
          60 * (1 + Real.log K) * (1 + Real.log n) *
              Real.sqrt (n * K * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) + 5 * K ^ 2 * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) ^ 2) +
            200 * K ^ 2 * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) ^ 2)) := by
  refine ⟨fun ν _ hν hgap => ?_, fun adv hadv => ?_⟩
  · exact BestBothWorlds.SAO.sao_stochastic_regret K n hK hKn δ hδ0 hδ1 ν hν hgap
  · exact BestBothWorlds.SAO.sao_adversarial_regret K n hK hKn δ hδ0 hδ1 adv hadv
