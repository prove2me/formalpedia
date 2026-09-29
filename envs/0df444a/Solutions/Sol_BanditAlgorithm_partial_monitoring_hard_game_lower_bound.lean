-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_hard_game_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T17:07:42.627215+00:00
-- url     : https://prove2.me/submissions/c88b4ae6-df4b-43da-8f03-ecd892e97ab6

import Theorems.Thm_BanditAlgorithm_partial_monitoring_hard_lower_of_tradeoff
import Theorems.Thm_BanditAlgorithm_partial_monitoring_hard_game_tradeoff

open MeasureTheory ProbabilityTheory

theorem solution {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : BanditAlgorithm.PartialMonitoringGame k d 𝕊)
    (hglob : BanditAlgorithm.GloballyObservable G)
    (hloc : ¬ BanditAlgorithm.LocallyObservable G) :
    ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, c * (n : ℝ) ^ ((2 : ℝ) / 3) ≤
        BanditAlgorithm.pmMinimaxRegret G n := by
  apply BanditAlgorithm.partial_monitoring_hard_lower_of_tradeoff G
  exact BanditAlgorithm.partial_monitoring_hard_game_tradeoff G hglob hloc
