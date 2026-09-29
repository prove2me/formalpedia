-- Prove2me | solution 1 for BanditAlgorithm.best_arm_identification_sequential_halving
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T19:43:19.340216+00:00
-- url     : https://prove2.me/submissions/b0d260fa-f7a2-49bf-b1b4-2af722c11449
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BanditAlgorithm_sequential_halving_run_error_probability_bound

open MeasureTheory
open BanditAlgorithm

theorem solution {k n : ℕ}
    (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    (hsorted : ∀ i j : Fin k, i ≤ j → banditArmMean ν j ≤ banditArmMean ν i)
    (hn : k * Nat.clog 2 k ≤ n) (H₂ : ℝ)
    (hH₂ : ∀ i : Fin k, 0 < banditGap ν i →
      ((i : ℕ) + 1 : ℝ) / banditGap ν i ^ 2 ≤ H₂)
    (π : BanditPolicy k) (rec : BanditHistory k n → Fin k)
    (hπ : IsSequentialHalvingPolicy k n π rec) :
    (banditMeasure ν π n).real {h | 0 < banditGap ν (rec h)} ≤
      3 * Real.logb 2 k * Real.exp (-(n / (16 * H₂ * Real.logb 2 k))) := by
  have hrun : ∀ᵐ h ∂banditMeasure ν π n, IsSeqHalvingRun k n h (rec h) :=
    hπ ν
  have heq :
      {h | 0 < banditGap ν (rec h)} =ᵐ[banditMeasure ν π n]
        {h | IsSeqHalvingRun k n h (rec h) ∧ 0 < banditGap ν (rec h)} := by
    filter_upwards [hrun] with h hh
    apply propext
    change (0 < banditGap ν (rec h)) ↔
      (IsSeqHalvingRun k n h (rec h) ∧ 0 < banditGap ν (rec h))
    exact ⟨fun hgap ↦ ⟨hh, hgap⟩, And.right⟩
  rw [Measure.real, measure_congr heq]
  exact sequential_halving_run_error_probability_bound
    ν hν hsorted hn H₂ hH₂ π rec
