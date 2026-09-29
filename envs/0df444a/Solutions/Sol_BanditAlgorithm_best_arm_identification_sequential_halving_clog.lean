-- Prove2me | solution 1 for BanditAlgorithm.best_arm_identification_sequential_halving_clog
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T18:20:12.542454+00:00
-- url     : https://prove2.me/submissions/c947b979-d942-4de6-9f37-1e8329f2d4f7

import Theorems.Thm_BanditAlgorithm_sequential_halving_run_error_probability_bound_clog

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
      3 * (Nat.clog 2 k : ℝ) *
        Real.exp (-(n / (16 * H₂ * (Nat.clog 2 k : ℝ)))) := by
  have hrun : ∀ᵐ h ∂banditMeasure ν π n, IsSeqHalvingRun k n h (rec h) := hπ ν
  have heq :
      {h | 0 < banditGap ν (rec h)} =ᵐ[banditMeasure ν π n]
        {h | IsSeqHalvingRun k n h (rec h) ∧ 0 < banditGap ν (rec h)} := by
    filter_upwards [hrun] with h hh
    apply propext
    exact ⟨fun hgap ↦ ⟨hh, hgap⟩, And.right⟩
  rw [Measure.real, measure_congr heq]
  exact sequential_halving_run_error_probability_bound_clog
    ν hν hsorted hn H₂ hH₂ π rec
