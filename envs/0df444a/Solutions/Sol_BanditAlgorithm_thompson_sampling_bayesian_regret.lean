-- Prove2me | solution 1 for BanditAlgorithm.thompson_sampling_bayesian_regret
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T21:42:58.403835+00:00
-- url     : https://prove2.me/submissions/7b093af0-3e0c-47e4-ad8f-1e078f7f9678

import Theorems.Thm_BanditAlgorithm_information_ratio_cumulative_bound_signed
import Theorems.Thm_BanditAlgorithm_bayesian_ts_information_accounting

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BanditAlgorithm

theorem _root_.solution {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (t : Fin n) (a : Fin k), X t a ∈ Set.Icc (0 : ℝ) 1)
    {π : BanditPolicy k} (hπ : IsBayesianTSPolicy Q π) :
    bayesianAdversarialRegret Q π ≤ Real.sqrt (k * n * Real.log k / 2) := by
  obtain ⟨δ, info, hregret, hpoint, hsum⟩ :=
    bayesian_ts_information_accounting Q hQ hπ
  rw [hregret]
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
  have h :=
    information_ratio_cumulative_bound_signed δ info ((k : ℝ) / 2)
      (Real.log k) (by positivity) hlog hpoint hsum
  convert h using 1 <;> ring

end BanditAlgorithm
