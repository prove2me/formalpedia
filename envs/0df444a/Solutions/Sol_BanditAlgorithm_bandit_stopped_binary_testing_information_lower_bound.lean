-- Prove2me | solution 1 for BanditAlgorithm.bandit_stopped_binary_testing_information_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T19:30:52.794475+00:00
-- url     : https://prove2.me/submissions/c016c5d4-317d-49a8-acb8-9ea34737d89b

import Theorems.Thm_BanditAlgorithm_bandit_stopped_bretagnolle_huber

open MeasureTheory ProbabilityTheory InformationTheory ENNReal
open BanditAlgorithm

theorem solution
    {k : ℕ} (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (ν ν' : StochasticBandit k) (π : BanditPolicy k)
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ)
    (hfinite : ∫⁻ ω, (τ ω : ℝ≥0∞) ∂banditTrajMeasure ν π < ⊤)
    (A : Set (ℕ → Fin k × ℝ)) (hA : Measurable[hτ.measurableSpace] A)
    (hνerr : (banditTrajMeasure ν π).real Aᶜ ≤ δ)
    (hν'err : (banditTrajMeasure ν' π).real A ≤ δ) :
    ENNReal.ofReal (Real.log (1 / (4 * δ))) ≤
      ∑ i, (∫⁻ ω, ∑' t : ℕ,
          if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0
        ∂banditTrajMeasure ν π) * klDiv (ν.P i) (ν'.P i) := by
  let I : ℝ≥0∞ :=
    ∑ i, (∫⁻ ω, ∑' t : ℕ,
        if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0
      ∂banditTrajMeasure ν π) * klDiv (ν.P i) (ν'.P i)
  change ENNReal.ofReal (Real.log (1 / (4 * δ))) ≤ I
  by_cases hItop : I = ⊤
  · simp [hItop]
  apply (ENNReal.ofReal_le_iff_le_toReal hItop).2
  have hbh :
      (2 : ℝ)⁻¹ * Real.exp (-I.toReal) ≤
        (banditTrajMeasure ν π).real Aᶜ +
          (banditTrajMeasure ν' π).real A := by
    simpa only [I] using bandit_stopped_bretagnolle_huber
      ν ν' π τ hτ hfinite A hA (by simpa only [I] using hItop)
  have hhalf : (2 : ℝ)⁻¹ * Real.exp (-I.toReal) ≤ 2 * δ :=
    hbh.trans <| by linarith
  have hexp : Real.exp (-I.toReal) ≤ 4 * δ := by
    norm_num at hhalf ⊢
    linarith
  have h4δ : 0 < 4 * δ := mul_pos (by norm_num) hδ.1
  have hlog : -I.toReal ≤ Real.log (4 * δ) := by
    rw [← Real.log_exp (-I.toReal)]
    exact Real.log_le_log (Real.exp_pos _) hexp
  rw [one_div, Real.log_inv]
  linarith
