-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.sensitivityClaim_of_local_data
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:15:34.43022+00:00
-- url     : https://prove2.me/submissions/e5bc97ac-889b-4833-bf99-55c90ded37f8

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Theorems.Thm_FairPricingPerturbation_welfare_sensitivity

open CohenPriceFairness.LocalWelfare
open Filter Topology Asymptotics

theorem solution (m : Market) (b : Prices) (k : Metric) (C : ℝ → Prop)
    (r mm σ : Fin 2 → ℝ)
    (hb : ∀ i, 0 < b i)
    (hopt : ∀ i, ∀ p, 0 ≤ p → profit m i p ≤ profit m i (b i))
    (hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → profit m i (b i) - δ ≤ profit m i p →
      |p - b i| < ε)
    (hcont : ∃ η > 0, ∀ i, ContinuousOn (profit m i) (Set.Icc (b i - η) (b i + η)) ∧
      ContinuousOn (metricValue m k i) (Set.Icc (b i - η) (b i + η)))
    (hr : ∀ i, r i < 0)
    (hRt : ∀ i, (fun h => profit m i (b i + h) - profit m i (b i) - r i / 2 * h ^ 2)
      =o[𝓝 0] (fun h => h ^ 2))
    (hMd : ∀ i, HasDerivAt (metricValue m k i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hSd : ∀ i, HasDerivAt (surplus m i) (σ i) (b i))
    (hgap : metricValue m k 0 (b 0) ≠ metricValue m k 1 (b 1))
    (hC : C (m.population 0 * σ 0 * ((-(metricValue m k 0 (b 0) - metricValue m k 1 (b 1)) /
        (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      m.population 1 * σ 1 * (-((-(metricValue m k 0 (b 0) - metricValue m k 1 (b 1)) /
        (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)))) :
    SensitivityClaim m b k C := by
  obtain ⟨h1, h2⟩ := FairPricingPerturbation.welfare_sensitivity (profit m) (metricValue m k) (surplus m) m.population
    b r mm σ hb hopt hloc hcont hr hRt hMd hmm hSd hgap
  refine ⟨?_, ?_⟩
  · obtain ⟨ε, hε, H⟩ := h1
    classical
    let P : ℝ → Prices := fun α =>
      if α = 0 then b else if h : α ∈ Set.Icc (0:ℝ) ε then Classical.choose (H α h) else b
    refine ⟨P, by simp [P], min ε 1, lt_min hε one_pos, min_le_right _ _, ?_⟩
    intro α hα
    have hα1 : α ∈ Set.Icc (0:ℝ) 1 := ⟨hα.1, hα.2.trans (min_le_right _ _)⟩
    by_cases h0 : α = 0
    · subst h0
      have hP : P 0 = b := by simp [P]
      rw [hP]
      refine ⟨⟨hα1, fun i => (hb i).le, ?_⟩, ?_⟩
      · simp
      · intro q hq
        exact add_le_add (hopt 0 _ (hq.2.1 0)) (hopt 1 _ (hq.2.1 1))
    · have hαε : α ∈ Set.Icc (0:ℝ) ε := ⟨hα.1, hα.2.trans (min_le_left _ _)⟩
      have hP : P α = Classical.choose (H α hαε) := by simp only [P, if_neg h0, dif_pos hαε]
      obtain ⟨hfeas, hmax⟩ := Classical.choose_spec (H α hαε)
      rw [hP]
      refine ⟨⟨hα1, hfeas.1, hfeas.2⟩, ?_⟩
      intro q hq
      exact hmax q ⟨hq.2.1, hq.2.2⟩
  · rintro P ⟨hP0, ε, hε, hε1, hP⟩
    refine ⟨_, ?_, hC⟩
    have hyp : ∃ ε > 0, ∀ α ∈ Set.Ioc (0 : ℝ) ε,
        ((∀ i, 0 ≤ P α i) ∧
          |metricValue m k 0 (P α 0) - metricValue m k 1 (P α 1)| ≤
            (1 - α) * |metricValue m k 0 (b 0) - metricValue m k 1 (b 1)|) ∧
        ∀ q : Fin 2 → ℝ,
          ((∀ i, 0 ≤ q i) ∧ |metricValue m k 0 (q 0) - metricValue m k 1 (q 1)| ≤
            (1 - α) * |metricValue m k 0 (b 0) - metricValue m k 1 (b 1)|) →
          profit m 0 (q 0) + profit m 1 (q 1) ≤ profit m 0 (P α 0) + profit m 1 (P α 1) := by
      refine ⟨ε, hε, fun α hα => ?_⟩
      have hαI : α ∈ Set.Icc (0:ℝ) ε := Set.Ioc_subset_Icc_self hα
      obtain ⟨⟨_, hnn, hg⟩, hmax⟩ := hP α hαI
      exact ⟨⟨hnn, hg⟩, fun q hq => hmax q ⟨⟨hαI.1, hαI.2.trans hε1⟩, hq.1, hq.2⟩⟩
    have := h2 P hyp
    show Tendsto (fun α => (welfare m (P α) - welfare m (P 0)) / α) _ _
    rw [hP0]
    exact this

