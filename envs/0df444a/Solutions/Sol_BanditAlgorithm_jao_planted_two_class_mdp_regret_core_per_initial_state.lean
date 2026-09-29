-- Prove2me | solution 1 for BanditAlgorithm.jao_planted_two_class_mdp_regret_core_per_initial_state
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-06T03:20:32.680202+00:00
-- url     : https://prove2.me/submissions/9581286d-db1a-4368-8bcf-c94118795591

import Theorems.Thm_BanditAlgorithm_jao_two_class_gadget_optimal_gain_ge
import Theorems.Thm_BanditAlgorithm_jao_two_class_reward_le_reference_plus_planted_plays_two_valued
import Theorems.Thm_BanditAlgorithm_jao_two_class_reference_occupancy_bounds_two_valued
import Theorems.Thm_BanditAlgorithm_jao_two_class_planted_plays_change_of_measure_two_valued
import Theorems.Thm_BanditAlgorithm_jao_collapsed_bandit_regret_arithmetic

open MeasureTheory ProbabilityTheory
open BanditAlgorithm

theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ (S A m : ℕ), 20 ≤ m → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 3 →
        ∀ T : ℕ, (16 : ℝ) * m ≤ δ * T →
          ∀ ε : ℝ, ε = 1 / 5 * Real.sqrt (δ * m / T) →
            ∀ (ρ : Fin S → ℝ) (up down : Fin S → Fin S) (nav : Fin S → Fin A → Fin S)
              (arm : Fin m → Fin S × Fin A)
              (M : Fin m → FiniteMDP S A) (M₀ : FiniteMDP S A),
              Function.Injective arm →
              (∀ i, ρ (arm i).1 = 0) →
              (∀ i, nav (arm i).1 (arm i).2 = (arm i).1) →
              (∀ i, down (up (arm i).1) = (arm i).1) →
              (∀ s, ρ s = 0 ∨ ρ s = 1) →
              (∀ s b, M₀.r s b = ρ s) →
              (∀ s b, ρ s = 0 →
                  ρ (up s) = 1 ∧ ρ (nav s b) = 0 ∧ up s ≠ nav s b ∧
                  (M₀.P s b (up s) : ℝ) = δ ∧
                  (M₀.P s b (nav s b) : ℝ) = 1 - δ) →
              (∀ s b, ρ s = 1 →
                  ρ (down s) = 0 ∧ down s ≠ s ∧
                  (M₀.P s b (down s) : ℝ) = δ ∧
                  (M₀.P s b s : ℝ) = 1 - δ) →
              (∀ i, ∀ s b, (M i).r s b = ρ s) →
              (∀ i, ∀ s b, ρ s = 0 →
                  ((M i).P s b (up s) : ℝ)
                      = δ + (if (s, b) = arm i then ε else 0) ∧
                  ((M i).P s b (nav s b) : ℝ)
                      = 1 - δ - (if (s, b) = arm i then ε else 0)) →
              (∀ i, ∀ s b, ρ s = 1 →
                  ((M i).P s b (down s) : ℝ) = δ ∧
                  ((M i).P s b s : ℝ) = 1 - δ) →
              ∀ π : MDPPolicy S A, ∀ s₀ : Fin S,
                ∃ i : Fin m,
                  c * Real.sqrt ((T : ℝ) * m / δ) ≤
                    ∫ h, mdpRegret (M i) T h
                      ∂(mdpMeasure (M i) (mdpStateDirac s₀) π T) := by
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro S A m hm δ hδ0 hδ T hT ε hεdef ρ up down nav arm M M₀ hinj harm0 hfix hud hρ01
    hr₀ hrow0₀ hrow1₀ hrM hrow0 hrow1 π s₀
  have hm0 : (0 : ℝ) < m := by
    have : (20 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hT0 : (0 : ℝ) < T := by
    by_cases h : (T : ℝ) ≤ 0
    · nlinarith
    · linarith [not_le.mp h]
  have hquot : 0 < δ * m / T := by positivity
  have hε0 : 0 < ε := by
    have := Real.sqrt_pos.mpr hquot
    simp only [hεdef]; linarith
  have hεδ : ε ≤ δ := by
    have hkey : δ * m / T ≤ (5 * δ) ^ 2 := by
      rw [div_le_iff₀ hT0]
      nlinarith [mul_le_mul_of_nonneg_left hT (le_of_lt hδ0)]
    have := Real.sqrt_le_sqrt hkey
    rw [Real.sqrt_sq (by linarith)] at this
    simp only [hεdef]; linarith
  -- the planted MDPs inherit the class facts from the reference MDP
  have hrow0' : ∀ i, ∀ s b, ρ s = 0 →
      ρ (up s) = 1 ∧ ρ (nav s b) = 0 ∧ up s ≠ nav s b ∧
      ((M i).P s b (up s) : ℝ)
          = δ + (if (s, b) = ((arm i).1, (arm i).2) then ε else 0) ∧
      ((M i).P s b (nav s b) : ℝ)
          = 1 - δ - (if (s, b) = ((arm i).1, (arm i).2) then ε else 0) := by
    intro i s b hs
    obtain ⟨h1, h2, h3, -, -⟩ := hrow0₀ s b hs
    obtain ⟨h4, h5⟩ := hrow0 i s b hs
    exact ⟨h1, h2, h3, h4, h5⟩
  have hrow1' : ∀ i, ∀ s b, ρ s = 1 →
      ρ (down s) = 0 ∧ down s ≠ s ∧
      ((M i).P s b (down s) : ℝ) = δ ∧ ((M i).P s b s : ℝ) = 1 - δ := by
    intro i s b hs
    obtain ⟨h1, h2, -, -⟩ := hrow1₀ s b hs
    obtain ⟨h3, h4⟩ := hrow1 i s b hs
    exact ⟨h1, h2, h3, h4⟩
  -- equation (35): the reference occupancy bounds
  obtain ⟨hCrew, hCsum⟩ :=
    BanditAlgorithm.jao_two_class_reference_occupancy_bounds_two_valued δ hδ0 hδ ρ up down nav hρ01
      arm hinj harm0 M₀ hr₀ hrow0₀ hrow1₀ T π s₀
  set V : Fin m → ℝ := fun i =>
    ∫ h, (mdpVisitCount h T (arm i).1 (arm i).2 : ℝ)
      ∂(mdpMeasure M₀ (mdpStateDirac s₀) π T) with hV
  set R : Fin m → ℝ := fun i =>
    ∫ h, mdpRegret (M i) T h ∂(mdpMeasure (M i) (mdpStateDirac s₀) π T) with hR
  have hV0 : ∀ i, 0 ≤ V i := by
    intro i; exact integral_nonneg fun h => by positivity
  have hRbound : ∀ i : Fin m,
      (T : ℝ) * ((δ + ε) / (2 * δ + ε)) - (T : ℝ) + ((T : ℝ) / 2 - 1 / (2 * δ))
        - (ε / δ) * (V i + (T : ℝ) / 2 * (ε / Real.sqrt δ) * Real.sqrt (2 * V i))
        ≤ R i := by
    intro i
    have hgain :=
      BanditAlgorithm.jao_two_class_gadget_optimal_gain_ge δ ε hδ0 hδ hε0 hεδ
        ρ up down nav (arm i).1 (arm i).2 (M i) (harm0 i) (hfix i) (hud i)
        (hrM i) (hrow0' i) (hrow1' i)
    have heq34 :=
      BanditAlgorithm.jao_two_class_reward_le_reference_plus_planted_plays_two_valued δ ε hδ0 hδ
        hε0 hεδ ρ up down nav hρ01 (arm i).1 (arm i).2 (M i) M₀ (harm0 i)
        (hrM i) (hrow0' i) (hrow1' i) hr₀ hrow0₀ hrow1₀ T π s₀
    have hlem13 :=
      BanditAlgorithm.jao_two_class_planted_plays_change_of_measure_two_valued δ ε hδ0 hδ
        hε0 hεδ ρ up down nav hρ01 (arm i).1 (arm i).2 (M i) M₀ (harm0 i)
        (hrM i) (hrow0' i) (hrow1' i) hr₀ hrow0₀ hrow1₀ T π s₀
    have hsplit : R i = (T : ℝ) * mdpOptimalGain (M i)
        - ∫ h, mdpTrajectoryReward (M i) h
            ∂(mdpMeasure (M i) (mdpStateDirac s₀) π T) := by
      simp only [hR, mdpRegret]
      rw [integral_sub Integrable.of_finite Integrable.of_finite]
      simp
    have hgain' : (T : ℝ) * ((δ + ε) / (2 * δ + ε))
        ≤ (T : ℝ) * mdpOptimalGain (M i) :=
      mul_le_mul_of_nonneg_left hgain hT0.le
    -- the change-of-measure bound, scaled by `ε/(2δ) ≤ ε/δ`
    have hbr : 0 ≤ V i + (T : ℝ) / 2 * (ε / Real.sqrt δ) * Real.sqrt (2 * V i) := by
      have : (0 : ℝ) ≤ (T : ℝ) / 2 * (ε / Real.sqrt δ) * Real.sqrt (2 * V i) := by
        positivity
      linarith [hV0 i]
    have hscale : (ε / (2 * δ))
        * ∫ h, (mdpVisitCount h T (arm i).1 (arm i).2 : ℝ)
            ∂(mdpMeasure (M i) (mdpStateDirac s₀) π T)
        ≤ (ε / δ) * (V i + (T : ℝ) / 2 * (ε / Real.sqrt δ) * Real.sqrt (2 * V i)) := by
      have h1 : (0 : ℝ) < ε / (2 * δ) := by positivity
      have h2 : (ε / (2 * δ)) ≤ ε / δ := by
        rw [div_le_div_iff₀ (by positivity) hδ0]; nlinarith
      calc (ε / (2 * δ))
            * ∫ h, (mdpVisitCount h T (arm i).1 (arm i).2 : ℝ)
                ∂(mdpMeasure (M i) (mdpStateDirac s₀) π T)
          ≤ (ε / (2 * δ))
              * (V i + (T : ℝ) / 2 * (ε / Real.sqrt δ) * Real.sqrt (2 * V i)) :=
            mul_le_mul_of_nonneg_left hlem13 h1.le
        _ ≤ (ε / δ) * (V i + (T : ℝ) / 2 * (ε / Real.sqrt δ) * Real.sqrt (2 * V i)) :=
            mul_le_mul_of_nonneg_right h2 hbr
    rw [hsplit]
    linarith
  obtain ⟨i, hi⟩ :=
    BanditAlgorithm.jao_collapsed_bandit_regret_arithmetic m hm δ ε hδ0 hδ T hT hεdef
      V R hV0 hCsum hRbound
  exact ⟨i, hi⟩
