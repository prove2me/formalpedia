-- Prove2me | solution 1 for ExploreFirst.Relative.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:09:15.318511+00:00
-- url     : https://prove2.me/submissions/d055a6c2-ffda-4793-9814-c013dcf280dc

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_ExploreFirst_Relative_Setting
import Theorems.Thm_ExploreFirst_Relative_pinsker_step

open MeasureTheory ProbabilityTheory BanditAlgorithm

theorem solution {K : ℕ} (𝒟 : Set (Measure ℝ)) (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟)
    (π : BanditPolicy K) (hπ : ExploreFirst.Relative.IsPairwiseSymmetric 𝒟 π)
    (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (a a' : Fin K) (ha : 0 < banditGap ν a) (ha' : a' ∈ ExploreFirst.Asymptotic.optimalArms ν)
    (hKL : InformationTheory.klDiv (ν.P a) (ν.P a') ≠ ⊤)
    (T : ℕ) (hT : 1 ≤ T) :
    (T : ℝ) / K ≤ ExploreFirst.FundIneq.expPulls ν π T a ∨
      1 - 2 * Real.sqrt (2 * (T : ℝ) * (InformationTheory.klDiv (ν.P a) (ν.P a')).toReal / K) ≤
        ∫ h, max (armPullCount a h : ℝ) 1 / max (armPullCount a' h : ℝ) 1
          ∂(banditMeasure ν π T) := by
  classical
  by_cases hpulls : (T : ℝ) / K ≤ ExploreFirst.FundIneq.expPulls ν π T a
  · exact Or.inl hpulls
  right
  push_neg at hpulls
  -- the alternative problem ν': arm `a` receives the law of the optimal arm `a'`
  let ν' : StochasticBandit K :=
    ⟨fun k => if k = a then ν.P a' else ν.P k, fun k => by
      by_cases hk : k = a
      · simp only [hk, if_true]; infer_instance
      · simp only [hk, if_false]; infer_instance⟩
  have hν'_ne : ∀ k, k ≠ a → ν'.P k = ν.P k := fun k hk => by simp [ν', hk]
  have hν'_a : ν'.P a = ν.P a' := by simp [ν']
  set r := ∫ h, max (armPullCount a h : ℝ) 1 / max (armPullCount a' h : ℝ) 1
    ∂(banditMeasure ν π T) with hrdef
  set L := (InformationTheory.klDiv (ν.P a) (ν.P a')).toReal with hL
  have hsq0 : 0 ≤ Real.sqrt (2 * (T : ℝ) * L / K) := Real.sqrt_nonneg _
  by_cases hr : 1 < r
  · linarith
  push_neg at hr
  have hr0 : 0 ≤ r := by
    apply integral_nonneg
    intro h
    have h1 : (1 : ℝ) ≤ max (armPullCount a h : ℝ) 1 := le_max_right _ _
    have h2 : (1 : ℝ) ≤ max (armPullCount a' h : ℝ) 1 := le_max_right _ _
    positivity
  have hKL' : InformationTheory.klDiv (ν.P a) (ν'.P a) ≠ ⊤ := by rw [hν'_a]; exact hKL
  have hstep := ExploreFirst.Relative.pinsker_step 𝒟 h𝒟 π hπ ν hν a a' ha ha' ν' hν'_ne hν'_a
    hKL' T hT hpulls.le hr
  rw [hν'_a] at hstep
  change 1 / 2 - Real.sqrt ((T : ℝ) * L / (2 * K)) ≤ r / (1 + r) at hstep
  -- r / (1 + r) ≤ (1 + r) / 4
  have hup : r / (1 + r) ≤ (1 + r) / 4 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg (1 - r)]
  have hs : Real.sqrt (2 * (T : ℝ) * L / K) = 2 * Real.sqrt ((T : ℝ) * L / (2 * K)) := by
    have : 2 * (T : ℝ) * L / K = 2 ^ 2 * ((T : ℝ) * L / (2 * K)) := by ring
    rw [this, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [hs]
  linarith
