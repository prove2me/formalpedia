-- Prove2me | solution 1 for ExploreFirst.Relative.pinsker_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:09:14.39978+00:00
-- url     : https://prove2.me/submissions/1c5fa336-8cc5-4442-80e7-c6cbe3423c30

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_ExploreFirst_Relative_Setting
import Theorems.Thm_ExploreFirst_Relative_equation_12
import Theorems.Thm_ExploreFirst_Relative_jensen_ratio
import Theorems.Thm_ExploreFirst_Absolute_lemma_6

open MeasureTheory ProbabilityTheory BanditAlgorithm

theorem solution {K : ℕ} (𝒟 : Set (Measure ℝ)) (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟)
    (π : BanditPolicy K) (hπ : ExploreFirst.Relative.IsPairwiseSymmetric 𝒟 π)
    (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (a a' : Fin K) (ha : 0 < banditGap ν a) (ha' : a' ∈ ExploreFirst.Asymptotic.optimalArms ν)
    (ν' : StochasticBandit K) (hν'_ne : ∀ k, k ≠ a → ν'.P k = ν.P k) (hν'_a : ν'.P a = ν.P a')
    (hKL : InformationTheory.klDiv (ν.P a) (ν'.P a) ≠ ⊤)
    (T : ℕ) (hT : 1 ≤ T)
    (hpulls : ExploreFirst.FundIneq.expPulls ν π T a ≤ (T : ℝ) / K)
    (hr : ∫ h, ExploreFirst.Relative.pullsPlus a h / ExploreFirst.Relative.pullsPlus a' h ∂(banditMeasure ν π T) ≤ 1) :
    1 / 2 - Real.sqrt ((T : ℝ) * (InformationTheory.klDiv (ν.P a) (ν'.P a)).toReal / (2 * K)) ≤
      (∫ h, ExploreFirst.Relative.pullsPlus a h / ExploreFirst.Relative.pullsPlus a' h ∂(banditMeasure ν π T)) /
        (1 + ∫ h, ExploreFirst.Relative.pullsPlus a h / ExploreFirst.Relative.pullsPlus a' h ∂(banditMeasure ν π T)) := by
  set E := ∫ h, ExploreFirst.Relative.pullsPlus a h /
    (ExploreFirst.Relative.pullsPlus a h + ExploreFirst.Relative.pullsPlus a' h) ∂(banditMeasure ν π T)
    with hE
  set r := ∫ h, ExploreFirst.Relative.pullsPlus a h / ExploreFirst.Relative.pullsPlus a' h
    ∂(banditMeasure ν π T) with hrdef
  set L := (InformationTheory.klDiv (ν.P a) (ν'.P a)).toReal with hL
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  -- Jensen: E ≤ r / (1 + r)
  have hjen := ExploreFirst.Relative.jensen_ratio π ν a a' T
  have hEr : E ≤ r / (1 + r) := hjen.1.trans_le hjen.2
  -- E ≥ 0
  have hE0 : 0 ≤ E := by
    apply integral_nonneg
    intro h
    have h1 : (1 : ℝ) ≤ ExploreFirst.Relative.pullsPlus a h := le_max_right _ _
    have h2 : (1 : ℝ) ≤ ExploreFirst.Relative.pullsPlus a' h := le_max_right _ _
    positivity
  have hsq0 : 0 ≤ Real.sqrt ((T : ℝ) * L / (2 * K)) := Real.sqrt_nonneg _
  by_cases hhalf : 1 / 2 ≤ E
  · linarith
  push_neg at hhalf
  -- (12)
  have h12 := ExploreFirst.Relative.equation_12 𝒟 h𝒟 π hπ ν hν a a' ha ha' ν' hν'_ne hν'_a T hT
  rw [← hE] at h12
  have hKLeq : InformationTheory.klDiv (ν.P a) (ν'.P a) = ENNReal.ofReal L := by
    rw [hL, ENNReal.ofReal_toReal hKL]
  have hTK0 : (0 : ℝ) ≤ (T : ℝ) / K := by positivity
  have h12' : ExploreFirst.FundIneq.klBer E (1 / 2) ≤ ENNReal.ofReal ((T : ℝ) / K * L) := by
    refine h12.trans ?_
    rw [hKLeq, ENNReal.ofReal_mul hTK0]
    gcongr
  -- Pinsker (Lemma 6 with q = 1/2)
  have h6 := (ExploreFirst.Absolute.lemma_6 E (1 / 2) hE0 hhalf (by norm_num)).1
  have hS : sSup ((fun x : ℝ => x * (1 - x)) '' Set.Icc E (1 / 2)) = 1 / 4 := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨1 / 2, ⟨hhalf.le, le_rfl⟩, by norm_num⟩, ?_⟩
    rintro y ⟨x, _, rfl⟩
    nlinarith [sq_nonneg (x - 1 / 2)]
  rw [hS] at h6
  have hpin := h6.trans h12'
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hpin
  have hsq : (1 / 2 - E) ^ 2 ≤ (T : ℝ) * L / (2 * K) := by
    have : (T : ℝ) * L / (2 * K) = ((T : ℝ) / K * L) / 2 := by ring
    rw [this]
    have : (E - 1 / 2) ^ 2 / (2 * (1 / 4)) = 2 * (1 / 2 - E) ^ 2 := by ring
    rw [this] at hpin
    linarith
  have hroot : 1 / 2 - E ≤ Real.sqrt ((T : ℝ) * L / (2 * K)) :=
    Real.le_sqrt_of_sq_le hsq
  linarith
