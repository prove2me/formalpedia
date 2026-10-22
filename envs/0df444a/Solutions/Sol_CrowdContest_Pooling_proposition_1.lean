-- Prove2me | solution 1 for CrowdContest.Pooling.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T00:06:24.820675+00:00
-- url     : https://prove2.me/submissions/97633bd5-5ab1-4464-889a-fa8e25265740

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_CrowdContest_Pooling_Density
import Definitions.Def_CrowdContest_Pooling_Setting
import Theorems.Thm_CrowdContest_Pooling_lemma_4
import Theorems.Thm_CrowdContest_Pooling_lemma_1
import Theorems.Thm_CrowdContest_Pooling_eq_A_6
import Theorems.Thm_CrowdContest_Pooling_concave_deriv_inverse

open MeasureTheory

open CrowdContest.Pooling

/-- The marginal cost of a cost function is strictly increasing on `(0, ∞)`. -/
lemma CCP_prop1_derivC_strictMono (C : ℝ → ℝ) (hC : IsCost C) :
    StrictMonoOn (deriv C) (Set.Ioi 0) := by
  obtain ⟨_, hCd, hpos⟩ := hC
  have hdiff : DifferentiableOn ℝ (deriv C) (Set.Ioi 0) :=
    (hCd.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).differentiableOn (by norm_num)
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) hdiff.continuousOn
  intro x hx
  rw [interior_Ioi] at hx
  exact (hpos x hx).2

lemma CCP_prop1_continuousOn (C : ℝ → ℝ) (hC : IsCost C) :
    ContinuousOn (deriv C) (Set.Ioi 0) := by
  obtain ⟨_, hCd, _⟩ := hC
  exact (hCd.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).continuousOn

theorem solution (n : ℕ) (hn : 2 ≤ n) (ψ : ℝ → ℝ) (hψ : IsSymLogConcaveDensity ψ) :
    (AssumptionR ψ → 0 < deltaXi ψ n) ∧
    ∀ (A w : ℝ) (C₁ C₂ : ℝ → ℝ) (e₁ e₂ s₁ s₂ : ℝ),
      0 < A → 0 < w → w < 1 → IsCost C₁ → IsCost C₂ →
      IsSymEqSub ψ n (w * A) C₁ e₁ → 0 < e₁ →
      IsSymEqSub ψ n ((1 - w) * A) C₂ e₂ → 0 < e₂ →
      IsSymEqJoint ψ n A C₁ C₂ s₁ s₂ → 0 < s₁ → 0 < s₂ →
      (max (w * hFun ψ n) ((1 - w) * hFun ψ n) < hFun (convDensity ψ) n →
          e₁ + e₂ - (s₁ + s₂) < 0) ∧
      (w = 1 / 2 → hFun ψ n / 2 < hFun (convDensity ψ) n →
          e₁ + e₂ - (s₁ + s₂) < 0) ∧
      (C₁ = C₂ → ConvexOn ℝ (Set.Ioi 0) (deriv C₁) → hFun ψ n / 2 < hFun (convDensity ψ) n →
          e₁ + e₂ - (s₁ + s₂) < 0) := by
  refine ⟨fun hR => ?_, ?_⟩
  · have := lemma_4 n hn ψ hψ hR
    unfold deltaXi
    linarith
  intro A w C₁ C₂ e₁ e₂ s₁ s₂ hA hw0 hw1 hC₁ hC₂ he₁ he₁0 he₂ he₂0 hs hs₁ hs₂
  have L1 := (lemma_1 n hn ψ hψ (w * A) C₁ hC₁ e₁ he₁ he₁0).1
  have L2 := (lemma_1 n hn ψ hψ ((1 - w) * A) C₂ hC₂ e₂ he₂ he₂0).1
  obtain ⟨J1, J2⟩ := eq_A_6 n hn ψ hψ A C₁ C₂ hC₁ hC₂ s₁ s₂ hs hs₁ hs₂
  have M1 := CCP_prop1_derivC_strictMono C₁ hC₁
  have M2 := CCP_prop1_derivC_strictMono C₂ hC₂
  set h := hFun ψ n
  set h0 := hFun (convDensity ψ) n
  -- the main case: from `h° > max {w h, (1-w) h}`
  have main : max (w * h) ((1 - w) * h) < h0 → e₁ + e₂ - (s₁ + s₂) < 0 := by
    intro hmax
    have h1 : w * h < h0 := lt_of_le_of_lt (le_max_left _ _) hmax
    have h2 : (1 - w) * h < h0 := lt_of_le_of_lt (le_max_right _ _) hmax
    have d1 : deriv C₁ e₁ < deriv C₁ s₁ := by
      rw [L1, J1]; nlinarith
    have d2 : deriv C₂ e₂ < deriv C₂ s₂ := by
      rw [L2, J2]; nlinarith
    have k1 : e₁ < s₁ := (M1.lt_iff_lt (Set.mem_Ioi.2 he₁0) (Set.mem_Ioi.2 hs₁)).1 d1
    have k2 : e₂ < s₂ := (M2.lt_iff_lt (Set.mem_Ioi.2 he₂0) (Set.mem_Ioi.2 hs₂)).1 d2
    linarith
  refine ⟨main, ?_, ?_⟩
  · intro hw hh
    apply main
    subst hw
    have : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
    rw [this, max_self]
    linarith
  · intro hCC hconv hh
    subst hCC
    -- find `c` with `C'(c) = (C'(e₁) + C'(e₂)) / 2` by the intermediate value theorem
    have hcont := CCP_prop1_continuousOn C₁ hC₁
    have hsub : Set.uIcc e₁ e₂ ⊆ Set.Ioi 0 := by
      intro x hx
      rcases Set.mem_uIcc.1 hx with hx | hx
      · exact lt_of_lt_of_le he₁0 hx.1
      · exact lt_of_lt_of_le he₂0 hx.1
    have hivt := intermediate_value_uIcc (hcont.mono hsub)
    have hmem : (deriv C₁ e₁ + deriv C₁ e₂) / 2 ∈ Set.uIcc (deriv C₁ e₁) (deriv C₁ e₂) := by
      rcases le_total (deriv C₁ e₁) (deriv C₁ e₂) with hle | hle
      · exact Set.mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩)
      · exact Set.mem_uIcc.2 (Or.inr ⟨by linarith, by linarith⟩)
    obtain ⟨c, hc, hcval⟩ := hivt hmem
    have hc0 : 0 < c := hsub hc
    have hab := concave_deriv_inverse C₁ hC₁ hconv e₁ e₂ c he₁0 he₂0 hc0 hcval
    have hcv : deriv C₁ c = A * h / 2 := by
      rw [hcval, L1, L2]; ring
    have d1 : deriv C₁ c < deriv C₁ s₁ := by
      rw [hcv, J1]; nlinarith
    have d2 : deriv C₁ c < deriv C₁ s₂ := by
      rw [hcv, J2]; nlinarith
    have k1 : c < s₁ := (M1.lt_iff_lt (Set.mem_Ioi.2 hc0) (Set.mem_Ioi.2 hs₁)).1 d1
    have k2 : c < s₂ := (M1.lt_iff_lt (Set.mem_Ioi.2 hc0) (Set.mem_Ioi.2 hs₂)).1 d2
    linarith
