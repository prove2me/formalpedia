-- Prove2me | solution 1 for BidPriceControl.Asymptotic.fixed_bid_price_asymptotically_optimal
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T09:59:50.256428+00:00
-- url     : https://prove2.me/submissions/d5259534-80ed-47cd-9ec5-463e60f795be

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model
import Theorems.Thm_BidPriceControl_Asymptotic_scaled_optimum_le
import Theorems.Thm_BidPriceControl_Asymptotic_explicit_lower_bound

open MeasureTheory ProbabilityTheory

namespace Aux_BPC_main
open BidPriceControl.Asymptotic

lemma optValue_nonneg {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ)) :
    ∀ t (y : Fin m → ℕ), 0 ≤ optValue A F t y := by
  intro t
  induction t with
  | zero => intro y; simp [optValue]
  | succ t ih =>
    intro y
    simp only [optValue]
    apply integral_nonneg
    intro r
    exact le_trans (ih y) ((Finset.le_fold_max _).mpr (Or.inl le_rfl))

lemma bidSum_nonneg {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (hμ : 0 ≤ μ) (j : Fin n) :
    0 ≤ bidSum A μ j := by
  unfold bidSum
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hμ i) (Nat.cast_nonneg _)

lemma heuristicRun_nonneg {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (hμ : 0 ≤ μ) :
    ∀ (l : List (Fin n → ℝ)) (y : Fin m → ℕ), 0 ≤ heuristicRun A μ l y := by
  intro l
  induction l with
  | nil => intro y; simp [heuristicRun]
  | cons r rs ih =>
    intro y
    simp only [heuristicRun]
    split_ifs with h
    · have hm : (acceptSet A μ y r).min' h ∈ acceptSet A μ y r := Finset.min'_mem _ h
      generalize (acceptSet A μ y r).min' h = j at hm ⊢
      rw [acceptSet, Finset.mem_filter] at hm
      have := bidSum_nonneg A μ hμ j
      have := ih (y - column A j)
      linarith [hm.2.1]
    · exact ih y

end Aux_BPC_main

open BidPriceControl.Asymptotic in
theorem solution {m n : ℕ} (A : Fin m → Fin n → ℕ)
    (F : ℕ → Measure (Fin n → ℝ)) (k : ℕ) (x : Fin m → ℕ)
    (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t))
    (C : ℝ) (hC : ∀ t ∈ Finset.Icc 1 k, ∀ᵐ r ∂(F t), ∀ j, r j ≤ C)
    (μstar : Fin m → ℝ) (hmin : IsRelaxedMinimizer A F k x μstar) :
    ∃ K : ℝ, ∀ θ : ℕ, 1 ≤ θ →
      (1 - K / Real.sqrt (θ : ℝ)) * optValue A (scaledLaw F θ) (θ * k) (θ • x)
        ≤ heuristicValue A (scaledLaw F θ) (θ * k) (θ • x) μstar := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ,
      c = C / 2 * ∑ i, Real.sqrt (∑ t ∈ Finset.Icc 1 k, ∑ j, indicatorVar A F μstar i t j) :=
    ⟨_, rfl⟩
  set v : ℝ := relaxedValue A F k x μstar with hv
  refine ⟨if 0 < v then max c 0 / v else 0, ?_⟩
  intro θ hθ
  have hJ := scaled_optimum_le A F k x hF μstar hmin θ hθ
  have hH := explicit_lower_bound A F k x hF C hC μstar hmin θ hθ
  have J0 := Aux_BPC_main.optValue_nonneg A (scaledLaw F θ) (θ * k) (θ • x)
  have H0 : 0 ≤ heuristicValue A (scaledLaw F θ) (θ * k) (θ • x) μstar := by
    unfold heuristicValue
    exact integral_nonneg fun ω => Aux_BPC_main.heuristicRun_nonneg A μstar hmin.1 _ _
  set J := optValue A (scaledLaw F θ) (θ * k) (θ • x)
  set H := heuristicValue A (scaledLaw F θ) (θ * k) (θ • x) μstar
  have hθr : (1 : ℝ) ≤ θ := by exact_mod_cast hθ
  set s := Real.sqrt (θ : ℝ) with hs
  have s1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hθr
  have ss : s * s = θ := Real.mul_self_sqrt (by linarith)
  have s0 : 0 < s := by linarith
  split_ifs with hvpos
  · set K := max c 0 / v
    have hKv : K * v = max c 0 := div_mul_cancel₀ _ (ne_of_gt hvpos)
    by_cases hK : 0 ≤ 1 - K / s
    · calc (1 - K / s) * J ≤ (1 - K / s) * (θ * v) := mul_le_mul_of_nonneg_left hJ hK
        _ = θ * v - max c 0 * s := by
            rw [← hKv, ← ss]; field_simp
        _ ≤ θ * v - c * s := by nlinarith [le_max_left c 0]
        _ = θ * v - C / 2 * s *
              ∑ i, Real.sqrt (∑ t ∈ Finset.Icc 1 k, ∑ j, indicatorVar A F μstar i t j) := by
            rw [hc]; ring
        _ ≤ H := hH
    · push Not at hK
      nlinarith
  · push Not at hvpos
    simp only [zero_div, sub_zero, one_mul]
    nlinarith
