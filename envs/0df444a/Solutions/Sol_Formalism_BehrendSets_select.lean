-- Prove2me | solution 1 for Formalism.BehrendSets.select
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:23:31.644161+00:00
-- url     : https://prove2.me/submissions/2cf0fa47-f1e6-4af2-ba6e-f033b1143a48

import Mathlib
import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_Select
import Theorems.Thm_Formalism_BehrendSets_Select_wt_nonneg
import Theorems.Thm_Formalism_BehrendSets_Select_moments
import Theorems.Thm_Formalism_BehrendSets_Select_variance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.BehrendSets
open Formalism.BehrendSets.Select
namespace Formalism.BehrendSets
theorem _root_.solution : Select := by
  intro α _ X δ lam Y hδ0 hδ1 hY hlam hvar
  classical
  obtain ⟨h0, -, -⟩ := moments X δ
  have wnn : ∀ T, 0 ≤ wt X δ T := wt_nonneg X hδ0 hδ1
  set E := expect X δ Y with hEdef
  have hEs : ∑ T ∈ X.powerset, wt X δ T * Y T = E := rfl
  have hE : 0 ≤ E := Finset.sum_nonneg (fun T _ => mul_nonneg (wnn T) (hY T))
  by_contra hcon
  push Not at hcon

  have w1 : ∑ T ∈ X.powerset,
      (if lam < |(T.card : ℝ) - δ * X.card| then wt X δ T else 0) < 1 / 2 := by
    have hl2 : 0 < lam ^ 2 := by positivity
    calc ∑ T ∈ X.powerset, (if lam < |(T.card : ℝ) - δ * X.card| then wt X δ T else 0)
        ≤ ∑ T ∈ X.powerset, wt X δ T * ((T.card : ℝ) - δ * X.card) ^ 2 / lam ^ 2 := by
          apply Finset.sum_le_sum
          intro T _
          split_ifs with hp
          · have hsq : lam ^ 2 < ((T.card : ℝ) - δ * X.card) ^ 2 := by
              rw [← sq_abs ((T.card : ℝ) - δ * X.card)]
              exact pow_lt_pow_left₀ hp hlam.le (by norm_num)
            rw [mul_div_assoc]
            have : 1 ≤ ((T.card : ℝ) - δ * X.card) ^ 2 / lam ^ 2 := by
              rw [one_le_div hl2]
              exact hsq.le
            nlinarith [wnn T]
          · exact div_nonneg (mul_nonneg (wnn T) (sq_nonneg _)) hl2.le
      _ = δ * X.card * (1 - δ) / lam ^ 2 := by
          rw [← Finset.sum_div, variance]
      _ < 1 / 2 := by
          rw [div_lt_iff₀ hl2]
          linarith

  have w2 : ∑ T ∈ X.powerset, (if 2 * E < Y T then wt X δ T else 0) ≤ 1 / 2 := by
    rcases hE.lt_or_eq with hEpos | hE0
    · calc ∑ T ∈ X.powerset, (if 2 * E < Y T then wt X δ T else 0)
          ≤ ∑ T ∈ X.powerset, wt X δ T * Y T / (2 * E) := by
            apply Finset.sum_le_sum
            intro T _
            have h2E : 0 < 2 * E := by linarith
            split_ifs with hp
            · rw [mul_div_assoc]
              have : 1 ≤ Y T / (2 * E) := by
                rw [one_le_div h2E]
                exact hp.le
              nlinarith [wnn T]
            · exact div_nonneg (mul_nonneg (wnn T) (hY T)) h2E.le
        _ = E / (2 * E) := by
            rw [← Finset.sum_div, hEs]
        _ = 1 / 2 := by
            field_simp
    · have hz : ∀ T ∈ X.powerset, wt X δ T * Y T = 0 := by
        have hsum : ∑ T ∈ X.powerset, wt X δ T * Y T = 0 := hEs.trans hE0.symm
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun T _ => mul_nonneg (wnn T) (hY T))).1 hsum
      have : ∑ T ∈ X.powerset, (if 2 * E < Y T then wt X δ T else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro T hT
        split_ifs with hp
        · rw [← hE0] at hp
          have hYp : 0 < Y T := by linarith
          rcases mul_eq_zero.1 (hz T hT) with h | h
          · exact h
          · linarith
        · rfl
      rw [this]
      norm_num

  have cover : ∑ T ∈ X.powerset, wt X δ T * 1 ≤
      ∑ T ∈ X.powerset, (if lam < |(T.card : ℝ) - δ * X.card| then wt X δ T else 0) +
      ∑ T ∈ X.powerset, (if 2 * E < Y T then wt X δ T else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro T hT
    have hTX : T ⊆ X := Finset.mem_powerset.1 hT
    by_cases hp : lam < |(T.card : ℝ) - δ * X.card|
    · rw [if_pos hp, mul_one]
      split_ifs
      · linarith [wnn T]
      · linarith
    · rw [if_neg hp, mul_one, zero_add]
      have hq : 2 * E < Y T := hcon T hTX (not_lt.1 hp)
      rw [if_pos hq]
  rw [h0] at cover
  linarith
end Formalism.BehrendSets
