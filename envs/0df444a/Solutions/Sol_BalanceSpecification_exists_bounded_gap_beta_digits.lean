-- Prove2me | solution 1 for BalanceSpecification.exists_bounded_gap_beta_digits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:51.889683+00:00
-- url     : https://prove2.me/submissions/e8d9f805-3b2a-470d-b21b-b877660f5c8e

module
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyRealization
public import Theorems.Thm_BalanceSpecification_betaDigit_zero_or_one
public import Theorems.Thm_BalanceSpecification_betaDigit_bounded_zero_runs
public import Theorems.Thm_BalanceSpecification_hasSum_betaDigit

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {β x : ℝ} (hβ1 : 1 < β) (hβ2 : β < 2)
    (hx : 0 < x) (hxB : x < 1 / (β - 1)) :
    ∃ d : ℕ → ℝ, (∀ n, d n = 0 ∨ d n = 1) ∧
      (∃ N : ℕ, ∀ t : ℕ, ∃ s : ℕ, t ≤ s ∧ s ≤ t + N ∧ d s = 1) ∧
      HasSum (fun n : ℕ => d n / β ^ (n + 1)) x := by
  let B := 1 / (β - 1)
  have hden : 0 < β - 1 := sub_pos.mpr hβ1
  have hB : 1 < B := by
    change 1 < 1 / (β - 1)
    apply (lt_div_iff₀ hden).mpr
    linarith only [hβ2]
  let a := min (x / 2) ((B - 1) / 2)
  have ha : 0 < a := lt_min (div_pos hx (by norm_num))
    (div_pos (sub_pos.mpr hB) (by norm_num))
  have hax : a ≤ x := by
    have H : a ≤ x / 2 := min_le_left _ _
    linarith only [H, hx]
  let R := max x (1 + a)
  have hxR : x ≤ R := le_max_left _ _
  have haR : 1 + a ≤ R := le_max_right _ _
  have hRlt : R < B := by
    apply max_lt_iff.mpr
    refine ⟨hxB, ?_⟩
    have H : a ≤ (B - 1) / 2 := min_le_right _ _
    linarith only [H, hB]
  have hR : (β - 1) * R ≤ 1 := by
    have H := mul_lt_mul_of_pos_left hRlt hden
    have he : (β - 1) * B = 1 := by
      dsimp only [B]
      field_simp
    rw [he] at H
    exact H.le
  exact ⟨betaDigit β a x, betaDigit_zero_or_one β a x,
    betaDigit_bounded_zero_runs hβ1 ha hax hxR haR hR,
    hasSum_betaDigit hβ1 ha hax hxR haR hR⟩
end BalanceSpecification
