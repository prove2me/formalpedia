-- Prove2me | solution 1 for BesbesZeevi.Nonparametric.step4_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T14:59:56.79459+00:00
-- url     : https://prove2.me/submissions/0e7d41ab-6b23-4cdc-b0c4-dfe7bdfddf6e

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_BesbesZeevi_Nonparametric_Model
import Definitions.Def_BesbesZeevi_Nonparametric_Algorithm
import Theorems.Thm_BesbesZeevi_Nonparametric_case1_revenue_ratio_A11
import Theorems.Thm_BesbesZeevi_Nonparametric_case2_revenue_ratio_A15
set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProcessingNetworks.Stability

namespace BesbesZeevi.Nonparametric

theorem s4_grid_nonneg (P : PriceSet) (κ j : ℕ) : 0 ≤ gridPrice P κ j := by
  unfold gridPrice
  have h1 := P.pl_pos
  have h2 := P.pl_lt_pu
  have : 0 ≤ (j : ℝ) * (P.pu - P.pl) / (κ : ℝ) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (Nat.cast_nonneg _)
  linarith

theorem s4_learn_mono (P : PriceSet) (lam : ℝ → ℝ) (hlam : ∀ p, 0 ≤ lam p) (n : ℕ) (τ : ℝ)
    (hτ : 0 ≤ τ) (κ j : ℕ) :
    learnIntensity P lam n τ κ j ≤ learnIntensity P lam n τ κ (j + 1) := by
  unfold learnIntensity
  rw [Finset.sum_range_succ]
  have : 0 ≤ (n : ℝ) * lam (gridPrice P κ j) * (τ / (κ : ℝ)) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hlam _)) (div_nonneg hτ (Nat.cast_nonneg _))
  linarith

theorem s4_revenue_nonneg (P : PriceSet) (L : DemandClass) (x T : ℝ)
    (c c' : ℝ) (τ : ℕ → ℝ) (κ : ℕ → ℕ) (htune : Tuning T c c' τ κ)
    {Ω : Type*} [MeasureSpace Ω] (N : ℝ → Ω → ℕ) (hN : IsPoissonProcess N 1)
    (n : ℕ) (hn : 1 ≤ n) (lam : ℝ → ℝ) (hlam : L.Mem P lam) (ω : Ω) :
    0 ≤ revenue P lam x T n (τ n) (κ n) N ω := by
  have hmono := hN.2.1 ω
  have hτ0 : 0 ≤ τ n := (htune.tau_pos n hn).le
  have hτT := htune.tau_le n hn
  have hlam0 := hlam.nonneg
  have hphat : 0 ≤ phat P lam x T n (τ n) (κ n) N ω := by
    unfold phat phatU
    exact le_trans (s4_grid_nonneg P _ _) (le_max_right _ _)
  unfold revenue
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (s4_grid_nonneg P _ _)
    have h1 := hmono (s4_learn_mono P lam hlam0 n (τ n) hτ0 (κ n) j)
    have h2 := min_le_min_right (salesCap n x) h1
    exact sub_nonneg.mpr (Nat.cast_le.mpr h2)
  · apply mul_nonneg hphat
    have hend : learnIntensity P lam n (τ n) (κ n) (κ n)
        ≤ endIntensity P lam x T n (τ n) (κ n) N ω := by
      unfold endIntensity
      have : 0 ≤ (n : ℝ) * lam (phat P lam x T n (τ n) (κ n) N ω) * (T - τ n) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hlam0 _)) (by linarith)
      linarith
    have h1 := hmono hend
    have h2 := min_le_min_right (salesCap n x) h1
    exact sub_nonneg.mpr (Nat.cast_le.mpr h2)

theorem s4_JDn_nonneg (P : PriceSet) (L : DemandClass) (lam : ℝ → ℝ) (hlam : L.Mem P lam)
    (x T : ℝ) (hx : 0 < x) (n : ℕ) : 0 ≤ JDn P lam x T n := by
  unfold JDn JD
  by_cases hb : BddAbove (pathRevenue (fun p => (n : ℝ) * lam p) T ''
      {p | FeasiblePath P (fun p => (n : ℝ) * lam p) ((n : ℝ) * x) T p})
  · apply le_csSup hb
    refine ⟨fun _ => P.pinf, ?_, ?_⟩
    · refine ⟨measurable_const, fun s _ => Or.inr rfl, ?_, ?_⟩
      · simp [hlam.off]
      · have hx' : 0 ≤ (n : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx.le
        simpa [hlam.off] using hx'
    · simp [pathRevenue, hlam.off]
  · rw [Real.sSup_of_not_bddAbove hb]

theorem s4_regret_le_one (P : PriceSet) (L : DemandClass) (x T : ℝ) (hx : 0 < x)
    (c c' : ℝ) (τ : ℕ → ℝ) (κ : ℕ → ℕ) (htune : Tuning T c c' τ κ)
    {Ω : Type*} [MeasureSpace Ω] (N : ℝ → Ω → ℕ) (hN : IsPoissonProcess N 1)
    (n : ℕ) (hn : 1 ≤ n) (lam : ℝ → ℝ) (hlam : L.Mem P lam) :
    regret P lam x T n (τ n) (κ n) N ≤ 1 := by
  unfold regret expectedRevenue
  have h1 : 0 ≤ ∫ ω, revenue P lam x T n (τ n) (κ n) N ω :=
    integral_nonneg (fun ω => s4_revenue_nonneg P L x T c c' τ κ htune N hN n hn lam hlam ω)
  have h2 := s4_JDn_nonneg P L lam hlam x T hx n
  have := div_nonneg h1 h2
  linarith

theorem s4_uSeq_nonneg (n : ℕ) (τ : ℝ) (κ : ℕ) : 0 ≤ uSeq n τ κ := by
  unfold uSeq
  exact mul_nonneg (Real.sqrt_nonneg _) (le_max_of_le_left (by positivity))

end BesbesZeevi.Nonparametric

section S4Solution

open BesbesZeevi.Nonparametric

theorem solution (P : PriceSet) (L : DemandClass) (x T : ℝ) (hx : 0 < x) (hT : 0 < T)
    (c c' : ℝ) (τ : ℕ → ℝ) (κ : ℕ → ℕ) (htune : Tuning T c c' τ κ) :
    ∃ C₁₂ : ℝ, 0 < C₁₂ ∧
      ∀ (Ω : Type*) [MeasureSpace Ω] (N : ℝ → Ω → ℕ), IsPoissonProcess N 1 →
      ∀ n : ℕ, 1 ≤ n → ∀ lam : ℝ → ℝ, L.Mem P lam →
        regret P lam x T n (τ n) (κ n) N ≤ C₁₂ * (uSeq n (τ n) (κ n) + τ n) := by
  obtain ⟨C8, hC8, h1⟩ := case1_revenue_ratio_A11 P L x T hx hT c c' τ κ htune
  obtain ⟨C11, hC11, h2⟩ := case2_revenue_ratio_A15 P L x T hx hT c c' τ κ htune
  have hm := L.m_pos
  have hM := L.M_pos
  have hTp : 0 < min T (x / L.M) := lt_min hT (div_pos hx hM)
  have hτ1 := htune.tau_pos 1 le_rfl
  set A := C8 / (L.m * min T (x / L.M)) with hA
  set B := C11 / (P.pu * x) with hB
  have hpu : 0 < P.pu := lt_trans P.pl_pos P.pl_lt_pu
  have hA0 : 0 < A := by positivity
  have hB0 : 0 < B := by positivity
  refine ⟨max (max A B) (1 / τ 1), lt_of_lt_of_le hA0 ((le_max_left _ _).trans (le_max_left _ _)),
    fun Ω _ N hN n hn lam hlam => ?_⟩
  have hu := s4_uSeq_nonneg n (τ n) (κ n)
  have hτn := htune.tau_pos n hn
  have hsum : 0 ≤ uSeq n (τ n) (κ n) + τ n := by linarith
  have hAC : A ≤ max (max A B) (1 / τ 1) := (le_max_left _ _).trans (le_max_left _ _)
  have hBC : B ≤ max (max A B) (1 / τ 1) := (le_max_right _ _).trans (le_max_left _ _)
  by_cases hcase : lam P.pu ≤ x / T
  · have := h1 Ω N hN lam hlam hcase n hn
    unfold regret
    calc 1 - expectedRevenue P lam x T n (τ n) (κ n) N / JDn P lam x T n
        ≤ A * (uSeq n (τ n) (κ n) + τ n) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hAC hsum
  · push_neg at hcase
    by_cases hn2 : 2 ≤ n
    · have := h2 Ω N hN lam hlam hcase n hn2
      unfold regret
      calc 1 - expectedRevenue P lam x T n (τ n) (κ n) N / JDn P lam x T n
          ≤ B * uSeq n (τ n) (κ n) := by linarith
        _ ≤ B * (uSeq n (τ n) (κ n) + τ n) :=
            mul_le_mul_of_nonneg_left (by linarith) hB0.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hBC hsum
    · have hn1 : n = 1 := by omega
      subst hn1
      have h := s4_regret_le_one P L x T hx c c' τ κ htune N hN 1 le_rfl lam hlam
      calc regret P lam x T 1 (τ 1) (κ 1) N ≤ 1 := h
        _ = (1 / τ 1) * τ 1 := by field_simp
        _ ≤ (1 / τ 1) * (uSeq 1 (τ 1) (κ 1) + τ 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_right _ _)) hsum

end S4Solution
