-- Prove2me | solution 1 for BudgetFeasSubmod.Main.corollary_3_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:49:17.9686+00:00
-- url     : https://prove2.me/submissions/3d5c8e58-1945-41fa-81a1-a013b84ef338

import Mathlib
import Definitions.Def_BudgetFeasSubmod_Main_Model
import Theorems.Thm_BudgetFeasSubmod_Main_lemma_3_8

open BudgetFeasSubmod.Main Finset

theorem solution {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    (v : Finset A → ℝ) (alg1 : Finset A → (A → ℝ) → Finset A) (alg2 : Finset A → Finset A)
    (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2) (B : ℝ) (c : A → ℝ)
    (hv : IsValuation v) (h1 : IsKnapsackEApprox v B alg1) (h2 : IsUnconstrainedTwoApprox v alg2)
    (htb : IsArgmaxRule v tb) (hB : 0 < B) (hc : InDomain B c) :
    opt v c B univ ≤ 505 * expectedValue v alg1 alg2 tb B c := by
  have hv0 : ∀ S, 0 ≤ v S := hv.2.1
  set O := opt v c B univ with hO
  set M := v {istar v} with hM
  have hmax : ∀ i : A, v {i} ≤ M := by
    intro i
    have := (Classical.choose_spec
      (Finset.exists_max_image univ (fun i => v {i}) univ_nonempty)).2 i (mem_univ i)
    exact this
  set n := Fintype.card A
  set w := (1 - pcoin) / 2 ^ n with hw
  have hp : pcoin = 201 / 1000 := rfl
  have hw0 : 0 ≤ w := by rw [hw, hp]; positivity
  set F := fun A₁ : Finset A => v (sampleThenGreedy v alg1 alg2 tb beta B A₁ c)
  have hE : expectedValue v alg1 alg2 tb B c = pcoin * M + ∑ A₁ : Finset A, w * F A₁ := by
    unfold expectedValue
    rw [Fintype.sum_option]
    rfl
  have hsum0 : 0 ≤ ∑ A₁ : Finset A, w * F A₁ :=
    Finset.sum_nonneg fun A₁ _ => mul_nonneg hw0 (hv0 _)
  have hM0 : 0 ≤ M := hv0 _
  rw [hE, hp]
  by_cases hcase : ∃ i : A, O ≤ 101 * v {i}
  · obtain ⟨i, hi⟩ := hcase
    have := hmax i
    nlinarith
  · push Not at hcase
    have hopt : ∀ i : A, ((101 : ℕ) : ℝ) * v {i} < O := by
      intro i; have := hcase i; push_cast; linarith
    have key := lemma_3_8 v alg1 alg2 tb beta B c 101 hv h1 h2 htb
      (by unfold beta; norm_num) hB hc (by norm_num) hopt
    have he1 := Real.exp_one_lt_d9
    have he2 := Real.exp_one_gt_d9
    have hβ : beta = 9185 / 1000 := rfl
    have hfloor : ⌊(((101 : ℕ) : ℝ) - 1) / (4 * Real.exp 1 * beta)⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by rw [hβ]; positivity)]
      rw [hβ]
      constructor
      · rw [le_div_iff₀ (by positivity)]; push_cast; nlinarith
      · rw [div_lt_iff₀ (by positivity)]; push_cast; nlinarith
    rw [hfloor] at key
    have hmin : min ((((1 : ℕ) : ℝ)) * (((101 : ℕ) : ℝ) - 1) /
          (Real.exp 1 * (((1 : ℕ) : ℝ) + 1)))
        ((beta * (((101 : ℕ) : ℝ) - 1) - 8 * ((101 : ℕ) : ℝ)) / 6) = 50 / Real.exp 1 := by
      rw [min_eq_left]
      · push_cast; field_simp; ring
      · rw [hβ]; push_cast
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
    rw [hmin] at key
    set bound := 50 / Real.exp 1 * (1 / (4 * beta * ((101 : ℕ) : ℝ))) * O with hbound
    set G := univ.powerset.filter (fun A₁ : Finset A => bound ≤ F A₁) with hG
    have hO0 : 0 ≤ O := by
      have := hopt (istar v); have := hv0 {istar v}; push_cast at *; linarith
    have hb0 : 0 ≤ bound := by rw [hbound, hβ]; positivity
    have hGsum : (G.card : ℝ) * (w * bound) ≤ ∑ A₁ : Finset A, w * F A₁ := by
      calc (G.card : ℝ) * (w * bound) = ∑ A₁ ∈ G, w * bound := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ A₁ ∈ G, w * F A₁ := by
            apply Finset.sum_le_sum
            intro A₁ hA₁
            rw [hG, Finset.mem_filter] at hA₁
            exact mul_le_mul_of_nonneg_left hA₁.2 hw0
        _ ≤ ∑ A₁ : Finset A, w * F A₁ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            intro A₁ _ _; exact mul_nonneg hw0 (hv0 _)
    have hcard : (2 : ℝ) ^ n ≤ 2 * (G.card : ℝ) := by
      have : (2 ^ n : ℕ) ≤ 2 * G.card := by
        exact key
      exact_mod_cast this
    have hwn : w * 2 ^ n = 1 - 201 / 1000 := by
      rw [hw, hp]; field_simp
    have hlow : (1 - 201 / 1000) / 2 * bound ≤ ∑ A₁ : Finset A, w * F A₁ := by
      have h2n : (0 : ℝ) < 2 ^ n := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hcard (mul_nonneg hw0 hb0)]
    have hfin : O ≤ 505 * ((1 - 201 / 1000) / 2 * bound) := by
      rw [hbound, hβ]; push_cast
      have hepos : 0 < Real.exp 1 := Real.exp_pos 1
      rw [show 505 * ((1 - 201 / 1000) / 2 * (50 / Real.exp 1 * (1 / (4 * (9185 / 1000) * 101)) * O))
          = (505 * (1 - 201 / 1000) / 2 * 50 / (4 * (9185 / 1000) * 101)) * O / Real.exp 1 by
            field_simp]
      rw [le_div_iff₀ hepos]
      nlinarith
    nlinarith
