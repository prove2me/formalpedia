-- Prove2me | solution 1 for FirstPriceLearning.Stochastic.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:51:33.032479+00:00
-- url     : https://prove2.me/submissions/2e80b6af-2911-486e-a401-957b4770a984

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_Auction

set_option autoImplicit false
open MeasureTheory FirstPriceLearning.Stochastic

theorem grid_round (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (N : ℕ) (hN : 1 ≤ N) :
    ∃ j : ℕ, j < N ∧ x ≤ ((j : ℝ) + 1) / N ∧ ((j : ℝ) + 1) / N ≤ x + 1 / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set c := ⌈x * N⌉₊ with hc
  obtain ⟨j, hj⟩ : ∃ j, j + 1 = max c 1 := ⟨max c 1 - 1, by omega⟩
  have hcN : c ≤ N := by
    rw [hc, Nat.ceil_le]; nlinarith
  refine ⟨j, by omega, ?_, ?_⟩
  · rw [le_div_iff₀ hNpos]
    have h1 : x * N ≤ (c : ℝ) := Nat.le_ceil _
    have h2 : (c : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : c ≤ j + 1)
    push_cast at h2
    linarith
  · rw [div_le_iff₀ hNpos]
    have h1 : (c : ℝ) < x * N + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : ((j + 1 : ℕ) : ℝ) ≤ x * N + 1 := by
      have : j + 1 = c ∨ j + 1 = 1 := by omega
      rcases this with h | h
      · rw [h]; linarith
      · rw [h]; push_cast; nlinarith
    push_cast at h2
    have : (x + 1 / (N : ℝ)) * N = x * N + 1 := by field_simp
    linarith

theorem solution (T M K : ℕ) (hM : 1 ≤ M) (hK : 1 ≤ K) (μG : Measure ℝ) [IsProbabilityMeasure μG]
    (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0) (v : Fin T → ℝ) (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (b : Fin T → ℝ) (hb : ∀ t, b t ∈ gridA K) :
    regret μG v b ≤
      gridRegret μG (gridA K) (fun t => clipValue M (v t)) b + (2 / M + 1 / K) * T := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hGmono : Monotone (cdf μG) := by
    intro x y hxy
    unfold cdf
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.2 hxy))
  have hG0 : ∀ x, 0 ≤ cdf μG x := fun x => ENNReal.toReal_nonneg
  have hG1 : ∀ x, cdf μG x ≤ 1 := by
    intro x
    unfold cdf
    have := (ENNReal.toReal_le_toReal (measure_ne_top μG (Set.Iic x)) ENNReal.one_ne_top).2
      (prob_le_one (μ := μG) (s := Set.Iic x))
    simpa using this
  -- clipping
  have hclip : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      x ≤ clipValue M x ∧ clipValue M x ≤ x + 1 / M ∧ clipValue M x ≤ 1 := by
    intro x hx0 hx1
    obtain ⟨j, hjM, hj1, hj2⟩ := grid_round x hx0 hx1 M hM
    have hyS : ((j : ℝ) + 1) / M ∈ {y : ℝ | y ∈ gridC M ∧ x ≤ y} := by
      refine ⟨?_, hj1⟩
      unfold gridC
      exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 hjM, rfl⟩
    have hfin : {y : ℝ | y ∈ gridC M ∧ x ≤ y}.Finite :=
      (gridC M).finite_toSet.subset (fun y hy => hy.1)
    have hmem : clipValue M x ∈ {y : ℝ | y ∈ gridC M ∧ x ≤ y} :=
      Set.Nonempty.csInf_mem ⟨_, hyS⟩ hfin
    have hle : clipValue M x ≤ ((j : ℝ) + 1) / M :=
      csInf_le ⟨x, fun y hy => hy.2⟩ hyS
    refine ⟨hmem.2, hle.trans hj2, ?_⟩
    have hm1 := hmem.1
    unfold gridC at hm1
    obtain ⟨i, hi, hieq⟩ := Finset.mem_image.1 hm1
    rw [← hieq, div_le_one hMpos]
    have : (i : ℝ) + 1 ≤ M := by exact_mod_cast Finset.mem_range.1 hi
    exact this
  -- rounding to the bid grid
  have hround : ∀ w : ℝ, 0 ≤ w → w ≤ 1 → ∀ b0 : ℝ, 0 ≤ b0 → b0 ≤ 1 →
      ∃ b' ∈ gridA K, expReward μG w b0 ≤ expReward μG w b' + 1 / K := by
    intro w hw0 hw1 b0 hb0 hb1
    obtain ⟨j, hjK, hj1, hj2⟩ := grid_round b0 hb0 hb1 K hK
    set b1 : ℝ := ((j : ℝ) + 1) / K with hb1def
    have hb1mem : b1 ∈ gridA K := by
      unfold gridA
      exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 hjK, rfl⟩
    have hKinv : 0 < 1 / (K : ℝ) := by positivity
    have hGb0 := hG0 b0
    have hGb0' := hG1 b0
    by_cases hw : b1 ≤ w
    · refine ⟨b1, hb1mem, ?_⟩
      unfold expReward
      have h1 : (w - b1) * cdf μG b0 ≤ (w - b1) * cdf μG b1 :=
        mul_le_mul_of_nonneg_left (hGmono hj1) (by linarith)
      have h2 : (b1 - b0) * cdf μG b0 ≤ (b1 - b0) * 1 :=
        mul_le_mul_of_nonneg_left hGb0' (by linarith)
      nlinarith [h1, h2]
    · push_neg at hw
      have h1Kmem : 1 / (K : ℝ) ∈ gridA K := by
        unfold gridA
        refine Finset.mem_image.2 ⟨0, Finset.mem_range.2 (by omega), ?_⟩
        simp
      refine ⟨1 / (K : ℝ), h1Kmem, ?_⟩
      unfold expReward
      have hRb0 : (w - b0) * cdf μG b0 ≤ w := by
        by_cases hwb : w ≤ b0
        · nlinarith [mul_nonneg (sub_nonneg.2 hwb) hGb0]
        · push_neg at hwb
          nlinarith [mul_le_mul_of_nonneg_left hGb0' (by linarith : 0 ≤ w - b0)]
      have hRb0' : (w - b0) * cdf μG b0 ≤ 1 / K := by
        by_cases hwb : w ≤ b0
        · nlinarith [mul_nonneg (sub_nonneg.2 hwb) hGb0]
        · push_neg at hwb
          nlinarith [mul_le_mul_of_nonneg_left hGb0' (by linarith : 0 ≤ w - b0)]
      have hGK := hG0 (1 / (K : ℝ))
      have hGK' := hG1 (1 / (K : ℝ))
      by_cases hwK : 1 / (K : ℝ) ≤ w
      · nlinarith [mul_nonneg (sub_nonneg.2 hwK) hGK]
      · push_neg at hwK
        nlinarith [mul_le_mul_of_nonneg_left hGK' (by linarith : 0 ≤ 1 / (K : ℝ) - w)]
  -- per-round bound
  have hround_t : ∀ t : Fin T, oracle μG (v t) - expReward μG (v t) (b t) ≤
      ((⨆ x : (gridA K), expReward μG (clipValue M (v t)) x) -
        expReward μG (clipValue M (v t)) (b t)) + (2 / M + 1 / K) := by
    intro t
    obtain ⟨hv0, hv1⟩ := hv t
    obtain ⟨hc1, hc2, hc3⟩ := hclip (v t) hv0 hv1
    set w := clipValue M (v t) with hw
    have hw0 : 0 ≤ w := hv0.trans hc1
    have hbdd : BddAbove (Set.range fun x : (gridA K) => expReward μG w x) :=
      (Set.finite_range _).bddAbove
    have horacle : oracle μG (v t) ≤ (⨆ x : (gridA K), expReward μG w x) + 1 / K := by
      unfold oracle
      haveI : Nonempty (Set.Icc (0 : ℝ) 1) := ⟨⟨0, by simp⟩⟩
      apply ciSup_le
      intro b0
      have hRle : expReward μG (v t) b0 ≤ expReward μG w b0 := by
        unfold expReward
        exact mul_le_mul_of_nonneg_right (by linarith) (hG0 _)
      obtain ⟨b', hb'A, hb'⟩ := hround w hw0 hc3 b0 b0.2.1 b0.2.2
      have : expReward μG w b' ≤ ⨆ x : (gridA K), expReward μG w x :=
        le_ciSup hbdd ⟨b', hb'A⟩
      linarith
    have hRb : expReward μG w (b t) ≤ expReward μG (v t) (b t) + 1 / M := by
      unfold expReward
      have h1 : (w - v t) * cdf μG (b t) ≤ (w - v t) * 1 :=
        mul_le_mul_of_nonneg_left (hG1 _) (by linarith)
      have h2 : (0 : ℝ) ≤ 1 / M := by positivity
      nlinarith [h1]
    have h3 : (0 : ℝ) ≤ 1 / M := by positivity
    have h4 : (2 : ℝ) / M = 1 / M + 1 / M := by ring
    linarith
  unfold regret gridRegret
  calc ∑ t, (oracle μG (v t) - expReward μG (v t) (b t))
      ≤ ∑ t : Fin T, (((⨆ x : (gridA K), expReward μG (clipValue M (v t)) x) -
          expReward μG (clipValue M (v t)) (b t)) + (2 / M + 1 / K)) :=
        Finset.sum_le_sum (fun t _ => hround_t t)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
