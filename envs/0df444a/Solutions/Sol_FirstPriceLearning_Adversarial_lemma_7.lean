-- Prove2me | solution 1 for FirstPriceLearning.Adversarial.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T06:46:04.709626+00:00
-- url     : https://prove2.me/submissions/70e5da0d-f1d3-4e17-90fb-1477adf5dcef

import Mathlib
import Definitions.Def_FirstPriceLearning_Adversarial_Model
import Definitions.Def_FirstPriceLearning_Adversarial_MLISUCB
import Theorems.Thm_FirstPriceLearning_Adversarial_lemma_7_target
import Theorems.Thm_FirstPriceLearning_Adversarial_lemma_7_heldout

open MeasureTheory

namespace FPA2bL7

open FirstPriceLearning.Adversarial

theorem two_le_of_init (T t : ℕ) (h1 : initLength T < t) (h2 : t ≤ T) : 2 ≤ T := by
  by_contra hT
  push Not at hT
  interval_cases T
  · omega
  · unfold initLength numLevels numGrid at h1
    simp at h1
    omega

theorem numLevels_pos (T : ℕ) (hT : 2 ≤ T) : 1 ≤ numLevels T := by
  unfold numLevels
  exact Nat.clog_pos (by norm_num) (by omega)

theorem numGrid_two_le (T : ℕ) (hT : 2 ≤ T) : 2 ≤ numGrid T := by
  unfold numGrid
  have h : (1 : ℝ) < Real.sqrt T := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    apply Real.sqrt_lt_sqrt (by norm_num)
    exact_mod_cast (by omega : 1 < T)
  have : 1 < ⌈Real.sqrt T⌉₊ := by
    rw [Nat.lt_ceil]; exact_mod_cast h
  omega

theorem cdf_mono (μG : Measure ℝ) [IsProbabilityMeasure μG] {x y : ℝ} (h : x ≤ y) :
    FirstPriceLearning.Stochastic.cdf μG x ≤ FirstPriceLearning.Stochastic.cdf μG y := by
  unfold FirstPriceLearning.Stochastic.cdf
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.mpr h))

theorem intervalProb_nonneg' (T : ℕ) (μG : Measure ℝ) [IsProbabilityMeasure μG] (j : ℕ) :
    0 ≤ intervalProb T μG j := by
  unfold intervalProb
  have : grid (numGrid T) j ≤ grid (numGrid T) (j + 1) := by
    unfold grid
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    push_cast; linarith
  linarith [cdf_mono μG this]

set_option maxHeartbeats 2000000 in
theorem lemma7_core (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : IsSelectionRule sel) (v : Fin T → ℝ) (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    (Measure.pi fun _ : Fin T => μG)
        {m | ¬ ∀ i < numGrid T, ∀ ℓ ∈ Finset.Icc 1 (numLevels T), ∀ t : ℕ,
            initLength T < t → t ≤ T →
              |runRhat T γ sel v m ℓ i t - gridReward μG v i t| ≤ runWidth T γ sel v m ℓ i t ∧
              runWidth T γ sel v m ℓ i t ≤ widthBound T γ sel μG v m ℓ i t}
      ≤ ENNReal.ofReal (4 / (T : ℝ) ^ 3) := by
  classical
  set μ := Measure.pi fun _ : Fin T => μG with hμ
  by_cases hT0 : initLength T < T
  swap
  · -- no round after the initialization: the event is empty
    have : {m : Fin T → ℝ | ¬ ∀ i < numGrid T, ∀ ℓ ∈ Finset.Icc 1 (numLevels T), ∀ t : ℕ,
            initLength T < t → t ≤ T →
              |runRhat T γ sel v m ℓ i t - gridReward μG v i t| ≤ runWidth T γ sel v m ℓ i t ∧
              runWidth T γ sel v m ℓ i t ≤ widthBound T γ sel μG v m ℓ i t} = ∅ := by
      ext m
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      intro i _ ℓ _ t h1 h2
      omega
    rw [this, measure_empty]; exact bot_le
  have hT2 : 2 ≤ T := two_le_of_init T T hT0 le_rfl
  have hL := numLevels_pos T hT2
  have hK2 := numGrid_two_le T hT2
  set K := numGrid T with hKdef
  set L := numLevels T with hLdef
  set a := logFactor T with hadef
  set a' := Real.log ((K : ℝ) * (T : ℝ)) with ha'def
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hLpos : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have ha'a : a' ≤ a := by
    simp only [ha'def, hadef, logFactor]
    rw [← hLdef, ← hKdef]
    apply Real.log_le_log (by positivity)
    have : (K : ℝ) * T ≤ L * (K * T) := le_mul_of_one_le_left (by positivity) hLpos
    linarith [mul_assoc (L : ℝ) K T]
  have ha'0 : 0 ≤ a' := Real.log_nonneg (by
    have : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
    have : (1 : ℝ) ≤ T := by
      have : (2 : ℝ) ≤ T := by exact_mod_cast hT2
      linarith
    nlinarith)
  have ha0 : 0 ≤ a := le_trans ha'0 ha'a
  have hγ0 : 0 ≤ γ := by linarith
  -- the bad sets of the two children
  set A : ℕ → ℕ → ℕ → Set (Fin T → ℝ) := fun i ℓ t =>
    {m | γ * (Real.sqrt (a * ∑ j ∈ Finset.Ico i K,
                intervalProb T μG j / (runN T γ sel v m ℓ j t : ℝ))
              + a / (runN T γ sel v m ℓ i t : ℝ))
            ≤ |runRhat T γ sel v m ℓ i t - gridReward μG v i t|} with hA
  set B : ℕ → Set (Fin T → ℝ) := fun j =>
    {m | ¬ (intervalProb T μG j ≤
              2 * (phat0 T (runRecord T γ sel v m) (runFeedback T γ sel v m) j
                + γ * a' / (K : ℝ)) ∧
            phat0 T (runRecord T γ sel v m) (runFeedback T γ sel v m) j ≤
              2 * (intervalProb T μG j + γ * a' / (K : ℝ)))} with hB
  -- inclusion of the bad event
  have hsub : {m : Fin T → ℝ | ¬ ∀ i < numGrid T, ∀ ℓ ∈ Finset.Icc 1 (numLevels T), ∀ t : ℕ,
            initLength T < t → t ≤ T →
              |runRhat T γ sel v m ℓ i t - gridReward μG v i t| ≤ runWidth T γ sel v m ℓ i t ∧
              runWidth T γ sel v m ℓ i t ≤ widthBound T γ sel μG v m ℓ i t} ⊆
      (⋃ i ∈ Finset.range K, ⋃ ℓ ∈ Finset.Icc 1 L, ⋃ t ∈ Finset.Ioc (initLength T) T, A i ℓ t)
        ∪ (⋃ j ∈ Finset.range K, B j) := by
    intro m hm
    by_contra hnot
    apply hm
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hnot
    obtain ⟨hnA, hnB⟩ := hnot
    intro i hi ℓ hℓ t ht1 ht2
    have hgA : |runRhat T γ sel v m ℓ i t - gridReward μG v i t| <
        γ * (Real.sqrt (a * ∑ j ∈ Finset.Ico i K,
                intervalProb T μG j / (runN T γ sel v m ℓ j t : ℝ))
              + a / (runN T γ sel v m ℓ i t : ℝ)) := by
      have := hnA i (Finset.mem_range.mpr hi) ℓ hℓ t (Finset.mem_Ioc.mpr ⟨ht1, ht2⟩)
      simp only [hA, Set.mem_setOf_eq, not_le] at this
      exact this
    have hgB : ∀ j < K, intervalProb T μG j ≤
              2 * (phat0 T (runRecord T γ sel v m) (runFeedback T γ sel v m) j
                + γ * a' / (K : ℝ)) ∧
            phat0 T (runRecord T γ sel v m) (runFeedback T γ sel v m) j ≤
              2 * (intervalProb T μG j + γ * a' / (K : ℝ)) := by
      intro j hj
      have := hnB j (Finset.mem_range.mpr hj)
      simp only [hB, Set.mem_setOf_eq, not_not] at this
      exact this
    set p0 := fun j => phat0 T (runRecord T γ sel v m) (runFeedback T γ sel v m) j with hp0
    set n := fun j => (runN T γ sel v m ℓ j t : ℝ) with hn
    have hn0 : ∀ j, 0 ≤ 1 / n j := fun j => by simp only [hn]; positivity
    have hc : γ * a' / (K : ℝ) ≤ γ * a / (K : ℝ) := by
      apply div_le_div_of_nonneg_right _ hKpos.le
      exact mul_le_mul_of_nonneg_left ha'a hγ0
    -- (17)
    have hS1 : a * ∑ j ∈ Finset.Ico i K, intervalProb T μG j / n j ≤
        2 * a * ∑ j ∈ Finset.Ico i K, 1 / n j * (p0 j + γ * a / (K : ℝ)) := by
      have hsum : ∑ j ∈ Finset.Ico i K, intervalProb T μG j / n j ≤
          ∑ j ∈ Finset.Ico i K, 2 * (1 / n j * (p0 j + γ * a / (K : ℝ))) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjK : j < K := (Finset.mem_Ico.mp hj).2
        have h1 := (hgB j hjK).1
        have : intervalProb T μG j / n j = 1 / n j * intervalProb T μG j := by ring
        rw [this]
        have : 1 / n j * intervalProb T μG j ≤ 1 / n j * (2 * (p0 j + γ * a / (K : ℝ))) :=
          mul_le_mul_of_nonneg_left (by linarith) (hn0 j)
        linarith
      rw [← Finset.mul_sum] at hsum
      have := mul_le_mul_of_nonneg_left hsum ha0
      linarith
    have h17 : |runRhat T γ sel v m ℓ i t - gridReward μG v i t| ≤ runWidth T γ sel v m ℓ i t := by
      refine le_trans hgA.le ?_
      unfold runWidth width
      apply mul_le_mul_of_nonneg_left _ hγ0
      apply add_le_add _ le_rfl
      apply Real.sqrt_le_sqrt
      exact hS1
    -- (18)
    have hS2 : ∑ j ∈ Finset.Ico i K, 1 / n j * (p0 j + γ * a / (K : ℝ)) ≤
        3 * ∑ j ∈ Finset.Ico i K, 1 / n j * (intervalProb T μG j + γ * a / (K : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hjK : j < K := (Finset.mem_Ico.mp hj).2
      have h2 := (hgB j hjK).2
      have hp := intervalProb_nonneg' T μG j
      have : p0 j + γ * a / (K : ℝ) ≤ 3 * (intervalProb T μG j + γ * a / (K : ℝ)) := by
        have : 0 ≤ γ * a / (K : ℝ) := by positivity
        linarith
      have := mul_le_mul_of_nonneg_left this (hn0 j)
      linarith
    have h18 : runWidth T γ sel v m ℓ i t ≤ widthBound T γ sel μG v m ℓ i t := by
      unfold runWidth width widthBound
      apply mul_le_mul_of_nonneg_left _ hγ0
      apply add_le_add _ le_rfl
      apply Real.sqrt_le_sqrt
      have := mul_le_mul_of_nonneg_left hS2 (show (0 : ℝ) ≤ 2 * a by positivity)
      show 2 * a * ∑ j ∈ Finset.Ico i K, 1 / n j * (p0 j + γ * a / (K : ℝ)) ≤
        6 * a * ∑ j ∈ Finset.Ico i K, 1 / n j * (intervalProb T μG j + γ * a / (K : ℝ))
      linarith
    exact ⟨h17, h18⟩
  -- union bound
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_union_le _ _) ?_
  have hAb : ∀ i ∈ Finset.range K, ∀ ℓ ∈ Finset.Icc 1 L, ∀ t ∈ Finset.Ioc (initLength T) T,
      μ (A i ℓ t) ≤ ENNReal.ofReal (2 / ((L : ℝ) * (K : ℝ) * (T : ℝ)) ^ 4) := by
    intro i hi ℓ hℓ t ht
    rw [Finset.mem_Ioc] at ht
    exact FirstPriceLearning.Adversarial.lemma_7_target T γ hγ sel hsel v hv μG hG i
      (Finset.mem_range.mp hi) ℓ hℓ t ht.1 ht.2
  have hBb : ∀ j ∈ Finset.range K, μ (B j) ≤ ENNReal.ofReal (2 / ((K : ℝ) * (T : ℝ)) ^ 3) := by
    intro j hj
    exact FirstPriceLearning.Adversarial.lemma_7_heldout T γ hγ sel hsel v hv μG hG j
      (Finset.mem_range.mp hj)
  have hU1 : μ (⋃ i ∈ Finset.range K, ⋃ ℓ ∈ Finset.Icc 1 L,
      ⋃ t ∈ Finset.Ioc (initLength T) T, A i ℓ t) ≤
      ∑ i ∈ Finset.range K, ∑ ℓ ∈ Finset.Icc 1 L, ∑ t ∈ Finset.Ioc (initLength T) T,
        ENNReal.ofReal (2 / ((L : ℝ) * (K : ℝ) * (T : ℝ)) ^ 4) := by
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    apply Finset.sum_le_sum; intro i hi
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    apply Finset.sum_le_sum; intro ℓ hℓ
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    apply Finset.sum_le_sum; intro t ht
    exact hAb i hi ℓ hℓ t ht
  have hU2 : μ (⋃ j ∈ Finset.range K, B j) ≤
      ∑ j ∈ Finset.range K, ENNReal.ofReal (2 / ((K : ℝ) * (T : ℝ)) ^ 3) := by
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    exact Finset.sum_le_sum hBb
  refine le_trans (add_le_add hU1 hU2) ?_
  simp only [Finset.sum_const, Finset.card_range, Nat.card_Icc, Nat.card_Ioc, nsmul_eq_mul,
    add_tsub_cancel_right]
  -- arithmetic
  have hcardT : ((T - initLength T : ℕ) : ℝ) ≤ T := by
    exact_mod_cast Nat.sub_le T (initLength T)
  have hx1 : (0 : ℝ) ≤ 2 / ((L : ℝ) * (K : ℝ) * (T : ℝ)) ^ 4 := by positivity
  have hx2 : (0 : ℝ) ≤ 2 / ((K : ℝ) * (T : ℝ)) ^ 3 := by positivity
  rw [show ((K : ℕ) : ENNReal) = ENNReal.ofReal (K : ℝ) from (ENNReal.ofReal_natCast K).symm,
    show ((L : ℕ) : ENNReal) = ENNReal.ofReal (L : ℝ) from (ENNReal.ofReal_natCast L).symm,
    show ((T - initLength T : ℕ) : ENNReal) = ENNReal.ofReal ((T - initLength T : ℕ) : ℝ) from
      (ENNReal.ofReal_natCast _).symm]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hK1 : (1 : ℝ) ≤ K := by linarith [show (2 : ℝ) ≤ K by exact_mod_cast hK2]
  have hLKT : (0 : ℝ) < (L : ℝ) * (K : ℝ) * (T : ℝ) := by positivity
  have e1 : (K : ℝ) * ((L : ℝ) * ((T : ℝ) * (2 / ((L : ℝ) * (K : ℝ) * (T : ℝ)) ^ 4))) ≤
      2 / (T : ℝ) ^ 3 := by
    have hTL : (K : ℝ) * ((L : ℝ) * ((T : ℝ) * (2 / ((L : ℝ) * (K : ℝ) * (T : ℝ)) ^ 4))) =
        2 / ((L : ℝ) * (K : ℝ) * (T : ℝ)) ^ 3 := by
      field_simp
    rw [hTL]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have : (T : ℝ) ≤ (L : ℝ) * (K : ℝ) * (T : ℝ) := by
      have : (1 : ℝ) ≤ (L : ℝ) * (K : ℝ) := by nlinarith
      nlinarith
    exact pow_le_pow_left₀ (by positivity) this 3
  have e2 : (K : ℝ) * (2 / ((K : ℝ) * (T : ℝ)) ^ 3) ≤ 2 / (T : ℝ) ^ 3 := by
    have : (K : ℝ) * (2 / ((K : ℝ) * (T : ℝ)) ^ 3) = 2 / (T : ℝ) ^ 3 / (K : ℝ) ^ 2 := by
      field_simp
    rw [this]
    apply div_le_self (by positivity)
    nlinarith
  have e0 : (K : ℝ) * ((L : ℝ) * (((T - initLength T : ℕ) : ℝ) *
      (2 / ((L : ℝ) * (K : ℝ) * (T : ℝ)) ^ 4))) ≤
      (K : ℝ) * ((L : ℝ) * ((T : ℝ) * (2 / ((L : ℝ) * (K : ℝ) * (T : ℝ)) ^ 4))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right hcardT hx1
  have : 2 / (T : ℝ) ^ 3 + 2 / (T : ℝ) ^ 3 = 4 / (T : ℝ) ^ 3 := by ring
  linarith

end FPA2bL7

open FirstPriceLearning.Adversarial in
theorem solution (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : IsSelectionRule sel) (v : Fin T → ℝ) (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    (Measure.pi fun _ : Fin T => μG)
        {m | ¬ ∀ i < numGrid T, ∀ ℓ ∈ Finset.Icc 1 (numLevels T), ∀ t : ℕ,
            initLength T < t → t ≤ T →
              |runRhat T γ sel v m ℓ i t - gridReward μG v i t| ≤ runWidth T γ sel v m ℓ i t ∧
              runWidth T γ sel v m ℓ i t ≤ widthBound T γ sel μG v m ℓ i t}
      ≤ ENNReal.ofReal (4 / (T : ℝ) ^ 3) :=
  FPA2bL7.lemma7_core T γ hγ sel hsel v hv μG hG
