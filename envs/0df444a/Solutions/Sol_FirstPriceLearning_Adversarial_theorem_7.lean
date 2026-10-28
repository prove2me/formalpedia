-- Prove2me | solution 1 for FirstPriceLearning.Adversarial.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T06:29:08.465991+00:00
-- url     : https://prove2.me/submissions/49639922-c778-4176-9f2b-c274f5115096

import Mathlib
import Definitions.Def_FirstPriceLearning_Adversarial_Model
import Definitions.Def_FirstPriceLearning_Adversarial_MLISUCB
import Theorems.Thm_FirstPriceLearning_Adversarial_eq_19
import Theorems.Thm_FirstPriceLearning_Adversarial_lemma_7
import Theorems.Thm_FirstPriceLearning_Adversarial_lemma_9

open MeasureTheory

namespace FPA2Core

open FirstPriceLearning.Adversarial

/-! ### Congruence: the round-`t` decision only reads the record at times `< t`. -/

/-- Membership in `cand (ℓ+1)`. -/
theorem mem_cand_succ (T : ℕ) (γ : ℝ) (y v : ℕ → ℝ) (rec : ℕ → ℕ × ℕ) (t ℓ i : ℕ) :
    i ∈ cand T γ rec y v t (ℓ + 1) ↔ i ∈ cand T γ rec y v t ℓ ∧
      (if h : (cand T γ rec y v t ℓ).Nonempty then (cand T γ rec y v t ℓ).sup' h
        (fun j => rhat T rec y v (ℓ + 1) j t + width T γ rec y (ℓ + 1) j t) else 0)
        - 2 * (1 / 2 : ℝ) ^ (ℓ + 1)
        ≤ rhat T rec y v (ℓ + 1) i t + width T γ rec y (ℓ + 1) i t := by
  simp only [cand, Finset.mem_filter]


section congr

variable (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (y v : ℕ → ℝ)
  (rec rec' : ℕ → ℕ × ℕ) (t : ℕ)

theorem levelSet_congr (h : ∀ s, s < t → rec s = rec' s) (ℓ : ℕ) (u : ℕ) (hu : u < t) :
    levelSet rec ℓ u = levelSet rec' ℓ u := by
  unfold levelSet
  apply Finset.filter_congr
  intro s hs
  rw [Finset.mem_Icc] at hs
  rw [h s (by omega)]

theorem nObs_congr (ht : 1 ≤ t) (h : ∀ s, s < t → rec s = rec' s) (ℓ i : ℕ) :
    nObs T rec ℓ i t = nObs T rec' ℓ i t := by
  unfold nObs obsCount
  rw [levelSet_congr rec rec' t h ℓ (t - 1) (by omega)]
  congr 1
  apply Finset.filter_congr
  intro s hs
  unfold levelSet at hs
  simp only [Finset.mem_filter, Finset.mem_Icc] at hs
  simp only [h s (by omega)]

theorem phat0_congr (ht : initLength T < t) (h : ∀ s, s < t → rec s = rec' s) (j : ℕ) :
    phat0 T rec y j = phat0 T rec' y j := by
  unfold phat0
  rw [levelSet_congr rec rec' t h 0 (initLength T) ht]

theorem width_congr (ht : initLength T < t) (h : ∀ s, s < t → rec s = rec' s) (ℓ i : ℕ) :
    width T γ rec y ℓ i t = width T γ rec' y ℓ i t := by
  unfold width
  have h1 : 1 ≤ t := by omega
  simp only [nObs_congr T rec rec' t h1 h, phat0_congr T y rec rec' t ht h]

theorem phat_congr (ht : 1 ≤ t) (h : ∀ s, s < t → rec s = rec' s) (ℓ i : ℕ) :
    phat T rec y ℓ i t = phat T rec' y ℓ i t := by
  unfold phat
  rw [nObs_congr T rec rec' t ht h, levelSet_congr rec rec' t h ℓ (t - 1) (by omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  unfold levelSet at hs
  simp only [Finset.mem_filter, Finset.mem_Icc] at hs
  rw [h s (by omega)]

theorem rhat_congr (ht : 1 ≤ t) (h : ∀ s, s < t → rec s = rec' s) (ℓ i : ℕ) :
    rhat T rec y v ℓ i t = rhat T rec' y v ℓ i t := by
  unfold rhat
  simp only [phat_congr T y rec rec' t ht h]

theorem cand_congr (ht : initLength T < t) (h : ∀ s, s < t → rec s = rec' s) (ℓ : ℕ) :
    cand T γ rec y v t ℓ = cand T γ rec' y v t ℓ := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    have h1 : 1 ≤ t := by omega
    ext i
    rw [mem_cand_succ, mem_cand_succ, ih]
    simp only [rhat_congr T y v rec rec' t h1 h, width_congr T γ y rec rec' t ht h]

theorem exploreSet_congr (ht : initLength T < t) (h : ∀ s, s < t → rec s = rec' s) (ℓ : ℕ) :
    exploreSet T γ rec y v ℓ t = exploreSet T γ rec' y v ℓ t := by
  unfold exploreSet
  simp only [cand_congr T γ y v rec rec' t ht h, width_congr T γ y rec rec' t ht h]

theorem breakLevels_congr (ht : initLength T < t) (h : ∀ s, s < t → rec s = rec' s) :
    breakLevels T γ rec y v t = breakLevels T γ rec' y v t := by
  unfold breakLevels
  simp only [exploreSet_congr T γ y v rec rec' t ht h]

theorem decideRound_congr (ht : initLength T < t) (h : ∀ s, s < t → rec s = rec' s) :
    decideRound T γ sel rec y v t = decideRound T γ sel rec' y v t := by
  unfold decideRound
  simp only [breakLevels_congr T γ y v rec rec' t ht h, exploreSet_congr T γ y v rec rec' t ht h]

end congr

/-! ### The record equations -/

theorem record_le (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v y : ℕ → ℝ) (t : ℕ)
    (ht : t ≤ initLength T) :
    record T γ sel v y t = ((t - 1) / numGrid T, 0) := by
  rw [record]; simp [ht]

theorem record_gt (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v y : ℕ → ℝ) (t : ℕ)
    (ht : initLength T < t) :
    record T γ sel v y t = decideRound T γ sel (record T γ sel v y) y v t := by
  rw [record]
  simp only [show ¬ t ≤ initLength T from by omega, if_false]
  apply decideRound_congr T γ sel y v _ _ t ht
  intro s hs
  simp [hs]

/-! ### Basic numerics -/

theorem numGrid_pos (T : ℕ) (hT : 1 ≤ T) : 1 ≤ numGrid T := by
  unfold numGrid
  apply Nat.one_le_iff_ne_zero.mpr
  intro h0
  rw [Nat.ceil_eq_zero] at h0
  have : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  linarith

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

theorem le_two_pow_numLevels (T : ℕ) : T ≤ 2 ^ numLevels T := by
  unfold numLevels
  exact Nat.le_pow_clog (by norm_num) T

theorem numGrid_two_le (T : ℕ) (hT : 2 ≤ T) : 2 ≤ numGrid T := by
  unfold numGrid
  have h : (1 : ℝ) < Real.sqrt T := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    apply Real.sqrt_lt_sqrt (by norm_num)
    exact_mod_cast (by omega : 1 < T)
  have : 1 < ⌈Real.sqrt T⌉₊ := by
    rw [Nat.lt_ceil]; exact_mod_cast h
  omega

theorem one_le_logFactor (T : ℕ) (hT : 2 ≤ T) : 1 ≤ logFactor T := by
  unfold logFactor
  have hL : (1 : ℝ) ≤ numLevels T := by exact_mod_cast numLevels_pos T hT
  have hK : (2 : ℝ) ≤ numGrid T := by exact_mod_cast numGrid_two_le T hT
  have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have h4 : (4 : ℝ) ≤ (numLevels T : ℝ) * (numGrid T : ℝ) * (T : ℝ) := by
    have : (2 : ℝ) ≤ (numLevels T : ℝ) * (numGrid T : ℝ) := by nlinarith
    nlinarith
  have hlog4 : 1 ≤ Real.log 4 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  calc (1 : ℝ) ≤ Real.log 4 := hlog4
    _ ≤ _ := Real.log_le_log (by norm_num) h4

theorem logFactor_nonneg (T : ℕ) : 0 ≤ logFactor T := by
  rcases Nat.lt_or_ge T 2 with h | h
  · interval_cases T <;> simp [logFactor, numLevels]
  · linarith [one_le_logFactor T h]

/-! ### Structure of the candidate sets -/

variable (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (y v : ℕ → ℝ)
  (rec : ℕ → ℕ × ℕ) (t : ℕ)

theorem cand_succ_subset (ℓ : ℕ) : cand T γ rec y v t (ℓ + 1) ⊆ cand T γ rec y v t ℓ := by
  intro i hi
  simp only [cand] at hi
  exact (Finset.mem_filter.mp hi).1

theorem cand_subset_range (ℓ : ℕ) : cand T γ rec y v t ℓ ⊆ Finset.range (numGrid T) := by
  induction ℓ with
  | zero => exact le_refl _
  | succ ℓ ih => exact (cand_succ_subset T γ y v rec t ℓ).trans ih

theorem cand_antitone {ℓ₁ ℓ₂ : ℕ} (h : ℓ₁ ≤ ℓ₂) :
    cand T γ rec y v t ℓ₂ ⊆ cand T γ rec y v t ℓ₁ := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact (cand_succ_subset T γ y v rec t _).trans ih

theorem cand_nonempty (hK : 1 ≤ numGrid T) (ℓ : ℕ) : (cand T γ rec y v t ℓ).Nonempty := by
  induction ℓ with
  | zero => simp [cand]; omega
  | succ ℓ ih =>
    simp only [cand]
    set B := cand T γ rec y v t ℓ
    set ucb := fun j => rhat T rec y v (ℓ + 1) j t + width T γ rec y (ℓ + 1) j t
    obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image B ucb ih
    refine ⟨j, Finset.mem_filter.mpr ⟨hj, ?_⟩⟩
    rw [dif_pos ih]
    have : B.sup' ih ucb ≤ ucb j := Finset.sup'_le ih ucb hjmax
    have hp : (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ (ℓ + 1) := by positivity
    linarith

end FPA2Core

namespace FPA2Core

open FirstPriceLearning.Adversarial

theorem init_level (T : ℕ) (hT : 1 ≤ T) :
    (initLength T - 1) / numGrid T = numLevels T := by
  unfold initLength
  have hK := numGrid_pos T hT
  apply Nat.div_eq_of_lt_le
  · have : numLevels T * numGrid T + numGrid T = (numLevels T + 1) * numGrid T := by ring
    omega
  · have : (numLevels T + 1) * numGrid T ≥ 1 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega

/-- Positivity and smallness of the level-`ℓ` counts after the initialization. -/
theorem nObs_pos (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (V Y : ℕ → ℝ) (t : ℕ)
    (ht0 : initLength T < t) (htT : t ≤ T) (ℓ i : ℕ) (hℓ : ℓ ≤ numLevels T) :
    1 ≤ nObs T (record T γ sel V Y) ℓ i t := by
  have hT : 1 ≤ T := by omega
  have hK := numGrid_pos T hT
  -- the time `s0 = ℓ * K + 1` of the initialization block of level `ℓ`
  set s0 := ℓ * numGrid T + 1 with hs0
  have hs0le : s0 ≤ initLength T := by
    unfold initLength
    have : ℓ * numGrid T + numGrid T = (ℓ + 1) * numGrid T := by ring
    have : (ℓ + 1) * numGrid T ≤ (numLevels T + 1) * numGrid T :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hrec : record T γ sel V Y s0 = (ℓ, 0) := by
    rw [record_le T γ sel V Y s0 hs0le]
    congr 1
    rw [hs0, Nat.add_sub_cancel, Nat.mul_div_cancel _ (by omega)]
  unfold nObs obsCount
  apply Finset.card_pos.mpr
  refine ⟨s0, ?_⟩
  simp only [Finset.mem_filter, levelSet, Finset.mem_Icc, hrec]
  refine ⟨⟨⟨by omega, by omega⟩, trivial⟩, by omega, ?_⟩
  unfold grid
  simp only [Nat.cast_zero, zero_div]
  positivity

theorem nObs_le (T : ℕ) (rec : ℕ → ℕ × ℕ) (t ℓ i : ℕ) : nObs T rec ℓ i t ≤ t - 1 := by
  unfold nObs obsCount levelSet
  calc _ ≤ ((Finset.Icc 1 (t - 1)).filter (fun s => (rec s).1 = ℓ)).card :=
        Finset.card_filter_le _ _
    _ ≤ (Finset.Icc 1 (t - 1)).card := Finset.card_filter_le _ _
    _ = t - 1 := by simp

theorem width_ge (T : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) (rec : ℕ → ℕ × ℕ) (Y : ℕ → ℝ) (ℓ i t : ℕ) :
    γ * (logFactor T / (nObs T rec ℓ i t : ℝ)) ≤ width T γ rec Y ℓ i t := by
  unfold width
  apply mul_le_mul_of_nonneg_left _ hγ
  have := Real.sqrt_nonneg (2 * logFactor T * ∑ j ∈ Finset.Ico i (numGrid T),
          (1 / (nObs T rec ℓ j t : ℝ)) * (phat0 T rec Y j + γ * logFactor T / (numGrid T : ℝ)))
  linarith

/-- The exploration test succeeds at the last level `L`, so the inner loop always breaks. -/
theorem breakLevels_nonempty (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (V Y : ℕ → ℝ) (t : ℕ) (ht0 : initLength T < t) (htT : t ≤ T) :
    (breakLevels T γ (record T γ sel V Y) Y V t).Nonempty := by
  have hT2 := two_le_of_init T t ht0 htT
  have hL := numLevels_pos T hT2
  have hK := numGrid_pos T (by omega)
  refine ⟨numLevels T, ?_⟩
  unfold breakLevels
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨hL, le_refl _⟩, ?_⟩
  obtain ⟨i, hi⟩ := cand_nonempty T γ Y V (record T γ sel V Y) t hK (numLevels T - 1)
  refine ⟨i, ?_⟩
  unfold exploreSet
  rw [Finset.mem_filter]
  refine ⟨hi, ?_⟩
  have hn1 := nObs_pos T γ sel V Y t ht0 htT (numLevels T) i (le_refl _)
  have hn2 := nObs_le T (record T γ sel V Y) t (numLevels T) i
  have hpow := le_two_pow_numLevels T
  set n := nObs T (record T γ sel V Y) (numLevels T) i t
  have hnlt : (n : ℝ) < (2 : ℝ) ^ numLevels T := by
    have : n < 2 ^ numLevels T := by omega
    exact_mod_cast this
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlog := one_le_logFactor T hT2
  have hw := width_ge T γ (by linarith) (record T γ sel V Y) Y (numLevels T) i t
  have h2 : (1 / 2 : ℝ) ^ numLevels T = 1 / (2 : ℝ) ^ numLevels T := by
    rw [div_pow, one_pow]
  have hkey : 1 / (2 : ℝ) ^ numLevels T < γ * (logFactor T / n) := by
    rw [div_lt_iff₀ (by positivity)]
    have : γ * (logFactor T / n) * 2 ^ numLevels T ≥ 3 * (1 / n) * n := by
      have h3 : γ * (logFactor T / n) ≥ 3 * (1 / n) := by
        rw [mul_div_assoc']
        rw [ge_iff_le, mul_one_div]
        apply div_le_div_of_nonneg_right _ (by linarith)
        nlinarith
      have : (0 : ℝ) ≤ 3 * (1 / n) := by positivity
      nlinarith
    have h4 : 3 * (1 / (n : ℝ)) * n = 3 := by field_simp
    linarith
  linarith

/-- The specification of the round-`t` decision for `T₀ < t ≤ T`. -/
theorem decide_spec (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : IsSelectionRule sel) (V Y : ℕ → ℝ) (t : ℕ) (ht0 : initLength T < t) (htT : t ≤ T) :
    let R := record T γ sel V Y
    (1 ≤ (R t).1 ∧ (R t).1 ≤ numLevels T) ∧
    (R t).2 ∈ exploreSet T γ R Y V (R t).1 t ∧
    (∀ ℓ', 1 ≤ ℓ' → ℓ' < (R t).1 → ∀ i ∈ cand T γ R Y V t (ℓ' - 1),
      width T γ R Y ℓ' i t ≤ (1 / 2 : ℝ) ^ ℓ') := by
  intro R
  have hne := breakLevels_nonempty T γ hγ sel V Y t ht0 htT
  have hRt : R t = ((breakLevels T γ R Y V t).min' hne,
      sel t ((breakLevels T γ R Y V t).min' hne)
        (exploreSet T γ R Y V ((breakLevels T γ R Y V t).min' hne) t)) := by
    show record T γ sel V Y t = _
    rw [record_gt T γ sel V Y t ht0]
    unfold decideRound
    rw [dif_pos hne]
  have hmem := Finset.min'_mem _ hne
  have hmem' : ((breakLevels T γ R Y V t).min' hne) ∈ Finset.Icc 1 (numLevels T) ∧
      (exploreSet T γ R Y V ((breakLevels T γ R Y V t).min' hne) t).Nonempty := by
    have := hmem
    unfold breakLevels at this
    exact Finset.mem_filter.mp this
  rw [Finset.mem_Icc] at hmem'
  rw [hRt]
  refine ⟨hmem'.1, hsel _ _ _ hmem'.2, ?_⟩
  intro ℓ' h1 h2 i hi
  by_contra hcon
  push Not at hcon
  have : ℓ' ∈ breakLevels T γ R Y V t := by
    unfold breakLevels
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨h1, by simp only at h2; omega⟩, ⟨i, ?_⟩⟩
    unfold exploreSet
    rw [Finset.mem_filter]
    exact ⟨hi, hcon⟩
  have := Finset.min'_le _ _ this
  simp only at h2
  omega

theorem exploreSet_subset (T : ℕ) (γ : ℝ) (rec : ℕ → ℕ × ℕ) (Y V : ℕ → ℝ) (ℓ t : ℕ) :
    exploreSet T γ rec Y V ℓ t ⊆ cand T γ rec Y V t (ℓ - 1) := by
  unfold exploreSet; exact Finset.filter_subset _ _

/-! ### Rewards -/

theorem cdf_nonneg (μG : Measure ℝ) (x : ℝ) : 0 ≤ FirstPriceLearning.Stochastic.cdf μG x :=
  ENNReal.toReal_nonneg

theorem cdf_le_one (μG : Measure ℝ) [IsProbabilityMeasure μG] (x : ℝ) :
    FirstPriceLearning.Stochastic.cdf μG x ≤ 1 := by
  unfold FirstPriceLearning.Stochastic.cdf
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

theorem cdf_mono (μG : Measure ℝ) [IsProbabilityMeasure μG] {x y : ℝ} (h : x ≤ y) :
    FirstPriceLearning.Stochastic.cdf μG x ≤ FirstPriceLearning.Stochastic.cdf μG y := by
  unfold FirstPriceLearning.Stochastic.cdf
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.mpr h))

theorem paperSeq_mem {T : ℕ} (v : Fin T → ℝ) (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    paperSeq v t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold paperSeq
  split_ifs with h
  · exact hv _
  · exact ⟨le_refl _, zero_le_one⟩

theorem grid_mem (K i : ℕ) (hi : i ≤ K) : grid K i ∈ Set.Icc (0 : ℝ) 1 := by
  unfold grid
  rcases Nat.eq_zero_or_pos K with h | h
  · subst h; simp
  · refine ⟨by positivity, ?_⟩
    rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast hi

theorem gridReward_le_one {T : ℕ} (μG : Measure ℝ) [IsProbabilityMeasure μG] (v : Fin T → ℝ)
    (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1) (i t : ℕ) (hi : i ≤ numGrid T) :
    gridReward μG v i t ≤ 1 := by
  unfold gridReward FirstPriceLearning.Stochastic.expReward
  have h1 := paperSeq_mem v hv t
  have h2 := grid_mem (numGrid T) i hi
  have h3 := cdf_nonneg μG (grid (numGrid T) i)
  have h4 := cdf_le_one μG (grid (numGrid T) i)
  obtain ⟨a1, a2⟩ := h1; obtain ⟨b1, b2⟩ := h2
  nlinarith

theorem gridReward_ge_neg_one {T : ℕ} (μG : Measure ℝ) [IsProbabilityMeasure μG] (v : Fin T → ℝ)
    (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1) (i t : ℕ) (hi : i ≤ numGrid T) :
    -1 ≤ gridReward μG v i t := by
  unfold gridReward FirstPriceLearning.Stochastic.expReward
  have h1 := paperSeq_mem v hv t
  have h2 := grid_mem (numGrid T) i hi
  have h3 := cdf_nonneg μG (grid (numGrid T) i)
  have h4 := cdf_le_one μG (grid (numGrid T) i)
  obtain ⟨a1, a2⟩ := h1; obtain ⟨b1, b2⟩ := h2
  nlinarith

theorem gridReward_nonneg_zero {T : ℕ} (μG : Measure ℝ) (v : Fin T → ℝ)
    (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    0 ≤ gridReward μG v 0 t := by
  unfold gridReward FirstPriceLearning.Stochastic.expReward
  have h1 := paperSeq_mem v hv t
  have h3 := cdf_nonneg μG (grid (numGrid T) 0)
  simp only [grid, Nat.cast_zero, zero_div, sub_zero]
  exact mul_nonneg h1.1 (by simpa [grid] using h3)

theorem exists_gridOracle {T : ℕ} (μG : Measure ℝ) (v : Fin T → ℝ) (t : ℕ)
    (hK : 1 ≤ numGrid T) :
    ∃ istar < numGrid T, (∀ i < numGrid T, gridReward μG v i t ≤ gridReward μG v istar t) ∧
      gridOracle μG v t = gridReward μG v istar t := by
  have : Nonempty (Fin (numGrid T)) := ⟨⟨0, hK⟩⟩
  obtain ⟨j, hj⟩ := Finite.exists_max (fun i : Fin (numGrid T) => gridReward μG v i t)
  refine ⟨j.val, j.isLt, fun i hi => hj ⟨i, hi⟩, ?_⟩
  unfold gridOracle
  apply le_antisymm
  · exact ciSup_le hj
  · exact le_ciSup (f := fun i : Fin (numGrid T) => gridReward μG v i t) (Finite.bddAbove_range _) j

theorem gridOracle_le_one {T : ℕ} (μG : Measure ℝ) [IsProbabilityMeasure μG] (v : Fin T → ℝ)
    (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) (hK : 1 ≤ numGrid T) :
    gridOracle μG v t ≤ 1 := by
  obtain ⟨istar, hlt, -, heq⟩ := exists_gridOracle μG v t hK
  rw [heq]; exact gridReward_le_one μG v hv istar t hlt.le

end FPA2Core


open MeasureTheory

namespace FPA2Core

open FirstPriceLearning.Adversarial

/-! ### Generic measurability tools -/

theorem meas_bind {X C β : Type*} [MeasurableSpace X] [MeasurableSpace C] [Countable C]
    [MeasurableSingletonClass C] [MeasurableSpace β] {c : X → C} (hc : Measurable c)
    {F : C → X → β} (hF : ∀ a, Measurable (F a)) : Measurable (fun x => F (c x) x) := by
  have h : Measurable (fun p : X × C => F p.2 p.1) :=
    measurable_from_prod_countable_left (fun y => hF y)
  exact h.comp (measurable_id.prodMk hc)

theorem meas_filter {X : Type*} [MeasurableSpace X] (B : Finset ℕ) (p : ℕ → X → Prop)
    [∀ x, DecidablePred (fun i => p i x)]
    (hp : ∀ i ∈ B, MeasurableSet {x | p i x}) :
    Measurable (fun x => B.filter (fun i => p i x)) := by
  rw [measurable_finset_iff]
  intro a
  rw [← measurableSet_setOfPred]
  by_cases ha : a ∈ B
  · have : {x | a ∈ B.filter (fun i => p i x)} = {x | p a x} := by
      ext x; simp [Finset.mem_filter, ha]
    rw [this]; exact hp a ha
  · have : {x | a ∈ B.filter (fun i => p i x)} = ∅ := by
      ext x; simp [Finset.mem_filter, ha]
    rw [this]; exact MeasurableSet.empty

theorem meas_of_finset {X β : Type*} [MeasurableSpace X] [MeasurableSpace β] {c : X → Finset ℕ}
    (hc : Measurable c) (g : Finset ℕ → β) : Measurable (fun x => g (c x)) :=
  (measurable_of_countable g).comp hc

theorem measSet_of_finset {X : Type*} [MeasurableSpace X] {c : X → Finset ℕ}
    (hc : Measurable c) (P : Finset ℕ → Prop) : MeasurableSet {x | P (c x)} :=
  hc (Set.to_countable {S : Finset ℕ | P S}).measurableSet

/-! ### Measurability of one round for a fixed past record -/

section fixedrec

variable {X : Type*} [MeasurableSpace X] (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
  (V Y : X → ℕ → ℝ) (hV : ∀ s, Measurable (fun x => V x s))
  (hY : ∀ s, Measurable (fun x => Y x s)) (rec : ℕ → ℕ × ℕ) (t : ℕ)

include hY in
theorem meas_ind (s : ℕ) (a b : ℝ) :
    Measurable (fun x => if a < Y x s ∧ Y x s ≤ b then (1 : ℝ) else 0) := by
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_lt measurable_const (hY s)).inter
    (measurableSet_le (hY s) measurable_const)

include hY in
theorem meas_phat0 (j : ℕ) : Measurable (fun x => phat0 T rec (Y x) j) := by
  unfold phat0
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro s _
  exact meas_ind Y hY s _ _

include hY in
theorem meas_width (ℓ i : ℕ) : Measurable (fun x => width T γ rec (Y x) ℓ i t) := by
  unfold width
  apply Measurable.const_mul
  apply Measurable.add _ measurable_const
  apply Measurable.sqrt
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro j _
  apply Measurable.const_mul
  exact (meas_phat0 T Y hY rec j).add measurable_const

include hY in
theorem meas_phat (ℓ i : ℕ) : Measurable (fun x => phat T rec (Y x) ℓ i t) := by
  unfold phat
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro s _
  exact measurable_const.mul (meas_ind Y hY s _ _)

include hV hY in
theorem meas_rhat (ℓ i : ℕ) : Measurable (fun x => rhat T rec (Y x) (V x) ℓ i t) := by
  unfold rhat
  apply Measurable.mul ((hV t).sub measurable_const)
  apply measurable_const.sub
  apply Finset.measurable_sum
  intro j _
  exact meas_phat T Y hY rec t ℓ j

include hV hY in
theorem meas_cand (ℓ : ℕ) : Measurable (fun x => cand T γ rec (Y x) (V x) t ℓ) := by
  induction ℓ with
  | zero => exact measurable_const
  | succ ℓ ih =>
    have hucb : ∀ j, Measurable (fun x => rhat T rec (Y x) (V x) (ℓ + 1) j t +
        width T γ rec (Y x) (ℓ + 1) j t) := fun j =>
      (meas_rhat T V Y hV hY rec t (ℓ + 1) j).add (meas_width T γ Y hY rec t (ℓ + 1) j)
    have hF : ∀ B : Finset ℕ, Measurable (fun x =>
        B.filter (fun i => (if h : B.Nonempty then B.sup' h (fun j =>
          rhat T rec (Y x) (V x) (ℓ + 1) j t + width T γ rec (Y x) (ℓ + 1) j t) else 0)
          - 2 * (1 / 2 : ℝ) ^ (ℓ + 1) ≤
          rhat T rec (Y x) (V x) (ℓ + 1) i t + width T γ rec (Y x) (ℓ + 1) i t)) := by
      intro B
      apply meas_filter
      intro i _
      apply measurableSet_le _ (hucb i)
      apply Measurable.sub _ measurable_const
      by_cases hB : B.Nonempty
      · simp only [dif_pos hB]
        have := Finset.measurable_sup' hB (f := fun j x => rhat T rec (Y x) (V x) (ℓ + 1) j t +
          width T γ rec (Y x) (ℓ + 1) j t) (fun j _ => hucb j)
        convert this using 1
        funext x
        rw [Finset.sup'_apply]
      · simp only [dif_neg hB]; exact measurable_const
    exact meas_bind ih hF

include hV hY in
theorem meas_exploreSet (ℓ : ℕ) : Measurable (fun x => exploreSet T γ rec (Y x) (V x) ℓ t) := by
  unfold exploreSet
  have hF : ∀ B : Finset ℕ, Measurable (fun x =>
      B.filter (fun i => (1 / 2 : ℝ) ^ ℓ < width T γ rec (Y x) ℓ i t)) := by
    intro B
    apply meas_filter
    intro i _
    exact measurableSet_lt measurable_const (meas_width T γ Y hY rec t ℓ i)
  exact meas_bind (meas_cand T γ V Y hV hY rec t (ℓ - 1)) hF

include hV hY in
theorem meas_breakLevels : Measurable (fun x => breakLevels T γ rec (Y x) (V x) t) := by
  unfold breakLevels
  apply meas_filter
  intro ℓ _
  exact measSet_of_finset (meas_exploreSet T γ V Y hV hY rec t ℓ) (fun S => S.Nonempty)

include hV hY in
theorem meas_decideRound : Measurable (fun x => decideRound T γ sel rec (Y x) (V x) t) := by
  unfold decideRound
  have hF : ∀ BL : Finset ℕ, Measurable (fun x =>
      if h : BL.Nonempty then (BL.min' h, sel t (BL.min' h)
        (exploreSet T γ rec (Y x) (V x) (BL.min' h) t)) else (numLevels T, 0)) := by
    intro BL
    by_cases h : BL.Nonempty
    · simp only [dif_pos h]
      exact measurable_const.prodMk
        (meas_of_finset (meas_exploreSet T γ V Y hV hY rec t (BL.min' h)) (sel t (BL.min' h)))
    · simp only [dif_neg h]; exact measurable_const
  exact meas_bind (meas_breakLevels T γ V Y hV hY rec t) hF

end fixedrec

/-! ### Measurability of the record -/

theorem meas_record {X : Type*} [MeasurableSpace X] (T : ℕ) (γ : ℝ)
    (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (V Y : X → ℕ → ℝ) (hV : ∀ s, Measurable (fun x => V x s))
    (hY : ∀ s, Measurable (fun x => Y x s)) (n : ℕ) :
    Measurable (fun x => record T γ sel (V x) (Y x) n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n ≤ initLength T
    · simp only [record_le T γ sel _ _ n hn]; exact measurable_const
    · push Not at hn
      let ext : (Fin n → ℕ × ℕ) → ℕ → ℕ × ℕ := fun h s => if hs : s < n then h ⟨s, hs⟩ else (0, 0)
      have hH : Measurable (fun x => (fun s : Fin n => record T γ sel (V x) (Y x) s.val)) :=
        measurable_pi_lambda _ (fun s => ih s.val s.isLt)
      have hF : ∀ h : Fin n → ℕ × ℕ, Measurable (fun x =>
          decideRound T γ sel (ext h) (Y x) (V x) n) :=
        fun h => meas_decideRound T γ sel V Y hV hY (ext h) n
      have := meas_bind hH hF
      convert this using 1
      funext x
      rw [record_gt T γ sel _ _ n hn]
      apply decideRound_congr T γ sel _ _ _ _ n hn
      intro s hs
      simp [ext, hs]

/-! ### Measurability of the bidding rule -/

theorem meas_mlRule (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (t : Fin T) :
    Measurable (fun p : (Fin (t.val + 1) → ℝ) × (Fin t.val → ℝ) =>
      mlRule T γ sel t p.1 p.2) := by
  unfold mlRule
  have hV : ∀ s, Measurable (fun p : (Fin (t.val + 1) → ℝ) × (Fin t.val → ℝ) =>
      (fun s => if h : 1 ≤ s ∧ s ≤ t.val + 1 then p.1 ⟨s - 1, by omega⟩ else 0) s) := by
    intro s
    by_cases h : 1 ≤ s ∧ s ≤ t.val + 1
    · simp only [dif_pos h]
      exact (measurable_pi_apply _).comp measurable_fst
    · simp only [dif_neg h]; exact measurable_const
  have hY : ∀ s, Measurable (fun p : (Fin (t.val + 1) → ℝ) × (Fin t.val → ℝ) =>
      (fun s => if h : 1 ≤ s ∧ s ≤ t.val then p.2 ⟨s - 1, by omega⟩ else 0) s) := by
    intro s
    by_cases h : 1 ≤ s ∧ s ≤ t.val
    · simp only [dif_pos h]
      exact (measurable_pi_apply _).comp measurable_snd
    · simp only [dif_neg h]; exact measurable_const
  have := meas_record T γ sel _ _ hV hY (t.val + 1)
  exact (measurable_of_countable (fun r : ℕ × ℕ => grid (numGrid T) r.2)).comp this

/-- The bids of any rule with measurable rounds are measurable functions of the HOBs. -/
theorem meas_runBidsNat {T : ℕ} (f : BidRule T)
    (hf : ∀ t : Fin T, Measurable (fun p : (Fin (t.val + 1) → ℝ) × (Fin t.val → ℝ) =>
      f t p.1 p.2))
    (v : Fin T → ℝ) (n : ℕ) : Measurable (fun m : Fin T → ℝ => runBidsNat f v m n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have heq : (fun m : Fin T → ℝ => runBidsNat f v m n) = fun m =>
        if h : n < T then
          f ⟨n, h⟩ (fun s => v ⟨s.val, by omega⟩)
            (fun s => max (runBidsNat f v m s.val) (m ⟨s.val, by omega⟩))
        else 0 := by
      funext m; rw [runBidsNat]
    rw [heq]
    by_cases h : n < T
    · simp only [dif_pos h]
      have hg : Measurable (fun m : Fin T → ℝ => ((fun s : Fin (n + 1) => v ⟨s.val, by omega⟩),
          (fun s : Fin n => max (runBidsNat f v m s.val) (m ⟨s.val, by omega⟩)))) := by
        apply measurable_const.prodMk
        apply measurable_pi_lambda
        intro s
        exact (ih s.val s.isLt).max (measurable_pi_apply _)
      exact (hf ⟨n, h⟩).comp hg
    · simp only [dif_neg h]; exact measurable_const

theorem cdf_measurable (μG : Measure ℝ) [IsProbabilityMeasure μG] :
    Measurable (FirstPriceLearning.Stochastic.cdf μG) :=
  Monotone.measurable (fun _ _ h => cdf_mono μG h)

theorem meas_regret {T : ℕ} (μG : Measure ℝ) [IsProbabilityMeasure μG] (v : Fin T → ℝ)
    (f : BidRule T)
    (hf : ∀ t : Fin T, Measurable (fun p : (Fin (t.val + 1) → ℝ) × (Fin t.val → ℝ) =>
      f t p.1 p.2)) :
    Measurable (fun m : Fin T → ℝ => regret μG v (runBids f v m)) := by
  unfold regret
  apply Finset.measurable_sum
  intro t _
  apply measurable_const.sub
  unfold FirstPriceLearning.Stochastic.expReward
  have hb : Measurable (fun m : Fin T → ℝ => runBids f v m t) := meas_runBidsNat f hf v t.val
  exact (measurable_const.sub hb).mul ((cdf_measurable μG).comp hb)

end FPA2Core


open MeasureTheory

namespace FPA2Core

open FirstPriceLearning.Adversarial

/-! ### Locality of the record in the data -/

section congr2

variable (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (y y' v v' : ℕ → ℝ)
  (rec rec' : ℕ → ℕ × ℕ) (t : ℕ)

theorem phat0_congr2 (ht : initLength T < t) (h : ∀ s, s < t → rec s = rec' s)
    (hy : ∀ s, 1 ≤ s → s < t → y s = y' s) (j : ℕ) :
    phat0 T rec y j = phat0 T rec' y' j := by
  rw [phat0_congr T y rec rec' t ht h]
  unfold phat0
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  unfold levelSet at hs
  simp only [Finset.mem_filter, Finset.mem_Icc] at hs
  rw [hy s hs.1.1 (by omega)]

theorem width_congr2 (ht : initLength T < t) (h : ∀ s, s < t → rec s = rec' s)
    (hy : ∀ s, 1 ≤ s → s < t → y s = y' s) (ℓ i : ℕ) :
    width T γ rec y ℓ i t = width T γ rec' y' ℓ i t := by
  unfold width
  have h1 : 1 ≤ t := by omega
  simp only [nObs_congr T rec rec' t h1 h, phat0_congr2 T y y' rec rec' t ht h hy]

theorem phat_congr2 (ht : 1 ≤ t) (h : ∀ s, s < t → rec s = rec' s)
    (hy : ∀ s, 1 ≤ s → s < t → y s = y' s) (ℓ i : ℕ) :
    phat T rec y ℓ i t = phat T rec' y' ℓ i t := by
  rw [phat_congr T y rec rec' t ht h]
  unfold phat
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  unfold levelSet at hs
  simp only [Finset.mem_filter, Finset.mem_Icc] at hs
  rw [hy s hs.1.1 (by omega)]

theorem rhat_congr2 (ht : 1 ≤ t) (h : ∀ s, s < t → rec s = rec' s)
    (hy : ∀ s, 1 ≤ s → s < t → y s = y' s) (hv : v t = v' t) (ℓ i : ℕ) :
    rhat T rec y v ℓ i t = rhat T rec' y' v' ℓ i t := by
  unfold rhat
  simp only [phat_congr2 T y y' rec rec' t ht h hy, hv]

theorem cand_congr2 (ht : initLength T < t) (h : ∀ s, s < t → rec s = rec' s)
    (hy : ∀ s, 1 ≤ s → s < t → y s = y' s) (hv : v t = v' t) (ℓ : ℕ) :
    cand T γ rec y v t ℓ = cand T γ rec' y' v' t ℓ := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    have h1 : 1 ≤ t := by omega
    ext i
    rw [mem_cand_succ, mem_cand_succ, ih]
    simp only [rhat_congr2 T y y' v v' rec rec' t h1 h hy hv,
      width_congr2 T γ y y' rec rec' t ht h hy]

theorem exploreSet_congr2 (ht : initLength T < t) (h : ∀ s, s < t → rec s = rec' s)
    (hy : ∀ s, 1 ≤ s → s < t → y s = y' s) (hv : v t = v' t) (ℓ : ℕ) :
    exploreSet T γ rec y v ℓ t = exploreSet T γ rec' y' v' ℓ t := by
  unfold exploreSet
  simp only [cand_congr2 T γ y y' v v' rec rec' t ht h hy hv,
    width_congr2 T γ y y' rec rec' t ht h hy]

theorem breakLevels_congr2 (ht : initLength T < t) (h : ∀ s, s < t → rec s = rec' s)
    (hy : ∀ s, 1 ≤ s → s < t → y s = y' s) (hv : v t = v' t) :
    breakLevels T γ rec y v t = breakLevels T γ rec' y' v' t := by
  unfold breakLevels
  simp only [exploreSet_congr2 T γ y y' v v' rec rec' t ht h hy hv]

theorem decideRound_congr2 (ht : initLength T < t) (h : ∀ s, s < t → rec s = rec' s)
    (hy : ∀ s, 1 ≤ s → s < t → y s = y' s) (hv : v t = v' t) :
    decideRound T γ sel rec y v t = decideRound T γ sel rec' y' v' t := by
  unfold decideRound
  simp only [breakLevels_congr2 T γ y y' v v' rec rec' t ht h hy hv,
    exploreSet_congr2 T γ y y' v v' rec rec' t ht h hy hv]

end congr2

theorem record_local (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (V V' Y Y' : ℕ → ℝ) (n : ℕ)
    (hV : ∀ s, 1 ≤ s → s ≤ n → V s = V' s) (hY : ∀ s, 1 ≤ s → s < n → Y s = Y' s) :
    record T γ sel V Y n = record T γ sel V' Y' n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n ≤ initLength T
    · rw [record_le T γ sel _ _ n hn, record_le T γ sel _ _ n hn]
    · push Not at hn
      rw [record_gt T γ sel _ _ n hn, record_gt T γ sel _ _ n hn]
      apply decideRound_congr2 T γ sel _ _ _ _ _ _ n hn
      · intro s hs
        exact ih s hs (fun r h1 h2 => hV r h1 (by omega)) (fun r h1 h2 => hY r h1 (by omega))
      · exact fun s h1 h2 => hY s h1 h2
      · exact hV n (by omega) le_rfl

/-- The bid of ML-IS-UCB in round `t` is the grid point of the run record at paper time `t+1`. -/
theorem mlBids_eq (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v m : Fin T → ℝ) (t : Fin T) :
    mlBids T γ sel v m t = grid (numGrid T) (runIndex T γ sel v m (t.val + 1)) := by
  unfold mlBids runBids
  rw [runBidsNat]
  simp only [dif_pos t.isLt]
  unfold mlRule runIndex runRecord
  congr 2
  apply record_local
  · intro s h1 h2
    unfold paperSeq
    rw [dif_pos ⟨h1, h2⟩, dif_pos ⟨h1, by omega⟩]
  · intro s h1 h2
    unfold paperSeq
    rw [dif_pos ⟨h1, by omega⟩, dif_pos ⟨h1, by omega⟩]
    rfl

theorem record_idx_le_gen (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : IsSelectionRule sel) (V Y : ℕ → ℝ) (n : ℕ) :
    (record T γ sel V Y n).2 ≤ numGrid T := by
  by_cases hn : n ≤ initLength T
  · rw [record_le T γ sel V Y n hn]; exact Nat.zero_le _
  · push Not at hn
    rw [record_gt T γ sel V Y n hn]
    unfold decideRound
    split_ifs with h
    · have hmem := Finset.min'_mem _ h
      have hne : (exploreSet T γ (record T γ sel V Y) Y V
          ((breakLevels T γ (record T γ sel V Y) Y V n).min' h) n).Nonempty := by
        have := hmem
        unfold breakLevels at this
        exact (Finset.mem_filter.mp this).2
      have h1 := hsel n ((breakLevels T γ (record T γ sel V Y) Y V n).min' h) _ hne
      have := cand_subset_range T γ Y V (record T γ sel V Y) n _
        (exploreSet_subset T γ _ Y V _ n h1)
      exact (Finset.mem_range.mp this).le
    · exact Nat.zero_le _

theorem mlBids_mem (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (hsel : IsSelectionRule sel)
    (v m : Fin T → ℝ) (t : Fin T) : mlBids T γ sel v m t ∈ Set.Icc (0 : ℝ) 1 := by
  rw [mlBids_eq]
  exact grid_mem _ _ (record_idx_le_gen T γ sel hsel _ _ _)

/-! ### The oracle -/

theorem expReward_le_one (μG : Measure ℝ) [IsProbabilityMeasure μG] (x b : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    FirstPriceLearning.Stochastic.expReward μG x b ≤ 1 := by
  unfold FirstPriceLearning.Stochastic.expReward
  have h3 := cdf_nonneg μG b
  have h4 := cdf_le_one μG b
  obtain ⟨a1, a2⟩ := hx; obtain ⟨b1, b2⟩ := hb
  nlinarith

theorem expReward_ge (μG : Measure ℝ) [IsProbabilityMeasure μG] (x b : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    -1 ≤ FirstPriceLearning.Stochastic.expReward μG x b := by
  unfold FirstPriceLearning.Stochastic.expReward
  have h3 := cdf_nonneg μG b
  have h4 := cdf_le_one μG b
  obtain ⟨a1, a2⟩ := hx; obtain ⟨b1, b2⟩ := hb
  nlinarith

theorem oracle_bdd (μG : Measure ℝ) [IsProbabilityMeasure μG] (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    BddAbove (Set.range fun b : Set.Icc (0 : ℝ) 1 =>
      FirstPriceLearning.Stochastic.expReward μG x b) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨b, rfl⟩
  exact expReward_le_one μG x b hx b.2

theorem le_oracle (μG : Measure ℝ) [IsProbabilityMeasure μG] (x b : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    FirstPriceLearning.Stochastic.expReward μG x b ≤ FirstPriceLearning.Stochastic.oracle μG x :=
  le_ciSup (f := fun b : Set.Icc (0 : ℝ) 1 => FirstPriceLearning.Stochastic.expReward μG x b)
    (oracle_bdd μG x hx) ⟨b, hb⟩

theorem oracle_le_one (μG : Measure ℝ) [IsProbabilityMeasure μG] (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : FirstPriceLearning.Stochastic.oracle μG x ≤ 1 := by
  unfold FirstPriceLearning.Stochastic.oracle
  have : Nonempty (Set.Icc (0 : ℝ) 1) := ⟨⟨0, by norm_num, by norm_num⟩⟩
  exact ciSup_le (fun b => expReward_le_one μG x b hx b.2)

/-- Quantization: the best grid bid loses at most `1/K` against the best bid in `[0,1]`. -/
theorem oracle_le_grid (μG : Measure ℝ) [IsProbabilityMeasure μG] (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (K : ℕ) (hK : 1 ≤ K) :
    FirstPriceLearning.Stochastic.oracle μG x ≤
      (⨆ i : Fin K, FirstPriceLearning.Stochastic.expReward μG x (grid K i)) + 1 / K := by
  have hne : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have hbdd : BddAbove (Set.range fun i : Fin K =>
      FirstPriceLearning.Stochastic.expReward μG x (grid K i)) := Finite.bddAbove_range _
  set gO := ⨆ i : Fin K, FirstPriceLearning.Stochastic.expReward μG x (grid K i) with hgO
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hg0 : 0 ≤ gO := by
    have : FirstPriceLearning.Stochastic.expReward μG x (grid K (⟨0, hK⟩ : Fin K)) ≤ gO :=
      le_ciSup hbdd ⟨0, hK⟩
    have h0 : 0 ≤ FirstPriceLearning.Stochastic.expReward μG x (grid K (⟨0, hK⟩ : Fin K)) := by
      unfold FirstPriceLearning.Stochastic.expReward grid
      simp only [Nat.cast_zero, zero_div, sub_zero]
      exact mul_nonneg hx.1 (cdf_nonneg μG 0)
    linarith
  unfold FirstPriceLearning.Stochastic.oracle
  have : Nonempty (Set.Icc (0 : ℝ) 1) := ⟨⟨0, by norm_num, by norm_num⟩⟩
  apply ciSup_le
  rintro ⟨b, hb0, hb1⟩
  simp only
  set i := ⌈b * K⌉₊ with hi
  have hi1 : b * K ≤ i := Nat.le_ceil _
  have hi2 : (i : ℝ) < b * K + 1 := Nat.ceil_lt_add_one (by positivity)
  have hbi : b ≤ (i : ℝ) / K := by rw [le_div_iff₀ hKpos]; exact hi1
  have hib : (i : ℝ) / K < b + 1 / K := by
    rw [div_lt_iff₀ hKpos]; field_simp; linarith
  have hGb := cdf_nonneg μG b
  have hGb1 := cdf_le_one μG b
  by_cases hcase : i < K ∧ (i : ℝ) / K ≤ x
  · have hgrid : grid K (⟨i, hcase.1⟩ : Fin K) = (i : ℝ) / K := rfl
    have hle : FirstPriceLearning.Stochastic.expReward μG x (grid K (⟨i, hcase.1⟩ : Fin K)) ≤ gO :=
      le_ciSup hbdd ⟨i, hcase.1⟩
    rw [hgrid] at hle
    have hmono := cdf_mono μG hbi
    unfold FirstPriceLearning.Stochastic.expReward at hle ⊢
    have h1 : (x - (i : ℝ) / K) * FirstPriceLearning.Stochastic.cdf μG b ≤
        (x - (i : ℝ) / K) * FirstPriceLearning.Stochastic.cdf μG ((i : ℝ) / K) :=
      mul_le_mul_of_nonneg_left hmono (by linarith [hcase.2])
    have h2 : (x - b) * FirstPriceLearning.Stochastic.cdf μG b ≤
        (x - (i : ℝ) / K) * FirstPriceLearning.Stochastic.cdf μG b +
          1 / K * FirstPriceLearning.Stochastic.cdf μG b := by
      have : (x - b) ≤ (x - (i : ℝ) / K) + 1 / K := by linarith
      nlinarith
    have h3 : 1 / (K : ℝ) * FirstPriceLearning.Stochastic.cdf μG b ≤ 1 / K := by
      have : (0 : ℝ) ≤ 1 / K := by positivity
      nlinarith
    linarith
  · have hsmall : x - b < 1 / K := by
      rcases not_and_or.mp hcase with h | h
      · push Not at h
        have : (K : ℝ) ≤ i := by exact_mod_cast h
        have : 1 ≤ (i : ℝ) / K := by rw [le_div_iff₀ hKpos]; linarith
        linarith [hx.2]
      · push Not at h
        linarith
    unfold FirstPriceLearning.Stochastic.expReward
    have : (x - b) * FirstPriceLearning.Stochastic.cdf μG b ≤ 1 / K := by
      rcases le_or_gt 0 (x - b) with h | h
      · have : (x - b) * FirstPriceLearning.Stochastic.cdf μG b ≤ x - b := by nlinarith
        linarith
      · have : (x - b) * FirstPriceLearning.Stochastic.cdf μG b ≤ 0 := by nlinarith
        have : (0 : ℝ) ≤ 1 / K := by positivity
        linarith
    linarith

end FPA2Core


open MeasureTheory

namespace FPA2Core

open FirstPriceLearning.Adversarial

theorem sum_fin_shift (T : ℕ) (h : ℕ → ℝ) :
    ∑ t : Fin T, h (t.val + 1) = ∑ s ∈ Finset.Icc 1 T, h s := by
  rw [Fin.sum_univ_eq_sum_range (fun t => h (t + 1)) T]
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

theorem paperSeq_succ {T : ℕ} (v : Fin T → ℝ) (t : Fin T) : paperSeq v (t.val + 1) = v t := by
  unfold paperSeq
  rw [dif_pos ⟨by omega, t.isLt⟩]
  rfl

/-- On the event of Lemma 7 the regret is at most `(L+2)K + 80 γ^{3/2} log(LKT)(1+log T) L √T`. -/
theorem regret_good (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : IsSelectionRule sel) (v : Fin T → ℝ) (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (m : Fin T → ℝ) (hT : 1 ≤ T)
    (hgood : ∀ i < numGrid T, ∀ ℓ ∈ Finset.Icc 1 (numLevels T), ∀ t : ℕ,
            initLength T < t → t ≤ T →
              |runRhat T γ sel v m ℓ i t - gridReward μG v i t| ≤ runWidth T γ sel v m ℓ i t ∧
              runWidth T γ sel v m ℓ i t ≤ widthBound T γ sel μG v m ℓ i t) :
    regret μG v (mlBids T γ sel v m) ≤
      ((numLevels T : ℝ) + 2) * (numGrid T : ℝ)
        + 80 * γ ^ ((3 : ℝ) / 2) * logFactor T * (1 + Real.log T) * (numLevels T : ℝ)
          * Real.sqrt T := by
  have hK := numGrid_pos T hT
  have hKpos : (0 : ℝ) < numGrid T := by exact_mod_cast hK
  set K := numGrid T with hKdef
  -- rewrite the regret on paper times
  have hdecomp : regret μG v (mlBids T γ sel v m) =
      ∑ s ∈ Finset.Icc 1 T, (FirstPriceLearning.Stochastic.oracle μG (paperSeq v s)
        - gridOracle μG v s)
      + ∑ s ∈ Finset.Icc 1 T, (gridOracle μG v s - gridReward μG v (runIndex T γ sel v m s) s) := by
    rw [← Finset.sum_add_distrib, ← sum_fin_shift T]
    unfold regret
    apply Finset.sum_congr rfl
    intro t _
    rw [mlBids_eq, paperSeq_succ]
    unfold gridReward
    rw [paperSeq_succ]
    ring
  rw [hdecomp]
  -- quantization part
  have hq : ∑ s ∈ Finset.Icc 1 T, (FirstPriceLearning.Stochastic.oracle μG (paperSeq v s)
        - gridOracle μG v s) ≤ K := by
    have h1 : ∀ s ∈ Finset.Icc 1 T, FirstPriceLearning.Stochastic.oracle μG (paperSeq v s)
        - gridOracle μG v s ≤ 1 / K := by
      intro s _
      have := oracle_le_grid μG (paperSeq v s) (paperSeq_mem v hv s) K hK
      unfold gridOracle gridReward
      linarith
    calc _ ≤ ∑ s ∈ Finset.Icc 1 T, (1 / (K : ℝ)) := Finset.sum_le_sum h1
      _ = (T : ℝ) * (1 / K) := by simp
      _ ≤ K := by
        rw [mul_one_div, div_le_iff₀ hKpos]
        have : Real.sqrt T ≤ K := by
          rw [hKdef]; unfold numGrid; exact Nat.le_ceil _
        have h0 := Real.sq_sqrt (show (0 : ℝ) ≤ T by positivity)
        nlinarith [Real.sqrt_nonneg (T : ℝ)]
  -- grid part
  have h17 : ∀ i < numGrid T, ∀ ℓ ∈ Finset.Icc 1 (numLevels T), ∀ t : ℕ,
      initLength T < t → t ≤ T →
        |runRhat T γ sel v m ℓ i t - gridReward μG v i t| ≤ runWidth T γ sel v m ℓ i t :=
    fun i hi ℓ hℓ t h1 h2 => (hgood i hi ℓ hℓ t h1 h2).1
  have h18 : ∀ i < numGrid T, ∀ ℓ ∈ Finset.Icc 1 (numLevels T), ∀ t : ℕ,
      initLength T < t → t ≤ T →
        runWidth T γ sel v m ℓ i t ≤ widthBound T γ sel μG v m ℓ i t :=
    fun i hi ℓ hℓ t h1 h2 => (hgood i hi ℓ hℓ t h1 h2).2
  have he19 := FirstPriceLearning.Adversarial.eq_19 T γ hγ sel hsel v hv μG hG m h17
  have hl9 := FirstPriceLearning.Adversarial.lemma_9 T γ hγ sel hsel v hv μG hG m h18
  set X := 10 * γ ^ ((3 : ℝ) / 2) * logFactor T * (1 + Real.log T) * Real.sqrt T with hX
  have hsum : ∑ ℓ ∈ Finset.Icc 1 (numLevels T), (1 / 2 : ℝ) ^ ℓ *
      (((runLevelSet T γ sel v m ℓ T).filter (fun t => initLength T < t)).card : ℝ)
      ≤ (numLevels T : ℝ) * X := by
    calc _ ≤ ∑ ℓ ∈ Finset.Icc 1 (numLevels T), X := Finset.sum_le_sum hl9
      _ = (numLevels T : ℝ) * X := by simp
  have hT0 : (initLength T : ℝ) = ((numLevels T : ℝ) + 1) * K := by
    unfold initLength; push_cast; ring
  have : 8 * ((numLevels T : ℝ) * X) = 80 * γ ^ ((3 : ℝ) / 2) * logFactor T * (1 + Real.log T)
      * (numLevels T : ℝ) * Real.sqrt T := by rw [hX]; ring
  nlinarith

theorem theorem7_core (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : IsSelectionRule sel) (v : Fin T → ℝ) (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    Integrable (fun m => regret μG v (mlBids T γ sel v m)) (Measure.pi fun _ : Fin T => μG) ∧
    ∫ m, regret μG v (mlBids T γ sel v m) ∂(Measure.pi fun _ : Fin T => μG)
      ≤ 4 + ((numLevels T : ℝ) + 4) * (numGrid T : ℝ)
          + 80 * γ ^ ((3 : ℝ) / 2) * logFactor T * (1 + Real.log T) * (numLevels T : ℝ)
            * Real.sqrt T := by
  set μ := Measure.pi fun _ : Fin T => μG with hμ
  set f := fun m => regret μG v (mlBids T γ sel v m) with hf
  have hfm : Measurable f := meas_regret μG v (mlRule T γ sel) (meas_mlRule T γ sel)
  -- pointwise bounds
  have hterm : ∀ m (t : Fin T), 0 ≤ FirstPriceLearning.Stochastic.oracle μG (v t) -
      FirstPriceLearning.Stochastic.expReward μG (v t) (mlBids T γ sel v m t) ∧
      FirstPriceLearning.Stochastic.oracle μG (v t) -
      FirstPriceLearning.Stochastic.expReward μG (v t) (mlBids T γ sel v m t) ≤ 2 := by
    intro m t
    have hb := mlBids_mem T γ sel hsel v m t
    have h1 := le_oracle μG (v t) _ (hv t) hb
    have h2 := oracle_le_one μG (v t) (hv t)
    have h3 := expReward_ge μG (v t) _ (hv t) hb
    constructor <;> linarith
  have hf0 : ∀ m, 0 ≤ f m := fun m => Finset.sum_nonneg (fun t _ => (hterm m t).1)
  have hf2 : ∀ m, f m ≤ 2 * T := by
    intro m
    calc f m ≤ ∑ _t : Fin T, (2 : ℝ) := Finset.sum_le_sum (fun t _ => (hterm m t).2)
      _ = 2 * T := by simp; ring
  have hint : Integrable f μ := by
    refine Integrable.of_bound hfm.aestronglyMeasurable (2 * T) (Filter.Eventually.of_forall ?_)
    intro m
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 m)]
    exact hf2 m
  refine ⟨hint, ?_⟩
  -- the bad event
  set Bad := {m : Fin T → ℝ | ¬ ∀ i < numGrid T, ∀ ℓ ∈ Finset.Icc 1 (numLevels T), ∀ t : ℕ,
            initLength T < t → t ≤ T →
              |runRhat T γ sel v m ℓ i t - gridReward μG v i t| ≤ runWidth T γ sel v m ℓ i t ∧
              runWidth T γ sel v m ℓ i t ≤ widthBound T γ sel μG v m ℓ i t} with hBad
  have hl7 : μ Bad ≤ ENNReal.ofReal (4 / (T : ℝ) ^ 3) :=
    FirstPriceLearning.Adversarial.lemma_7 T γ hγ sel hsel v hv μG hG
  set N := toMeasurable μ Bad with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable μ Bad
  have hNμ : μ N = μ Bad := measure_toMeasurable Bad
  set B0 := ((numLevels T : ℝ) + 2) * (numGrid T : ℝ)
        + 80 * γ ^ ((3 : ℝ) / 2) * logFactor T * (1 + Real.log T) * (numLevels T : ℝ)
          * Real.sqrt T with hB0
  have hlogT : 0 ≤ 1 + Real.log T := by
    rcases Nat.eq_zero_or_pos T with h | h
    · rw [h]; simp
    · have : 0 ≤ Real.log T := Real.log_nonneg (by exact_mod_cast h)
      linarith
  have hB0nn : 0 ≤ B0 := by
    have := logFactor_nonneg T
    have : 0 ≤ γ ^ ((3 : ℝ) / 2) := by positivity
    positivity
  -- pointwise domination
  have hdom : ∀ m, f m ≤ B0 + 2 * T * N.indicator (fun _ => (1 : ℝ)) m := by
    intro m
    by_cases hmN : m ∈ N
    · rw [Set.indicator_of_mem hmN]
      linarith [hf2 m]
    · rw [Set.indicator_of_notMem hmN, mul_zero, add_zero]
      have hmB : m ∉ Bad := fun h => hmN (subset_toMeasurable μ Bad h)
      rcases Nat.eq_zero_or_pos T with hT | hT
      · have : f m = 0 := by
          simp only [hf, regret]
          subst hT; simp
        linarith
      · have hg : ∀ i < numGrid T, ∀ ℓ ∈ Finset.Icc 1 (numLevels T), ∀ t : ℕ,
            initLength T < t → t ≤ T →
              |runRhat T γ sel v m ℓ i t - gridReward μG v i t| ≤ runWidth T γ sel v m ℓ i t ∧
              runWidth T γ sel v m ℓ i t ≤ widthBound T γ sel μG v m ℓ i t := by
          by_contra hc; exact hmB hc
        exact regret_good T γ hγ sel hsel v hv μG hG m hT hg
  have hint2 : Integrable (fun m => B0 + 2 * T * N.indicator (fun _ => (1 : ℝ)) m) μ :=
    (integrable_const B0).add (((integrable_const (1 : ℝ)).indicator hNm).const_mul _)
  have hI := integral_mono hint hint2 hdom
  have hI2 : ∫ m, (B0 + 2 * T * N.indicator (fun _ => (1 : ℝ)) m) ∂μ = B0 + 2 * T * μ.real N := by
    rw [integral_add (integrable_const B0) (((integrable_const (1 : ℝ)).indicator hNm).const_mul _),
      integral_const, integral_const_mul]
    have : ∫ m, N.indicator (fun _ => (1 : ℝ)) m ∂μ = μ.real N := integral_indicator_one hNm
    rw [this]
    simp [probReal_univ]
  have hfail : 2 * (T : ℝ) * μ.real N ≤ 2 := by
    have hle1 : μ.real N ≤ 1 := by
      rw [Measure.real]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    have hnn : 0 ≤ μ.real N := measureReal_nonneg
    rcases Nat.lt_or_ge T 2 with h | h
    · have : (T : ℝ) ≤ 1 := by exact_mod_cast (by omega : T ≤ 1)
      nlinarith
    · have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast h
      have hle : μ.real N ≤ 4 / (T : ℝ) ^ 3 := by
        rw [Measure.real, hNμ]
        exact ENNReal.toReal_le_of_le_ofReal (by positivity) hl7
      have : 2 * (T : ℝ) * (4 / (T : ℝ) ^ 3) ≤ 2 := by
        have hTne : (T : ℝ) ≠ 0 := by positivity
        rw [show 2 * (T : ℝ) * (4 / (T : ℝ) ^ 3) = 8 / (T : ℝ) ^ 2 by field_simp; ring]
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      have h0 : (0 : ℝ) ≤ 2 * T := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hle h0]
  have hKnn : (0 : ℝ) ≤ numGrid T := by positivity
  rw [hI2] at hI
  show ∫ m, f m ∂μ ≤ _
  linarith

end FPA2Core


open MeasureTheory

theorem solution (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : FirstPriceLearning.Adversarial.IsSelectionRule sel) (v : Fin T → ℝ)
    (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    Integrable (fun m => FirstPriceLearning.Adversarial.regret μG v
      (FirstPriceLearning.Adversarial.mlBids T γ sel v m)) (Measure.pi fun _ : Fin T => μG) ∧
    ∫ m, FirstPriceLearning.Adversarial.regret μG v
        (FirstPriceLearning.Adversarial.mlBids T γ sel v m) ∂(Measure.pi fun _ : Fin T => μG)
      ≤ 4 + ((FirstPriceLearning.Adversarial.numLevels T : ℝ) + 4) *
            (FirstPriceLearning.Adversarial.numGrid T : ℝ)
          + 80 * γ ^ ((3 : ℝ) / 2) * FirstPriceLearning.Adversarial.logFactor T *
            (1 + Real.log T) * (FirstPriceLearning.Adversarial.numLevels T : ℝ)
            * Real.sqrt T :=
  FPA2Core.theorem7_core T γ hγ sel hsel v hv μG hG
