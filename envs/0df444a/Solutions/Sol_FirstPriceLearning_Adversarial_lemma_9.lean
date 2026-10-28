-- Prove2me | solution 1 for FirstPriceLearning.Adversarial.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T06:12:00.775842+00:00
-- url     : https://prove2.me/submissions/e4a0d155-f346-499b-9947-e9e1710468c3

import Mathlib
import Definitions.Def_FirstPriceLearning_Adversarial_Model
import Definitions.Def_FirstPriceLearning_Adversarial_MLISUCB
import Theorems.Thm_FirstPriceLearning_Adversarial_lemma_16

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

theorem sum_sqrt_le_sqrt_card_mul (s : Finset ℕ) (x : ℕ → ℝ) (hx : ∀ t ∈ s, 0 ≤ x t) :
    ∑ t ∈ s, Real.sqrt (x t) ≤ Real.sqrt (s.card) * Real.sqrt (∑ t ∈ s, x t) := by
  have := Real.sum_mul_le_sqrt_mul_sqrt s (fun _ => (1 : ℝ)) (fun t => Real.sqrt (x t))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at this
  have h2 : ∑ t ∈ s, Real.sqrt (x t) ^ 2 = ∑ t ∈ s, x t :=
    Finset.sum_congr rfl (fun t ht => Real.sq_sqrt (hx t ht))
  rw [h2] at this
  exact this

theorem intervalProb_nonneg (T : ℕ) (μG : Measure ℝ) [IsProbabilityMeasure μG] (j : ℕ) :
    0 ≤ intervalProb T μG j := by
  unfold intervalProb
  have : grid (numGrid T) j ≤ grid (numGrid T) (j + 1) := by
    unfold grid
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    push_cast; linarith
  linarith [cdf_mono μG this]

theorem sum_intervalProb_le (T : ℕ) (μG : Measure ℝ) [IsProbabilityMeasure μG] :
    ∑ j ∈ Finset.range (numGrid T), intervalProb T μG j ≤ 1 := by
  unfold intervalProb
  rw [Finset.sum_range_sub (fun j => FirstPriceLearning.Stochastic.cdf μG (grid (numGrid T) j))]
  linarith [cdf_le_one μG (grid (numGrid T) (numGrid T)), cdf_nonneg μG (grid (numGrid T) 0)]

set_option maxHeartbeats 2000000 in
theorem lemma9_core (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : IsSelectionRule sel) (v : Fin T → ℝ) (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (m : Fin T → ℝ)
    (h18 : ∀ i < numGrid T, ∀ ℓ ∈ Finset.Icc 1 (numLevels T), ∀ t : ℕ,
      initLength T < t → t ≤ T →
        runWidth T γ sel v m ℓ i t ≤ widthBound T γ sel μG v m ℓ i t) :
    ∀ ℓ ∈ Finset.Icc 1 (numLevels T),
      (1 / 2 : ℝ) ^ ℓ *
          (((runLevelSet T γ sel v m ℓ T).filter (fun t => initLength T < t)).card : ℝ)
        ≤ 10 * γ ^ ((3 : ℝ) / 2) * logFactor T * (1 + Real.log T) * Real.sqrt T := by
  classical
  intro ℓ hℓ
  set R := runRecord T γ sel v m with hR
  set Φ := runLevelSet T γ sel v m ℓ T with hΦdef
  set F := Φ.filter (fun t => initLength T < t) with hFdef
  have hγ0 : 0 ≤ γ := by linarith
  have hγ32 : γ ^ ((3 : ℝ) / 2) = γ * Real.sqrt γ := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one,
      Real.sqrt_eq_rpow]
  rcases F.eq_empty_or_nonempty with hFe | ⟨t₁, ht₁⟩
  · rw [hFe, Finset.card_empty, Nat.cast_zero, mul_zero]
    have h1 : 0 ≤ 1 + Real.log T := by
      rcases Nat.eq_zero_or_pos T with h | h
      · subst h; simp
      · have : 0 ≤ Real.log T := Real.log_nonneg (by exact_mod_cast h)
        linarith
    have := logFactor_nonneg T
    have : 0 ≤ γ ^ ((3 : ℝ) / 2) := by positivity
    positivity
  -- main case: there is a level-ℓ time after the initialization
  have ht₁' := ht₁
  simp only [hFdef, hΦdef, runLevelSet, levelSet, Finset.mem_filter, Finset.mem_Icc] at ht₁'
  have hT2 : 2 ≤ T := two_le_of_init T t₁ ht₁'.2 ht₁'.1.1.2
  have hT0T : initLength T < T := by omega
  have hK := numGrid_pos T (by omega)
  have hlogF := one_le_logFactor T hT2
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ T))
  rw [Finset.mem_Icc] at hℓ
  -- notation
  set K := numGrid T with hKdef
  set a := logFactor T with hadef
  set c := γ * a / (K : ℝ) with hcdef
  set idx := fun s => (R s).2 with hidxdef
  -- per-time facts
  have hspec : ∀ t ∈ F, initLength T < t ∧ t ≤ T ∧ (R t).1 = ℓ ∧ idx t < K ∧
      (1 / 2 : ℝ) ^ ℓ < runWidth T γ sel v m ℓ (idx t) t := by
    intro t ht
    simp only [hFdef, hΦdef, runLevelSet, levelSet, Finset.mem_filter, Finset.mem_Icc] at ht
    have hds := decide_spec T γ hγ sel hsel (paperSeq v) (runFeedback T γ sel v m) t ht.2 ht.1.1.2
    have hexp : (R t).2 ∈ exploreSet T γ R (runFeedback T γ sel v m) (paperSeq v) (R t).1 t :=
      hds.2.1
    have hcand := exploreSet_subset T γ R _ _ _ t hexp
    have hiK : (R t).2 < K := Finset.mem_range.mp (cand_subset_range T γ _ _ R t _ hcand)
    refine ⟨ht.2, ht.1.1.2, ht.1.2, hiK, ?_⟩
    have hw := hexp
    unfold exploreSet at hw
    rw [Finset.mem_filter] at hw
    rw [ht.1.2] at hw
    exact hw.2
  -- Step 1: 2^{-ℓ} |F| ≤ Σ widthBound
  have hstep1 : (1 / 2 : ℝ) ^ ℓ * (F.card : ℝ) ≤
      ∑ t ∈ F, widthBound T γ sel μG v m ℓ (idx t) t := by
    rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro t ht
    obtain ⟨h1, h2, h3, h4, h5⟩ := hspec t ht
    exact le_trans h5.le (h18 (idx t) h4 ℓ (by rw [Finset.mem_Icc]; exact hℓ) t h1 h2)
  -- the counts agree with those of Lemma 16
  have hcount : ∀ t ∈ F, ∀ j, runN T γ sel v m ℓ j t = obsCount K Φ idx j t := by
    intro t ht j
    obtain ⟨h1, h2, -⟩ := hspec t ht
    unfold runN nObs obsCount
    congr 1
    ext s
    simp only [hΦdef, runLevelSet, levelSet, Finset.mem_filter, Finset.mem_Icc, hidxdef, hR]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩; exact ⟨⟨⟨h1, by omega⟩, h3⟩, h4, h5⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩; exact ⟨⟨⟨h1, by omega⟩, h3⟩, h4, h5⟩
  -- Lemma 16 hypotheses
  have hΦsub : Φ ⊆ Finset.Icc 1 T := by
    intro s hs
    simp only [hΦdef, runLevelSet, levelSet, Finset.mem_filter] at hs
    exact hs.1
  have hidxK : ∀ t ∈ Φ, idx t < K := by
    intro t ht
    by_cases h : t ≤ initLength T
    · have : idx t = 0 := by
        simp only [hidxdef, hR, runRecord]
        rw [record_le _ _ _ _ _ t h]
      rw [this]; exact hK
    · exact (hspec t (by rw [hFdef, Finset.mem_filter]; exact ⟨ht, by omega⟩)).2.2.2.1
  have hinit : numGrid T ≤ (Φ.filter (fun r => r ≤ initLength T ∧ idx r = 0)).card := by
    have hsub : Finset.Icc (ℓ * K + 1) (ℓ * K + K) ⊆
        Φ.filter (fun r => r ≤ initLength T ∧ idx r = 0) := by
      intro s hs
      rw [Finset.mem_Icc] at hs
      have hsT0 : s ≤ initLength T := by
        unfold initLength
        have : ℓ * K + K = (ℓ + 1) * K := by ring
        have : (ℓ + 1) * K ≤ (numLevels T + 1) * K := Nat.mul_le_mul_right _ (by omega)
        rw [← hKdef]; omega
      have hrec : R s = ((s - 1) / K, 0) := by
        simp only [hR, runRecord]; rw [record_le _ _ _ _ _ s hsT0]
      have hdiv : (s - 1) / K = ℓ := by
        apply Nat.div_eq_of_lt_le
        · omega
        · have : (ℓ + 1) * K = ℓ * K + K := by ring
          omega
      simp only [hΦdef, runLevelSet, levelSet, Finset.mem_filter, Finset.mem_Icc, hidxdef]
      rw [← hR, hrec, hdiv]
      refine ⟨⟨⟨by omega, by omega⟩, rfl⟩, hsT0, rfl⟩
    have := Finset.card_le_card hsub
    simp only [Nat.card_Icc] at this
    rw [← hKdef]; omega
  set w : ℕ → ℝ := fun j => intervalProb T μG j + c with hwdef
  have hc0 : 0 ≤ c := by positivity
  have hw0 : ∀ j < K, 0 ≤ w j := fun j _ => by
    simp only [hwdef]; linarith [intervalProb_nonneg T μG j]
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hsum_w : ∑ j ∈ Finset.range K, w j ≤ 1 + γ * a := by
    simp only [hwdef, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h1 := sum_intervalProb_le T μG
    have h2 : (K : ℝ) * c = γ * a := by
      simp only [hcdef]; field_simp
    rw [← hKdef] at h1
    linarith
  obtain ⟨L16a, L16b⟩ := FirstPriceLearning.Adversarial.lemma_16 T K (initLength T) Φ hΦsub idx
    hidxK hinit w hw0 (∑ j ∈ Finset.range K, w j) rfl
  -- Step 2: split the width bound
  have hA : ∀ t ∈ F, 0 ≤ 6 * a * ∑ j ∈ Finset.Ico (idx t) K,
      (1 / (runN T γ sel v m ℓ j t : ℝ)) * (intervalProb T μG j + c) := by
    intro t _
    have : 0 ≤ ∑ j ∈ Finset.Ico (idx t) K,
        (1 / (runN T γ sel v m ℓ j t : ℝ)) * (intervalProb T μG j + c) := by
      apply Finset.sum_nonneg
      intro j _
      have := intervalProb_nonneg T μG j
      positivity
    have : 0 ≤ a := by linarith
    positivity
  have hsplit : ∑ t ∈ F, widthBound T γ sel μG v m ℓ (idx t) t =
      γ * (∑ t ∈ F, Real.sqrt (6 * a * ∑ j ∈ Finset.Ico (idx t) K,
        (1 / (runN T γ sel v m ℓ j t : ℝ)) * (intervalProb T μG j + c))
       + a * ∑ t ∈ F, 1 / (runN T γ sel v m ℓ (idx t) t : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    simp only [widthBound, hcdef, hadef, hKdef]
    ring
  -- Step 3: Cauchy–Schwarz + Lemma 16
  have hS1 : ∑ t ∈ F, Real.sqrt (6 * a * ∑ j ∈ Finset.Ico (idx t) K,
        (1 / (runN T γ sel v m ℓ j t : ℝ)) * (intervalProb T μG j + c)) ≤
      Real.sqrt (T * (6 * a * ((1 + γ * a) * (1 + Real.log T)))) := by
    refine le_trans (sum_sqrt_le_sqrt_card_mul F _ hA) ?_
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have hcardF : (F.card : ℝ) ≤ T := by
      have : F ⊆ Finset.Icc 1 T := (Finset.filter_subset _ _).trans hΦsub
      have := Finset.card_le_card this
      simp only [Nat.card_Icc, add_tsub_cancel_right] at this
      exact_mod_cast this
    have hsumA : ∑ t ∈ F, 6 * a * ∑ j ∈ Finset.Ico (idx t) K,
        (1 / (runN T γ sel v m ℓ j t : ℝ)) * (intervalProb T μG j + c) ≤
        6 * a * ((1 + γ * a) * (1 + Real.log T)) := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      have : ∑ t ∈ F, ∑ j ∈ Finset.Ico (idx t) K,
          (1 / (runN T γ sel v m ℓ j t : ℝ)) * (intervalProb T μG j + c) =
          ∑ t ∈ F, ∑ j ∈ Finset.Ico (idx t) K, w j / (obsCount K Φ idx j t : ℝ) := by
        apply Finset.sum_congr rfl; intro t ht
        apply Finset.sum_congr rfl; intro j _
        rw [hcount t ht j]; simp only [hwdef]; ring
      rw [this]
      refine le_trans L16a ?_
      apply mul_le_mul_of_nonneg_right hsum_w (by linarith)
    have h0 : 0 ≤ ∑ t ∈ F, 6 * a * ∑ j ∈ Finset.Ico (idx t) K,
        (1 / (runN T γ sel v m ℓ j t : ℝ)) * (intervalProb T μG j + c) :=
      Finset.sum_nonneg hA
    have h00 : 0 ≤ 6 * a * ((1 + γ * a) * (1 + Real.log T)) := by
      have : 0 ≤ a := by linarith
      positivity
    exact mul_le_mul hcardF hsumA h0 (by positivity)
  have hS2 : ∑ t ∈ F, 1 / (runN T γ sel v m ℓ (idx t) t : ℝ) ≤ K * (1 + Real.log T) := by
    have : ∑ t ∈ F, 1 / (runN T γ sel v m ℓ (idx t) t : ℝ) =
        ∑ t ∈ F, 1 / (obsCount K Φ idx (idx t) t : ℝ) := by
      apply Finset.sum_congr rfl; intro t ht; rw [hcount t ht]
    rw [this]; exact L16b
  -- Step 4: numerics
  have hsqT : 1 ≤ Real.sqrt T := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ T))
  have hKle : (K : ℝ) ≤ 2 * Real.sqrt T := by
    have : (K : ℝ) < Real.sqrt T + 1 := by
      simp only [hKdef, numGrid]
      exact Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
    linarith
  have hsqγ : 1 ≤ Real.sqrt γ := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  set b := 1 + Real.log T with hbdef
  have hb : 1 ≤ b := by linarith
  have hsq1 : Real.sqrt (T * (6 * a * ((1 + γ * a) * b))) ≤
      4 * Real.sqrt γ * a * b * Real.sqrt T := by
    rw [Real.sqrt_le_left (by positivity)]
    have e1 : (4 * Real.sqrt γ * a * b * Real.sqrt T) ^ 2 = 16 * γ * a ^ 2 * b ^ 2 * T := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by linarith),
        Real.sq_sqrt (by positivity)]
      ring
    rw [e1]
    have hT0 : (0 : ℝ) ≤ T := by positivity
    have h1 : 1 + γ * a ≤ 2 * γ * a := by nlinarith
    have h2 : 6 * a * ((1 + γ * a) * b) ≤ 16 * γ * a ^ 2 * b ^ 2 := by
      have : 0 ≤ a := by linarith
      have : 0 ≤ b := by linarith
      have hab : 6 * a * ((1 + γ * a) * b) ≤ 6 * a * (2 * γ * a * b) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
      have : 6 * a * (2 * γ * a * b) ≤ 16 * γ * a ^ 2 * b ^ 2 := by
        have : 0 ≤ γ * a ^ 2 * b := by positivity
        nlinarith
      linarith
    have := mul_le_mul_of_nonneg_left h2 hT0
    linarith
  have hfinal : (1 / 2 : ℝ) ^ ℓ * (F.card : ℝ) ≤
      γ * (4 * Real.sqrt γ * a * b * Real.sqrt T + a * (2 * Real.sqrt T * b)) := by
    refine le_trans hstep1 ?_
    rw [hsplit]
    apply mul_le_mul_of_nonneg_left _ hγ0
    have : a * ∑ t ∈ F, 1 / (runN T γ sel v m ℓ (idx t) t : ℝ) ≤ a * (2 * Real.sqrt T * b) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      refine le_trans hS2 ?_
      exact mul_le_mul_of_nonneg_right hKle (by linarith)
    linarith [hS1.trans hsq1]
  rw [hγ32]
  refine le_trans hfinal ?_
  have : 0 ≤ a * b * Real.sqrt T := by
    have : 0 ≤ a := by linarith
    positivity
  have hP : 0 ≤ γ * Real.sqrt γ := by positivity
  have h2 : γ * (a * (2 * Real.sqrt T * b)) ≤ 2 * (γ * Real.sqrt γ) * (a * b * Real.sqrt T) := by
    have hγs : γ ≤ γ * Real.sqrt γ := by nlinarith
    have e : γ * (a * (2 * Real.sqrt T * b)) = 2 * γ * (a * b * Real.sqrt T) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hγs this
    linarith
  have e1 : γ * (4 * Real.sqrt γ * a * b * Real.sqrt T + a * (2 * Real.sqrt T * b)) =
      4 * (γ * Real.sqrt γ) * (a * b * Real.sqrt T) + γ * (a * (2 * Real.sqrt T * b)) := by ring
  have e2 : 10 * (γ * Real.sqrt γ) * a * b * Real.sqrt T =
      10 * (γ * Real.sqrt γ) * (a * b * Real.sqrt T) := by ring
  rw [e1, e2]
  have := mul_nonneg hP this
  linarith

end FPA2Core


open MeasureTheory

theorem solution (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : FirstPriceLearning.Adversarial.IsSelectionRule sel) (v : Fin T → ℝ)
    (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (m : Fin T → ℝ)
    (h18 : ∀ i < FirstPriceLearning.Adversarial.numGrid T,
      ∀ ℓ ∈ Finset.Icc 1 (FirstPriceLearning.Adversarial.numLevels T), ∀ t : ℕ,
      FirstPriceLearning.Adversarial.initLength T < t → t ≤ T →
        FirstPriceLearning.Adversarial.runWidth T γ sel v m ℓ i t ≤
          FirstPriceLearning.Adversarial.widthBound T γ sel μG v m ℓ i t) :
    ∀ ℓ ∈ Finset.Icc 1 (FirstPriceLearning.Adversarial.numLevels T),
      (1 / 2 : ℝ) ^ ℓ *
          (((FirstPriceLearning.Adversarial.runLevelSet T γ sel v m ℓ T).filter
            (fun t => FirstPriceLearning.Adversarial.initLength T < t)).card : ℝ)
        ≤ 10 * γ ^ ((3 : ℝ) / 2) * FirstPriceLearning.Adversarial.logFactor T *
            (1 + Real.log T) * Real.sqrt T :=
  FPA2Core.lemma9_core T γ hγ sel hsel v hv μG hG m h18
