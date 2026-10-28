-- Prove2me | solution 1 for FirstPriceLearning.Adversarial.eq_19
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T06:06:19.876471+00:00
-- url     : https://prove2.me/submissions/35d7917f-8608-47de-822c-f4723f6f4d23

import Mathlib
import Definitions.Def_FirstPriceLearning_Adversarial_Model
import Definitions.Def_FirstPriceLearning_Adversarial_MLISUCB
import Theorems.Thm_FirstPriceLearning_Adversarial_lemma_8

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

theorem eq19_core (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : IsSelectionRule sel) (v : Fin T → ℝ) (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (m : Fin T → ℝ)
    (h17 : ∀ i < numGrid T, ∀ ℓ ∈ Finset.Icc 1 (numLevels T), ∀ t : ℕ,
      initLength T < t → t ≤ T →
        |runRhat T γ sel v m ℓ i t - gridReward μG v i t| ≤ runWidth T γ sel v m ℓ i t) :
    ∑ t ∈ Finset.Icc 1 T, (gridOracle μG v t - gridReward μG v (runIndex T γ sel v m t) t)
      ≤ (initLength T : ℝ) + 8 * ∑ ℓ ∈ Finset.Icc 1 (numLevels T),
          (1 / 2 : ℝ) ^ ℓ *
            (((runLevelSet T γ sel v m ℓ T).filter (fun t => initLength T < t)).card : ℝ) := by
  classical
  have h8 := FirstPriceLearning.Adversarial.lemma_8 T γ hγ sel hsel v hv μG hG m h17
  set f := fun t => gridOracle μG v t - gridReward μG v (runIndex T γ sel v m t) t with hf
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 T) (fun t => t ≤ initLength T)]
  -- initial rounds
  have hA : ∑ t ∈ (Finset.Icc 1 T).filter (fun t => t ≤ initLength T), f t ≤ initLength T := by
    calc ∑ t ∈ (Finset.Icc 1 T).filter (fun t => t ≤ initLength T), f t
        ≤ ∑ t ∈ (Finset.Icc 1 T).filter (fun t => t ≤ initLength T), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro t ht
          simp only [Finset.mem_filter, Finset.mem_Icc] at ht
          have hK := numGrid_pos T (by omega)
          have hidx : runIndex T γ sel v m t = 0 := by
            unfold runIndex runRecord
            rw [record_le _ _ _ _ _ t ht.2]
          simp only [hf, hidx]
          have := gridOracle_le_one μG v hv t hK
          have := gridReward_nonneg_zero μG v hv t
          linarith
      _ = (((Finset.Icc 1 T).filter (fun t => t ≤ initLength T)).card : ℝ) := by simp
      _ ≤ initLength T := by
          have : (Finset.Icc 1 T).filter (fun t => t ≤ initLength T) ⊆ Finset.Icc 1 (initLength T) := by
            intro t ht; simp only [Finset.mem_filter, Finset.mem_Icc] at ht ⊢; omega
          have := Finset.card_le_card this
          simp only [Nat.card_Icc, add_tsub_cancel_right] at this
          exact_mod_cast this
  -- later rounds
  set B := (Finset.Icc 1 T).filter (fun t => ¬ t ≤ initLength T) with hB
  have hB1 : ∑ t ∈ B, f t ≤ ∑ t ∈ B, 8 * (1 / 2 : ℝ) ^ runLevel T γ sel v m t := by
    apply Finset.sum_le_sum
    intro t ht
    simp only [hB, Finset.mem_filter, Finset.mem_Icc] at ht
    exact (h8 t (by omega) ht.1.2).2
  have hmaps : ∀ t ∈ B, runLevel T γ sel v m t ∈ Finset.Icc 1 (numLevels T) := by
    intro t ht
    simp only [hB, Finset.mem_filter, Finset.mem_Icc] at ht
    have := (decide_spec T γ hγ sel hsel (paperSeq v) (runFeedback T γ sel v m) t
      (by omega) ht.1.2).1
    rw [Finset.mem_Icc]
    exact this
  have hB2 : ∑ t ∈ B, 8 * (1 / 2 : ℝ) ^ runLevel T γ sel v m t =
      8 * ∑ ℓ ∈ Finset.Icc 1 (numLevels T), (1 / 2 : ℝ) ^ ℓ *
        (((runLevelSet T γ sel v m ℓ T).filter (fun t => initLength T < t)).card : ℝ) := by
    rw [← Finset.mul_sum, ← Finset.sum_fiberwise_of_maps_to hmaps]
    congr 1
    apply Finset.sum_congr rfl
    intro ℓ _
    rw [Finset.sum_congr rfl (fun t ht => by
      rw [(Finset.mem_filter.mp ht).2])]
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 2
    congr 1
    ext t
    simp only [hB, runLevelSet, levelSet, runLevel, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, by omega⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨h1, by omega⟩, h3⟩
  linarith

end FPA2Core


open MeasureTheory

theorem solution (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : FirstPriceLearning.Adversarial.IsSelectionRule sel) (v : Fin T → ℝ)
    (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (m : Fin T → ℝ)
    (h17 : ∀ i < FirstPriceLearning.Adversarial.numGrid T,
      ∀ ℓ ∈ Finset.Icc 1 (FirstPriceLearning.Adversarial.numLevels T), ∀ t : ℕ,
      FirstPriceLearning.Adversarial.initLength T < t → t ≤ T →
        |FirstPriceLearning.Adversarial.runRhat T γ sel v m ℓ i t -
          FirstPriceLearning.Adversarial.gridReward μG v i t| ≤
          FirstPriceLearning.Adversarial.runWidth T γ sel v m ℓ i t) :
    ∑ t ∈ Finset.Icc 1 T, (FirstPriceLearning.Adversarial.gridOracle μG v t -
        FirstPriceLearning.Adversarial.gridReward μG v
          (FirstPriceLearning.Adversarial.runIndex T γ sel v m t) t)
      ≤ (FirstPriceLearning.Adversarial.initLength T : ℝ) + 8 * ∑ ℓ ∈ Finset.Icc 1
          (FirstPriceLearning.Adversarial.numLevels T),
          (1 / 2 : ℝ) ^ ℓ *
            (((FirstPriceLearning.Adversarial.runLevelSet T γ sel v m ℓ T).filter
              (fun t => FirstPriceLearning.Adversarial.initLength T < t)).card : ℝ) :=
  FPA2Core.eq19_core T γ hγ sel hsel v hv μG hG m h17
