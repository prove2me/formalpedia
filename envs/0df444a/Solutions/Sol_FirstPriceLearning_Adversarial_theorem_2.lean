-- Prove2me | solution 1 for FirstPriceLearning.Adversarial.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T06:22:32.872751+00:00
-- url     : https://prove2.me/submissions/4e77e3f5-a7a9-4d73-82e8-a594cf82f3d2

import Mathlib
import Definitions.Def_FirstPriceLearning_Adversarial_Model
import Definitions.Def_FirstPriceLearning_Adversarial_MLISUCB
import Theorems.Thm_FirstPriceLearning_Adversarial_theorem_7

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

end FPA2Core


open MeasureTheory

namespace FPA2Core

open FirstPriceLearning.Adversarial

/-- A concrete selection rule: the least element of a nonempty candidate set. -/
noncomputable def sel0 : ℕ → ℕ → Finset ℕ → ℕ :=
  fun _ _ S => if h : S.Nonempty then S.min' h else 0

theorem sel0_isSel : IsSelectionRule sel0 := by
  intro t ℓ S hS
  simp only [sel0, dif_pos hS]
  exact Finset.min'_mem S hS

theorem record_idx_le (T : ℕ) (γ : ℝ) (V Y : ℕ → ℝ) (n : ℕ) :
    (record T γ sel0 V Y n).2 ≤ numGrid T := by
  by_cases hn : n ≤ initLength T
  · rw [record_le T γ sel0 V Y n hn]; exact Nat.zero_le _
  · push Not at hn
    rw [record_gt T γ sel0 V Y n hn]
    unfold decideRound
    split_ifs with h
    · simp only [sel0]
      split_ifs with h2
      · have hmem := Finset.min'_mem _ h2
        have := cand_subset_range T γ Y V (record T γ sel0 V Y) n _
          (exploreSet_subset T γ _ Y V _ n hmem)
        exact (Finset.mem_range.mp this).le
      · exact Nat.zero_le _
    · exact Nat.zero_le _

theorem mlRule_mem (T : ℕ) (γ : ℝ) (t : Fin T) (vs : Fin (t.val + 1) → ℝ) (ys : Fin t.val → ℝ) :
    mlRule T γ sel0 t vs ys ∈ Set.Icc (0 : ℝ) 1 := by
  unfold mlRule
  exact grid_mem _ _ (record_idx_le _ _ _ _ _)

/-- ML-IS-UCB with `γ = 3` as a (deterministic) policy. -/
noncomputable def mlPolicy (T : ℕ) : Policy T where
  U := Unit
  μU := Measure.dirac ()
  bid := fun _ => mlRule T 3 sel0
  measurable_bid := fun t => (meas_mlRule T 3 sel0 t).comp measurable_snd
  bid_mem := fun _ t vs ys => mlRule_mem T 3 t vs ys

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

/-! ### Numerics: the explicit bound of Theorem 7 is `O(√T log³ T)` -/

theorem log_two_ge : (0.69 : ℝ) ≤ Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

theorem bound_numeric (T : ℕ) (hT : 2 ≤ T) :
    4 + ((numLevels T : ℝ) + 4) * (numGrid T : ℝ)
        + 80 * (3 : ℝ) ^ ((3 : ℝ) / 2) * logFactor T * (1 + Real.log T) * (numLevels T : ℝ)
          * Real.sqrt T
      ≤ 20000 * Real.sqrt T * Real.log T ^ 3 := by
  set lam := Real.log T with hlam
  have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hlam0 : (0.69 : ℝ) ≤ lam := by
    have := Real.log_le_log (by norm_num) hT'
    linarith [log_two_ge]
  have hsT : 1 ≤ Real.sqrt T := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  -- L ≤ 3 λ
  have hLpos := numLevels_pos T hT
  have hL : (numLevels T : ℝ) ≤ 3 * lam := by
    have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < T by omega)
    have h2 : ((2 : ℝ) ^ (numLevels T - 1)) < T := by
      unfold numLevels; exact_mod_cast h1
    have h3 : Real.log ((2 : ℝ) ^ (numLevels T - 1)) < lam := Real.log_lt_log (by positivity) h2
    rw [Real.log_pow] at h3
    have h4 : ((numLevels T - 1 : ℕ) : ℝ) = (numLevels T : ℝ) - 1 := by
      rw [Nat.cast_sub hLpos]; simp
    rw [h4] at h3
    have hl2 := log_two_ge
    have : (numLevels T : ℝ) * Real.log 2 < lam + Real.log 2 := by nlinarith
    have hLnn : (0 : ℝ) ≤ numLevels T := by positivity
    nlinarith
  -- K ≤ 2 √T and K ≤ T
  have hK1 := numGrid_pos T (by omega)
  have hK : (numGrid T : ℝ) ≤ 2 * Real.sqrt T := by
    have : (numGrid T : ℝ) < Real.sqrt T + 1 := by
      unfold numGrid; exact Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
    linarith
  have hKT : (numGrid T : ℝ) ≤ T := by
    have : numGrid T ≤ T := by
      unfold numGrid
      apply Nat.ceil_le.mpr
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    exact_mod_cast this
  have hlamT : lam ≤ T := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < T by linarith); linarith
  -- log(LKT) ≤ 3 λ
  have hF : logFactor T ≤ 3 * lam := by
    unfold logFactor
    have hLT : (numLevels T : ℝ) ≤ T := by
      have : numLevels T ≤ T := by
        unfold numLevels
        exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
      exact_mod_cast this
    have hpos : (0 : ℝ) < (numLevels T : ℝ) * (numGrid T : ℝ) * (T : ℝ) := by
      have : (1 : ℝ) ≤ numLevels T := by exact_mod_cast hLpos
      have : (1 : ℝ) ≤ numGrid T := by exact_mod_cast hK1
      positivity
    have hle : (numLevels T : ℝ) * (numGrid T : ℝ) * (T : ℝ) ≤ (T : ℝ) ^ 3 := by
      have : (0 : ℝ) ≤ numLevels T := by positivity
      have : (0 : ℝ) ≤ numGrid T := by positivity
      calc (numLevels T : ℝ) * (numGrid T : ℝ) * (T : ℝ) ≤ T * T * T := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            exact mul_le_mul hLT hKT (by positivity) (by linarith)
        _ = (T : ℝ) ^ 3 := by ring
    calc Real.log ((numLevels T : ℝ) * (numGrid T : ℝ) * (T : ℝ)) ≤ Real.log ((T : ℝ) ^ 3) :=
          Real.log_le_log hpos hle
      _ = 3 * lam := by rw [Real.log_pow]; push_cast; ring
  have hF0 := logFactor_nonneg T
  -- 3^{3/2} ≤ 6
  have h32 : (3 : ℝ) ^ ((3 : ℝ) / 2) ≤ 6 := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    have : Real.sqrt 3 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  have h32' : (0 : ℝ) ≤ (3 : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  have h1lam : 1 + lam ≤ 3 * lam := by linarith
  have hLnn : (0 : ℝ) ≤ numLevels T := by positivity
  -- term 3
  have t3 : 80 * (3 : ℝ) ^ ((3 : ℝ) / 2) * logFactor T * (1 + lam) * (numLevels T : ℝ)
      * Real.sqrt T ≤ 12960 * lam ^ 3 * Real.sqrt T := by
    have a1 : (3 : ℝ) ^ ((3 : ℝ) / 2) * logFactor T ≤ 6 * (3 * lam) :=
      mul_le_mul h32 hF hF0 (by norm_num)
    have a2 : (3 : ℝ) ^ ((3 : ℝ) / 2) * logFactor T * (1 + lam) ≤ 6 * (3 * lam) * (3 * lam) :=
      mul_le_mul a1 h1lam (by linarith) (by positivity)
    have a3 : (3 : ℝ) ^ ((3 : ℝ) / 2) * logFactor T * (1 + lam) * (numLevels T : ℝ) ≤
        6 * (3 * lam) * (3 * lam) * (3 * lam) :=
      mul_le_mul a2 hL hLnn (by positivity)
    have a4 := mul_le_mul_of_nonneg_right a3 (Real.sqrt_nonneg (T : ℝ))
    nlinarith
  -- term 2
  have hsq : (0.4761 : ℝ) ≤ lam ^ 2 := by nlinarith
  have hcube : (0.32 : ℝ) ≤ lam ^ 3 := by
    have : lam ^ 3 = lam * lam ^ 2 := by ring
    rw [this]; nlinarith
  have hlam3 : lam ≤ 3 * lam ^ 3 := by
    have : 3 * lam ^ 3 - lam = lam * (3 * lam ^ 2 - 1) := by ring
    have : 0 ≤ lam * (3 * lam ^ 2 - 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  have t2 : ((numLevels T : ℝ) + 4) * (numGrid T : ℝ) ≤ 108 * lam ^ 3 * Real.sqrt T := by
    have b1 : (numLevels T : ℝ) + 4 ≤ 9 * lam := by linarith
    have b2 : ((numLevels T : ℝ) + 4) * (numGrid T : ℝ) ≤ 9 * lam * (2 * Real.sqrt T) :=
      mul_le_mul b1 hK (by positivity) (by positivity)
    have b3 : 9 * lam * (2 * Real.sqrt T) ≤ 9 * (3 * lam ^ 3) * (2 * Real.sqrt T) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
    nlinarith
  -- term 1
  have t1 : (4 : ℝ) ≤ 13 * lam ^ 3 * Real.sqrt T := by
    have : (4 : ℝ) ≤ 13 * lam ^ 3 := by linarith
    nlinarith
  have : (0 : ℝ) ≤ lam ^ 3 * Real.sqrt T := by positivity
  nlinarith

end FPA2Core


open MeasureTheory

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, 2 ≤ T → ∃ π : FirstPriceLearning.Adversarial.Policy T,
      ∀ v : Fin T → ℝ, (∀ t, v t ∈ Set.Icc (0 : ℝ) 1) →
      ∀ (μG : Measure ℝ) [IsProbabilityMeasure μG], μG (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
        Integrable (fun p : π.U × (Fin T → ℝ) => FirstPriceLearning.Adversarial.regret μG v
            (FirstPriceLearning.Adversarial.runBids (π.bid p.1) v p.2))
            (π.μU.prod (Measure.pi fun _ : Fin T => μG)) ∧
          FirstPriceLearning.Adversarial.expectedRegret π μG v
            ≤ C * Real.sqrt T * Real.log T ^ 3 := by
  refine ⟨20000, by norm_num, fun T hT => ⟨FPA2Core.mlPolicy T, fun v hv μG _ hG => ?_⟩⟩
  obtain ⟨hint, hbound⟩ := FirstPriceLearning.Adversarial.theorem_7 T 3 (le_refl _)
    FPA2Core.sel0 FPA2Core.sel0_isSel v hv μG hG
  set ν := Measure.pi fun _ : Fin T => μG with hν
  set g : Unit × (Fin T → ℝ) → ℝ := fun p => FirstPriceLearning.Adversarial.regret μG v
    (FirstPriceLearning.Adversarial.runBids
      (FirstPriceLearning.Adversarial.mlRule T 3 FPA2Core.sel0) v p.2) with hg
  have hgm : Measurable g :=
    (FPA2Core.meas_regret μG v _ (FPA2Core.meas_mlRule T 3 FPA2Core.sel0)).comp measurable_snd
  have hμ : (FPA2Core.mlPolicy T).μU.prod ν = Measure.map (Prod.mk ()) ν :=
    Measure.dirac_prod ()
  have hmk : AEMeasurable (Prod.mk () : (Fin T → ℝ) → Unit × (Fin T → ℝ)) ν :=
    measurable_prodMk_left.aemeasurable
  refine ⟨?_, ?_⟩
  · show Integrable g ((FPA2Core.mlPolicy T).μU.prod ν)
    have key : Integrable g (Measure.map (Prod.mk ()) ν) :=
      (integrable_map_measure hgm.aestronglyMeasurable hmk).mpr hint
    rw [hμ]
    exact key
  · show ∫ p, g p ∂((FPA2Core.mlPolicy T).μU.prod ν) ≤ _
    have key2 : ∫ p, g p ∂(Measure.map (Prod.mk ()) ν) = ∫ m, g ((), m) ∂ν :=
      integral_map hmk hgm.aestronglyMeasurable
    rw [hμ]
    refine le_trans (le_of_eq key2) ?_
    refine le_trans hbound ?_
    exact FPA2Core.bound_numeric T hT
