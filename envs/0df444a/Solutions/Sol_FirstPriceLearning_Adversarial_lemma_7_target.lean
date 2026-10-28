-- Prove2me | solution 1 for FirstPriceLearning.Adversarial.lemma_7_target
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T07:11:10.662656+00:00
-- url     : https://prove2.me/submissions/548dca5a-6154-49b6-8997-1e58030a3397

import Mathlib
import Definitions.Def_FirstPriceLearning_Adversarial_Model
import Definitions.Def_FirstPriceLearning_Adversarial_MLISUCB
import Theorems.Thm_bernstein_exp_le

open MeasureTheory

namespace FPA2bLib

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

end FPA2bLib

namespace FPA2bLib

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

end FPA2bLib


open MeasureTheory

namespace FPA2bLib

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

end FPA2bLib
open MeasureTheory

namespace FPA2bLib

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

end FPA2bLib


open MeasureTheory ProbabilityTheory

namespace FPA2bConc

theorem chernoff_pi {n : ℕ} (μG : Measure ℝ) [IsProbabilityMeasure μG] (f : Fin n → ℝ → ℝ)
    (hf : ∀ s, Measurable (f s)) (B : ℝ) (hb : ∀ s x, |f s x| ≤ B) (lam : ℝ) (hlam : 0 ≤ lam)
    (y : ℝ) :
    (Measure.pi fun _ : Fin n => μG) {m | y ≤ ∑ s, f s (m s)} ≤
      ENNReal.ofReal (Real.exp (-lam * y) * ∏ s, ∫ x, Real.exp (lam * f s x) ∂μG) := by
  set μ := Measure.pi fun _ : Fin n => μG
  have hmeas : Measurable (fun m : Fin n → ℝ => ∑ s, f s (m s)) :=
    Finset.measurable_sum _ (fun s _ => (hf s).comp (measurable_pi_apply s))
  have hint : Integrable (fun m : Fin n → ℝ => Real.exp (lam * ∑ s, f s (m s))) μ := by
    refine Integrable.of_bound (C := Real.exp (lam * (n * B))) ?_ ?_
    · exact (Real.measurable_exp.comp (hmeas.const_mul lam)).aestronglyMeasurable
    · refine ae_of_all _ (fun m => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hlam
      calc ∑ s, f s (m s) ≤ ∑ _s : Fin n, B :=
            Finset.sum_le_sum (fun s _ => le_trans (le_abs_self _) (hb s _))
        _ = n * B := by simp
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  refine (measure_ge_le_exp_mul_mgf y hlam hint).trans_eq ?_
  congr 1
  unfold mgf
  have : (fun m : Fin n → ℝ => Real.exp (lam * ∑ s, f s (m s))) =
      fun m => ∏ s, Real.exp (lam * f s (m s)) := by
    funext m
    rw [Finset.mul_sum, Real.exp_sum]
  rw [this]
  exact integral_fintype_prod_eq_prod (fun s x => Real.exp (lam * f s x))

theorem exp_le_quad_of_nonpos (y : ℝ) (hy : y ≤ 0) : Real.exp y ≤ 1 + y + y ^ 2 / 2 := by
  set x := -y with hx
  have hx0 : 0 ≤ x := by linarith
  have hc := Real.sum_le_exp_of_nonneg hx0 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hc
  norm_num [Nat.factorial] at hc
  have hpos : 0 < 1 - x + x ^ 2 / 2 := by nlinarith [sq_nonneg (x - 1)]
  have key : 1 ≤ Real.exp x * (1 - x + x ^ 2 / 2) := by
    have h1 : (1 + x + x ^ 2 / 2 + x ^ 3 / 6) * (1 - x + x ^ 2 / 2) ≤
        Real.exp x * (1 - x + x ^ 2 / 2) := mul_le_mul_of_nonneg_right (by linarith) hpos.le
    have h2 : 1 ≤ (1 + x + x ^ 2 / 2 + x ^ 3 / 6) * (1 - x + x ^ 2 / 2) := by
      have : (1 + x + x ^ 2 / 2 + x ^ 3 / 6) * (1 - x + x ^ 2 / 2) =
          1 + x ^ 3 / 6 + x ^ 4 / 12 + x ^ 5 / 12 := by ring
      rw [this]
      have : 0 ≤ x ^ 3 / 6 + x ^ 4 / 12 + x ^ 5 / 12 := by positivity
      linarith
    linarith
  have hy' : y = -x := by simp [hx]
  rw [hy', Real.exp_neg]
  rw [inv_le_iff_one_le_mul₀ (Real.exp_pos x)]
  nlinarith

/-- Pointwise Bernstein bound: `e^y ≤ 1 + y + y²/(2(1-θ/3))` for `y ≤ θ < 3`, `0 ≤ θ`. -/
theorem exp_le_bern (y θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 3) (hy : y ≤ θ) :
    Real.exp y ≤ 1 + y + y ^ 2 / (2 * (1 - θ / 3)) := by
  have hden : 0 < 2 * (1 - θ / 3) := by linarith
  rcases le_or_gt y 0 with h | h
  · have := exp_le_quad_of_nonpos y h
    have : y ^ 2 / 2 ≤ y ^ 2 / (2 * (1 - θ / 3)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) hden; linarith
    linarith
  · have hb := bernstein_exp_le y h.le (by linarith)
    have : y ^ 2 / (2 * (1 - y / 3)) ≤ y ^ 2 / (2 * (1 - θ / 3)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) hden; linarith
    linarith

/-- MGF bound for a centred bounded variable. -/
theorem mgf_bern (μG : Measure ℝ) [IsProbabilityMeasure μG] (g : ℝ → ℝ) (hg : Measurable g)
    (c : ℝ) (hb : ∀ x, |g x| ≤ c) (hmean : ∫ x, g x ∂μG = 0) (lam : ℝ) (hlam : 0 ≤ lam)
    (hlc : lam * c < 3) :
    ∫ x, Real.exp (lam * g x) ∂μG ≤
      Real.exp (lam ^ 2 * (∫ x, g x ^ 2 ∂μG) / (2 * (1 - lam * c / 3))) := by
  have hc0 : 0 ≤ c := le_trans (abs_nonneg _) (hb 0)
  have hθ0 : 0 ≤ lam * c := mul_nonneg hlam hc0
  have hden : 0 < 2 * (1 - lam * c / 3) := by linarith
  have hgi : Integrable g μG :=
    Integrable.of_bound hg.aestronglyMeasurable c (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs]; exact hb x))
  have hg2i : Integrable (fun x => g x ^ 2) μG :=
    Integrable.of_bound (hg.pow_const 2).aestronglyMeasurable (c ^ 2) (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb x) 2))
  have hpt : ∀ x, Real.exp (lam * g x) ≤
      1 + lam * g x + lam ^ 2 / (2 * (1 - lam * c / 3)) * g x ^ 2 := by
    intro x
    have hy : lam * g x ≤ lam * c :=
      mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hb x)) hlam
    have := exp_le_bern (lam * g x) (lam * c) hθ0 hlc hy
    calc Real.exp (lam * g x) ≤ 1 + lam * g x + (lam * g x) ^ 2 / (2 * (1 - lam * c / 3)) := this
      _ = 1 + lam * g x + lam ^ 2 / (2 * (1 - lam * c / 3)) * g x ^ 2 := by ring
  have hei : Integrable (fun x => Real.exp (lam * g x)) μG :=
    Integrable.of_bound (Real.measurable_exp.comp (hg.const_mul lam)).aestronglyMeasurable
      (Real.exp (lam * c)) (ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
          (le_trans (le_abs_self _) (hb x)) hlam)))
  have hrhs : Integrable (fun x => 1 + lam * g x + lam ^ 2 / (2 * (1 - lam * c / 3)) * g x ^ 2)
      μG := ((integrable_const _).add (hgi.const_mul _)).add (hg2i.const_mul _)
  calc ∫ x, Real.exp (lam * g x) ∂μG
      ≤ ∫ x, (1 + lam * g x + lam ^ 2 / (2 * (1 - lam * c / 3)) * g x ^ 2) ∂μG :=
        integral_mono hei hrhs hpt
    _ = 1 + lam ^ 2 * (∫ x, g x ^ 2 ∂μG) / (2 * (1 - lam * c / 3)) := by
        have e1 : ∫ x, (1 + lam * g x + lam ^ 2 / (2 * (1 - lam * c / 3)) * g x ^ 2) ∂μG =
            ∫ x, (1 + lam * g x) ∂μG + ∫ x, lam ^ 2 / (2 * (1 - lam * c / 3)) * g x ^ 2 ∂μG :=
          integral_add ((integrable_const _).add (hgi.const_mul _)) (hg2i.const_mul _)
        have e2 : ∫ x, (1 + lam * g x) ∂μG = ∫ _x, (1 : ℝ) ∂μG + ∫ x, lam * g x ∂μG :=
          integral_add (integrable_const _) (hgi.const_mul _)
        rw [e1, e2, integral_const_mul, integral_const_mul, hmean]
        simp; ring
    _ ≤ _ := by
        have := Real.add_one_le_exp (lam ^ 2 * (∫ x, g x ^ 2 ∂μG) / (2 * (1 - lam * c / 3)))
        linarith

/-- **Bernstein's inequality** for a sum of independent coordinates under a product measure. -/
theorem bernstein_pi {n : ℕ} (μG : Measure ℝ) [IsProbabilityMeasure μG] (g : Fin n → ℝ → ℝ)
    (hg : ∀ k, Measurable (g k)) (c : ℝ) (hc : 0 < c) (hb : ∀ k x, |g k x| ≤ c)
    (hmean : ∀ k, ∫ x, g k x ∂μG = 0) (W : ℝ) (hW : 0 < W)
    (hvar : ∑ k, ∫ x, g k x ^ 2 ∂μG ≤ W) (ε : ℝ) (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin n => μG) {m | ε ≤ ∑ k, g k (m k)} ≤
      ENNReal.ofReal (Real.exp (-(ε ^ 2 / (2 * (W + c * ε / 3))))) := by
  have hD : 0 < W + c * ε / 3 := by positivity
  set lam := ε / (W + c * ε / 3) with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hε hD.le
  have hlc : lam * c < 3 := by
    rw [hlam, div_mul_eq_mul_div, div_lt_iff₀ hD]
    nlinarith
  refine le_trans (chernoff_pi μG g hg c hb lam hlam0 ε) (ENNReal.ofReal_le_ofReal ?_)
  have hden : 0 < 2 * (1 - lam * c / 3) := by linarith
  have hprod : ∏ k, ∫ x, Real.exp (lam * g k x) ∂μG ≤
      Real.exp (lam ^ 2 * W / (2 * (1 - lam * c / 3))) := by
    calc ∏ k, ∫ x, Real.exp (lam * g k x) ∂μG
        ≤ ∏ k : Fin n, Real.exp (lam ^ 2 * (∫ x, g k x ^ 2 ∂μG) / (2 * (1 - lam * c / 3))) :=
          Finset.prod_le_prod (fun k _ => integral_nonneg (fun x => (Real.exp_pos _).le))
            (fun k _ => mgf_bern μG (g k) (hg k) c (hb k) (hmean k) lam hlam0 hlc)
      _ = Real.exp (lam ^ 2 * (∑ k, ∫ x, g k x ^ 2 ∂μG) / (2 * (1 - lam * c / 3))) := by
          rw [← Real.exp_sum]; congr 1
          rw [Finset.mul_sum, Finset.sum_div]
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          apply div_le_div_of_nonneg_right _ hden.le
          exact mul_le_mul_of_nonneg_left hvar (sq_nonneg _)
  refine le_trans (mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le) ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  -- algebra: -lam ε + lam² W / (2(1 - lam c/3)) = -ε²/(2(W + cε/3))
  have h1 : 1 - lam * c / 3 = W / (W + c * ε / 3) := by
    rw [hlam]; field_simp; ring
  rw [h1, hlam]
  have : -(ε / (W + c * ε / 3)) * ε + (ε / (W + c * ε / 3)) ^ 2 * W /
      (2 * (W / (W + c * ε / 3))) = -(ε ^ 2 / (2 * (W + c * ε / 3))) := by
    field_simp; ring
  rw [this]

/-- Independence of events depending on disjoint sets of coordinates. -/
theorem indep_pi {n : ℕ} (μG : Measure ℝ) [IsProbabilityMeasure μG] (S : Finset (Fin n))
    (E D : Set (Fin n → ℝ)) (hE : MeasurableSet E) (hD : MeasurableSet D)
    (hEdep : ∀ m m' : Fin n → ℝ, (∀ k ∈ S, m k = m' k) → (m ∈ E ↔ m' ∈ E))
    (hDdep : ∀ m m' : Fin n → ℝ, (∀ k ∈ Sᶜ, m k = m' k) → (m ∈ D ↔ m' ∈ D)) :
    (Measure.pi fun _ : Fin n => μG) (E ∩ D) =
      (Measure.pi fun _ : Fin n => μG) E * (Measure.pi fun _ : Fin n => μG) D := by
  have hind : iIndepFun (fun k (m : Fin n → ℝ) => m k) (Measure.pi fun _ : Fin n => μG) :=
    iIndepFun_pi (X := fun _ x => x) (fun _ => measurable_id.aemeasurable)
  have h2 := hind.indepFun_finset S Sᶜ disjoint_compl_right (fun k => measurable_pi_apply k)
  let ext1 : (S → ℝ) → (Fin n → ℝ) := fun x k => if h : k ∈ S then x ⟨k, h⟩ else 0
  let ext2 : ((Sᶜ : Finset (Fin n)) → ℝ) → (Fin n → ℝ) :=
    fun x k => if h : k ∈ Sᶜ then x ⟨k, h⟩ else 0
  have hm1 : Measurable ext1 := by
    apply measurable_pi_lambda; intro k
    by_cases h : k ∈ S
    · simp only [ext1, dif_pos h]; exact measurable_pi_apply _
    · simp only [ext1, dif_neg h]; exact measurable_const
  have hm2 : Measurable ext2 := by
    apply measurable_pi_lambda; intro k
    by_cases h : k ∈ Sᶜ
    · simp only [ext2, dif_pos h]; exact measurable_pi_apply _
    · simp only [ext2, dif_neg h]; exact measurable_const
  have hE' : (fun m (k : S) => m k) ⁻¹' (ext1 ⁻¹' E) = E := by
    ext m
    simp only [Set.mem_preimage]
    apply (hEdep m _ _).symm
    intro k hk; simp [ext1, hk]
  have hD' : (fun m (k : (Sᶜ : Finset (Fin n))) => m k) ⁻¹' (ext2 ⁻¹' D) = D := by
    ext m
    simp only [Set.mem_preimage]
    apply (hDdep m _ _).symm
    intro k hk
    have hk' : k ∉ S := Finset.mem_compl.mp hk
    simp [ext2, hk']
  have := h2.measure_inter_preimage_eq_mul (ext1 ⁻¹' E) (ext2 ⁻¹' D) (hm1 hE) (hm2 hD)
  rwa [hE', hD'] at this

end FPA2bConc


open MeasureTheory ProbabilityTheory

namespace FPA2bTgt

open FirstPriceLearning.Adversarial FPA2bLib FPA2bConc

/-- The record entry truncated at level `ℓ`: entries of a level above `ℓ` are forgotten. -/
def trunc (ℓ : ℕ) (r : ℕ × ℕ) : Option (ℕ × ℕ) := if r.1 ≤ ℓ then some r else none

theorem trunc_level_iff {ℓ ℓ' : ℕ} {r r' : ℕ × ℕ} (h : trunc ℓ r = trunc ℓ r') (hℓ' : ℓ' ≤ ℓ) :
    r.1 = ℓ' ↔ r'.1 = ℓ' := by
  unfold trunc at h
  constructor
  · intro hr
    rw [if_pos (by omega)] at h
    split_ifs at h with h'
    · rw [← Option.some.inj h]; exact hr
  · intro hr
    rw [if_pos (show r'.1 ≤ ℓ by omega)] at h
    split_ifs at h with h'
    · rw [Option.some.inj h]; exact hr

theorem trunc_eq_of_le {ℓ : ℕ} {r r' : ℕ × ℕ} (h : trunc ℓ r = trunc ℓ r') (hr : r.1 ≤ ℓ) :
    r = r' := by
  unfold trunc at h
  rw [if_pos hr] at h
  split_ifs at h with h'
  exact Option.some.inj h

section tcongr

variable (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (ℓ : ℕ) (y y' v : ℕ → ℝ)
  (rec rec' : ℕ → ℕ × ℕ) (t : ℕ)
  (H : ∀ u, u < t → trunc ℓ (rec u) = trunc ℓ (rec' u))
  (HY : ∀ u, 1 ≤ u → u < t → (rec u).1 < ℓ → y u = y' u)

include H in
theorem levelSet_T (ℓ' : ℕ) (hℓ' : ℓ' ≤ ℓ) (u : ℕ) (hu : u < t) :
    levelSet rec ℓ' u = levelSet rec' ℓ' u := by
  unfold levelSet
  apply Finset.filter_congr
  intro s hs
  rw [Finset.mem_Icc] at hs
  exact trunc_level_iff (H s (by omega)) hℓ'

include H in
theorem nObs_T (ht : 1 ≤ t) (ℓ' : ℕ) (hℓ' : ℓ' ≤ ℓ) (i : ℕ) :
    nObs T rec ℓ' i t = nObs T rec' ℓ' i t := by
  unfold nObs obsCount
  rw [levelSet_T ℓ rec rec' t H ℓ' hℓ' (t - 1) (by omega)]
  congr 1
  apply Finset.filter_congr
  intro s hs
  unfold levelSet at hs
  simp only [Finset.mem_filter, Finset.mem_Icc] at hs
  have hr := trunc_eq_of_le (H s (by omega)) (by
    have := (trunc_level_iff (H s (by omega)) hℓ').mpr hs.2
    omega)
  simp only [hr]

include H HY in
theorem phat0_T (ht : initLength T < t) (hℓ : 1 ≤ ℓ) (j : ℕ) :
    phat0 T rec y j = phat0 T rec' y' j := by
  unfold phat0
  rw [levelSet_T ℓ rec rec' t H 0 (by omega) (initLength T) ht]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  unfold levelSet at hs
  simp only [Finset.mem_filter, Finset.mem_Icc] at hs
  have hlev : (rec s).1 = 0 := (trunc_level_iff (H s (by omega)) (Nat.zero_le ℓ)).mpr hs.2
  rw [HY s hs.1.1 (by omega) (by omega)]

include H HY in
theorem width_T (ht : initLength T < t) (hℓ : 1 ≤ ℓ) (ℓ' : ℕ) (hℓ' : ℓ' ≤ ℓ) (i : ℕ) :
    width T γ rec y ℓ' i t = width T γ rec' y' ℓ' i t := by
  unfold width
  have h1 : 1 ≤ t := by omega
  simp only [nObs_T T ℓ rec rec' t H h1 ℓ' hℓ', phat0_T T ℓ y y' rec rec' t H HY ht hℓ]

include H HY in
theorem phat_T (ht : 1 ≤ t) (ℓ' : ℕ) (hℓ' : ℓ' < ℓ) (i : ℕ) :
    phat T rec y ℓ' i t = phat T rec' y' ℓ' i t := by
  unfold phat
  rw [nObs_T T ℓ rec rec' t H ht ℓ' hℓ'.le, levelSet_T ℓ rec rec' t H ℓ' hℓ'.le (t - 1) (by omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  unfold levelSet at hs
  simp only [Finset.mem_filter, Finset.mem_Icc] at hs
  have hlev : (rec' s).1 = ℓ' := hs.2
  have hlev' : (rec s).1 = ℓ' := (trunc_level_iff (H s (by omega)) hℓ'.le).mpr hlev
  have hr := trunc_eq_of_le (H s (by omega)) (by omega)
  rw [hr, HY s hs.1.1 (by omega) (by omega)]

include H HY in
theorem rhat_T (ht : 1 ≤ t) (ℓ' : ℕ) (hℓ' : ℓ' < ℓ) (i : ℕ) :
    rhat T rec y v ℓ' i t = rhat T rec' y' v ℓ' i t := by
  unfold rhat
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  exact phat_T T ℓ y y' rec rec' t H HY ht ℓ' hℓ' j

include H HY in
theorem cand_T (ht : initLength T < t) (hℓ : 1 ≤ ℓ) (ℓ' : ℕ) (hℓ' : ℓ' < ℓ) :
    cand T γ rec y v t ℓ' = cand T γ rec' y' v t ℓ' := by
  induction ℓ' with
  | zero => rfl
  | succ k ih =>
    have h1 : 1 ≤ t := by omega
    ext i
    rw [mem_cand_succ, mem_cand_succ, ih (by omega)]
    simp only [rhat_T T ℓ y y' v rec rec' t H HY h1 (k + 1) hℓ',
      width_T T γ ℓ y y' rec rec' t H HY ht hℓ (k + 1) hℓ'.le]

include H HY in
theorem explore_T (ht : initLength T < t) (hℓ : 1 ≤ ℓ) (ℓ' : ℕ) (hℓ' : ℓ' ≤ ℓ) :
    exploreSet T γ rec y v ℓ' t = exploreSet T γ rec' y' v ℓ' t := by
  unfold exploreSet
  rw [cand_T T γ ℓ y y' v rec rec' t H HY ht hℓ (ℓ' - 1) (by omega)]
  apply Finset.filter_congr
  intro i _
  rw [width_T T γ ℓ y y' rec rec' t H HY ht hℓ ℓ' hℓ' i]

include H HY in
theorem decide_T (ht : initLength T < t) (hℓ : 1 ≤ ℓ) :
    trunc ℓ (decideRound T γ sel rec y v t) = trunc ℓ (decideRound T γ sel rec' y' v t) := by
  have hmem : ∀ ℓ', ℓ' ≤ ℓ → (ℓ' ∈ breakLevels T γ rec y v t ↔
      ℓ' ∈ breakLevels T γ rec' y' v t) := by
    intro ℓ' hℓ'
    unfold breakLevels
    simp only [Finset.mem_filter, explore_T T γ ℓ y y' v rec rec' t H HY ht hℓ ℓ' hℓ']
  have hle : ∀ x ∈ breakLevels T γ rec y v t, x ≤ numLevels T := by
    intro x hx; unfold breakLevels at hx
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1).2
  have hle' : ∀ x ∈ breakLevels T γ rec' y' v t, x ≤ numLevels T := by
    intro x hx; unfold breakLevels at hx
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1).2
  unfold decideRound trunc
  by_cases h1 : (breakLevels T γ rec y v t).Nonempty <;>
    by_cases h2 : (breakLevels T γ rec' y' v t).Nonempty
  · simp only [dif_pos h1, dif_pos h2]
    set a := (breakLevels T γ rec y v t).min' h1
    set a' := (breakLevels T γ rec' y' v t).min' h2
    by_cases ha : a ≤ ℓ
    · have ha1 : a ∈ breakLevels T γ rec' y' v t :=
        (hmem a ha).mp (Finset.min'_mem _ h1)
      have h3 : a' ≤ a := Finset.min'_le _ _ ha1
      have ha2 : a' ∈ breakLevels T γ rec y v t :=
        (hmem a' (by omega)).mpr (Finset.min'_mem _ h2)
      have h4 : a ≤ a' := Finset.min'_le _ _ ha2
      have hae : a = a' := le_antisymm h4 h3
      rw [← hae, explore_T T γ ℓ y y' v rec rec' t H HY ht hℓ a ha]
    · have ha' : ¬ a' ≤ ℓ := by
        intro ha'
        have ha2 : a' ∈ breakLevels T γ rec y v t :=
          (hmem a' ha').mpr (Finset.min'_mem _ h2)
        have := Finset.min'_le _ _ ha2
        omega
      simp only [ha, ha', if_false]
  · simp only [dif_pos h1, dif_neg h2]
    set a := (breakLevels T γ rec y v t).min' h1
    have ha : ¬ a ≤ ℓ := by
      intro ha
      exact h2 ⟨a, (hmem a ha).mp (Finset.min'_mem _ h1)⟩
    have hL : ¬ numLevels T ≤ ℓ := by
      have := hle a (Finset.min'_mem _ h1); omega
    simp only [ha, hL, if_false]
  · simp only [dif_neg h1, dif_pos h2]
    set a' := (breakLevels T γ rec' y' v t).min' h2
    have ha : ¬ a' ≤ ℓ := by
      intro ha
      exact h1 ⟨a', (hmem a' ha).mpr (Finset.min'_mem _ h2)⟩
    have hL : ¬ numLevels T ≤ ℓ := by
      have := hle' a' (Finset.min'_mem _ h2); omega
    simp only [ha, hL, if_false]
  · simp only [dif_neg h1, dif_neg h2]

end tcongr

/-! ### The run -/

theorem feedback_eq (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v m : Fin T → ℝ) (u : ℕ)
    (h1 : 1 ≤ u) (h2 : u ≤ T) :
    runFeedback T γ sel v m u =
      max (grid (numGrid T) (runRecord T γ sel v m u).2) (m ⟨u - 1, by omega⟩) := by
  unfold runFeedback paperSeq
  rw [dif_pos ⟨h1, h2⟩]
  simp only
  rw [mlBids_eq]
  unfold runIndex
  have : u - 1 + 1 = u := by omega
  simp only [this]

theorem meas_feedback (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v : Fin T → ℝ) (u : ℕ) :
    Measurable (fun m : Fin T → ℝ => runFeedback T γ sel v m u) := by
  unfold runFeedback paperSeq
  by_cases h : 1 ≤ u ∧ u ≤ T
  · simp only [dif_pos h]
    apply Measurable.max _ (measurable_pi_apply _)
    unfold mlBids runBids
    exact meas_runBidsNat (mlRule T γ sel) (meas_mlRule T γ sel) v _
  · simp only [dif_neg h]; exact measurable_const

theorem meas_runRecord (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v : Fin T → ℝ) (u : ℕ) :
    Measurable (fun m : Fin T → ℝ => runRecord T γ sel v m u) := by
  unfold runRecord
  exact meas_record T γ sel (fun _ => paperSeq v) (fun m => runFeedback T γ sel v m)
    (fun _ => measurable_const) (fun s => meas_feedback T γ sel v s) u

/-- **Lemma 6 (independence), formal core.** The record truncated at level `ℓ` up to time `t`
depends only on the HOBs of the rounds `u < t` whose level is `< ℓ`. -/
theorem run_trunc_local (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v : Fin T → ℝ)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (m m' : Fin T → ℝ) (t : ℕ) (htT : t ≤ T + 1)
    (h : ∀ u (hu1 : 1 ≤ u) (hut : u < t), (runRecord T γ sel v m u).1 < ℓ →
      m ⟨u - 1, by omega⟩ = m' ⟨u - 1, by omega⟩) :
    ∀ u, u < t → trunc ℓ (runRecord T γ sel v m u) = trunc ℓ (runRecord T γ sel v m' u) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hu0 : u ≤ initLength T
    · unfold runRecord
      rw [record_le T γ sel _ _ u hu0, record_le T γ sel _ _ u hu0]
    · push Not at hu0
      have e1 : runRecord T γ sel v m u = decideRound T γ sel (runRecord T γ sel v m)
          (runFeedback T γ sel v m) (paperSeq v) u := by
        unfold runRecord runFeedback; rw [record_gt T γ sel _ _ u hu0]
      have e2 : runRecord T γ sel v m' u = decideRound T γ sel (runRecord T γ sel v m')
          (runFeedback T γ sel v m') (paperSeq v) u := by
        unfold runRecord runFeedback; rw [record_gt T γ sel _ _ u hu0]
      rw [e1, e2]
      apply decide_T T γ sel ℓ _ _ (paperSeq v) _ _ u
      · intro u' hu'; exact ih u' hu' (by omega)
      · intro u' h1 h2 hlev
        have htr := ih u' h2 (by omega)
        have hr := trunc_eq_of_le htr (by omega)
        rw [feedback_eq T γ sel v m u' h1 (by omega), feedback_eq T γ sel v m' u' h1 (by omega),
          hr, h u' h1 (by omega) hlev]
      · exact hu0
      · exact hℓ

/-! ### The level-`ℓ` estimation error as a sum over level-`ℓ` HOBs -/

/-- Indicator of the `j`-th grid interval `(b^j, b^{j+1}]`. -/
noncomputable def ind (K j : ℕ) (x : ℝ) : ℝ :=
  if grid K j < x ∧ x ≤ grid K (j + 1) then 1 else 0

/-- The weight `𝟙(b_s ≤ b^j) / n^ℓ_{j,t}` of the round `s`. -/
noncomputable def wt (T : ℕ) (rec : ℕ → ℕ × ℕ) (ℓ t s j : ℕ) : ℝ :=
  if grid (numGrid T) (rec s).2 ≤ grid (numGrid T) j then 1 / (nObs T rec ℓ j t : ℝ) else 0

/-- The centred contribution `X_s` of round `s = k + 1` (zero unless `s ∈ Φ^ℓ(t-1)`). -/
noncomputable def Gf (T : ℕ) (μG : Measure ℝ) (rec : ℕ → ℕ × ℕ) (ℓ i t : ℕ) (k : Fin T)
    (x : ℝ) : ℝ :=
  if k.val + 1 ∈ levelSet rec ℓ (t - 1) then
    ∑ j ∈ Finset.Ico i (numGrid T), wt T rec ℓ t (k.val + 1) j *
      (ind (numGrid T) j x - intervalProb T μG j)
  else 0

theorem paperSeq_succ' {T : ℕ} (x : Fin T → ℝ) (k : Fin T) : paperSeq x (k.val + 1) = x k := by
  unfold paperSeq
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1

theorem feedback_eq' (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v m : Fin T → ℝ) (u : ℕ)
    (h1 : 1 ≤ u) (h2 : u ≤ T) :
    runFeedback T γ sel v m u = max (grid (numGrid T) (runRecord T γ sel v m u).2) (paperSeq m u) := by
  rw [feedback_eq T γ sel v m u h1 h2]
  unfold paperSeq
  rw [dif_pos ⟨h1, h2⟩]

theorem ind_max (K j : ℕ) (b x : ℝ) (hb : b ≤ grid K j) :
    ind K j (max b x) = ind K j x := by
  unfold ind
  by_cases hx : b ≤ x
  · rw [max_eq_right hx]
  · push Not at hx
    rw [max_eq_left hx.le]
    have h1 : ¬ (grid K j < b ∧ b ≤ grid K (j + 1)) := fun h => by linarith [h.1]
    have h2 : ¬ (grid K j < x ∧ x ≤ grid K (j + 1)) := fun h => by linarith [h.1]
    simp [h1, h2]

theorem nObs_eq_sum (T : ℕ) (rec : ℕ → ℕ × ℕ) (ℓ j t : ℕ) (ht : 1 ≤ t) :
    (nObs T rec ℓ j t : ℝ) = ∑ s ∈ levelSet rec ℓ (t - 1),
      (if grid (numGrid T) (rec s).2 ≤ grid (numGrid T) j then (1 : ℝ) else 0) := by
  unfold nObs obsCount
  rw [Finset.sum_boole]
  congr 2
  apply Finset.filter_congr
  intro s hs
  unfold levelSet at hs
  simp only [Finset.mem_filter, Finset.mem_Icc] at hs
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by omega, h⟩

/-- For a run whose truncated record agrees with that of `m0` before `t`, the level-`ℓ`
estimation error is the sum of the centred contributions of the level-`ℓ` HOBs. -/
theorem err_eq (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v : Fin T → ℝ)
    (μG : Measure ℝ) (ℓ i t : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) (m m0 : Fin T → ℝ)
    (hag : ∀ u, u < t → trunc ℓ (runRecord T γ sel v m u) = trunc ℓ (runRecord T γ sel v m0 u))
    (hn : ∀ j, 0 < nObs T (runRecord T γ sel v m0) ℓ j t) :
    ∑ j ∈ Finset.Ico i (numGrid T),
        (phat T (runRecord T γ sel v m) (runFeedback T γ sel v m) ℓ j t - intervalProb T μG j) =
      ∑ k : Fin T, Gf T μG (runRecord T γ sel v m0) ℓ i t k (m k) := by
  set R := runRecord T γ sel v m
  set R0 := runRecord T γ sel v m0
  set Φ0 := levelSet R0 ℓ (t - 1)
  have hΦ : levelSet R ℓ (t - 1) = Φ0 := levelSet_T ℓ R R0 t hag ℓ le_rfl (t - 1) (by omega)
  have hmemΦ : ∀ s ∈ Φ0, 1 ≤ s ∧ s ≤ t - 1 := by
    intro s hs
    simp only [Φ0, levelSet, Finset.mem_filter, Finset.mem_Icc] at hs
    exact hs.1
  have hRs : ∀ s ∈ Φ0, R s = R0 s := by
    intro s hs
    have h1 := hmemΦ s hs
    have hl : (R0 s).1 = ℓ := by
      simp only [Φ0, levelSet, Finset.mem_filter] at hs; exact hs.2
    exact trunc_eq_of_le (hag s (by omega)) (by
      have := (trunc_level_iff (hag s (by omega)) le_rfl).mpr hl; omega)
  -- each `phat_j - p_j`
  have hj : ∀ j, phat T R (runFeedback T γ sel v m) ℓ j t - intervalProb T μG j =
      ∑ s ∈ Φ0, wt T R0 ℓ t s j * (ind (numGrid T) j (paperSeq m s) - intervalProb T μG j) := by
    intro j
    have hnj : (nObs T R0 ℓ j t : ℝ) ≠ 0 := by
      have := hn j; positivity
    have hcount := nObs_eq_sum T R0 ℓ j t ht
    unfold phat
    rw [nObs_T T ℓ R R0 t hag ht ℓ le_rfl j, hΦ]
    have e1 : ∑ s ∈ Φ0, (if grid (numGrid T) (R s).2 ≤ grid (numGrid T) j then (1 : ℝ) else 0) *
        (if grid (numGrid T) j < runFeedback T γ sel v m s ∧
          runFeedback T γ sel v m s ≤ grid (numGrid T) (j + 1) then (1 : ℝ) else 0) =
        ∑ s ∈ Φ0, (if grid (numGrid T) (R0 s).2 ≤ grid (numGrid T) j then (1 : ℝ) else 0) *
          ind (numGrid T) j (paperSeq m s) := by
      apply Finset.sum_congr rfl
      intro s hs
      have h1 := hmemΦ s hs
      rw [hRs s hs]
      by_cases hg : grid (numGrid T) (R0 s).2 ≤ grid (numGrid T) j
      · rw [if_pos hg, one_mul, one_mul]
        rw [show (if grid (numGrid T) j < runFeedback T γ sel v m s ∧
          runFeedback T γ sel v m s ≤ grid (numGrid T) (j + 1) then (1 : ℝ) else 0) =
          ind (numGrid T) j (runFeedback T γ sel v m s) from rfl,
          feedback_eq' T γ sel v m s h1.1 (by omega)]
        rw [show (runRecord T γ sel v m s) = R0 s from hRs s hs, ind_max _ _ _ _ hg]
      · rw [if_neg hg]; ring
    rw [e1]
    have hsumw : ∑ s ∈ Φ0, wt T R0 ℓ t s j = 1 := by
      unfold wt
      have : ∀ s ∈ Φ0, (if grid (numGrid T) (R0 s).2 ≤ grid (numGrid T) j then
          1 / (nObs T R0 ℓ j t : ℝ) else 0) = 1 / (nObs T R0 ℓ j t : ℝ) *
          (if grid (numGrid T) (R0 s).2 ≤ grid (numGrid T) j then (1 : ℝ) else 0) := by
        intro s _; split_ifs <;> ring
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum, ← hcount]
      field_simp
    have e3 : ∀ s ∈ Φ0, wt T R0 ℓ t s j * (ind (numGrid T) j (paperSeq m s) - intervalProb T μG j)
        = wt T R0 ℓ t s j * ind (numGrid T) j (paperSeq m s) -
          wt T R0 ℓ t s j * intervalProb T μG j := fun s _ => by ring
    rw [Finset.sum_congr rfl e3, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumw, one_mul,
      Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    unfold wt
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_comm]
  -- reindex `Φ0` by `Fin T`
  unfold Gf
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun k _ => k.val + 1) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact hk
  · intro a _ b _ hab
    exact Fin.ext (by omega)
  · intro s hs
    have h1 := hmemΦ s hs
    refine ⟨⟨s - 1, by omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have : s - 1 + 1 = s := by omega
      rw [this]; exact hs
    · simp only; omega
  · intro k _
    rw [paperSeq_succ']

/-! ### Rewards and interval probabilities -/

theorem intervalProb_eq (T : ℕ) (μG : Measure ℝ) [IsProbabilityMeasure μG] (j : ℕ) :
    intervalProb T μG j =
      μG.real (Set.Ioc (grid (numGrid T) j) (grid (numGrid T) (j + 1))) := by
  have hab : grid (numGrid T) j ≤ grid (numGrid T) (j + 1) := by
    unfold grid
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    push_cast; linarith
  unfold intervalProb FirstPriceLearning.Stochastic.cdf
  rw [← Set.Iic_union_Ioc_eq_Iic hab]
  rw [show (μG (Set.Iic (grid (numGrid T) j) ∪
      Set.Ioc (grid (numGrid T) j) (grid (numGrid T) (j + 1)))).toReal =
      μG.real (Set.Iic (grid (numGrid T) j) ∪
      Set.Ioc (grid (numGrid T) j) (grid (numGrid T) (j + 1))) from rfl]
  rw [measureReal_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
  simp [Measure.real]

theorem cdf_one (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    FirstPriceLearning.Stochastic.cdf μG 1 = 1 := by
  unfold FirstPriceLearning.Stochastic.cdf
  have h : μG (Set.Iic (1 : ℝ))ᶜ = 0 := by
    apply measure_mono_null _ hG
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Iic, not_le] at hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and, not_le]
    intro _; exact hx
  rw [prob_compl_eq_zero_iff measurableSet_Iic] at h
  rw [h]; simp

theorem sum_p (T : ℕ) (μG : Measure ℝ) [IsProbabilityMeasure μG]
    (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0) (hK : 1 ≤ numGrid T) (i : ℕ) (hi : i ≤ numGrid T) :
    ∑ j ∈ Finset.Ico i (numGrid T), intervalProb T μG j =
      1 - FirstPriceLearning.Stochastic.cdf μG (grid (numGrid T) i) := by
  unfold intervalProb
  rw [Finset.sum_Ico_eq_sum_range]
  have := Finset.sum_range_sub
    (fun k => FirstPriceLearning.Stochastic.cdf μG (grid (numGrid T) (i + k))) (numGrid T - i)
  rw [show (∑ k ∈ Finset.range (numGrid T - i),
      (FirstPriceLearning.Stochastic.cdf μG (grid (numGrid T) (i + k + 1)) -
        FirstPriceLearning.Stochastic.cdf μG (grid (numGrid T) (i + k)))) =
      ∑ k ∈ Finset.range (numGrid T - i),
      (FirstPriceLearning.Stochastic.cdf μG (grid (numGrid T) (i + (k + 1))) -
        FirstPriceLearning.Stochastic.cdf μG (grid (numGrid T) (i + k))) from by
      apply Finset.sum_congr rfl; intro k _; rw [Nat.add_assoc]]
  rw [this, Nat.add_sub_cancel' hi, Nat.add_zero]
  have hgK : grid (numGrid T) (numGrid T) = 1 := by
    unfold grid; field_simp
  rw [hgK, cdf_one μG hG]

theorem rhat_sub (T : ℕ) (γ : ℝ) (sel : ℕ → ℕ → Finset ℕ → ℕ) (v m : Fin T → ℝ)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hK : 1 ≤ numGrid T) (ℓ i t : ℕ) (hi : i ≤ numGrid T) :
    runRhat T γ sel v m ℓ i t - gridReward μG v i t =
      -(paperSeq v t - grid (numGrid T) i) * ∑ j ∈ Finset.Ico i (numGrid T),
        (phat T (runRecord T γ sel v m) (runFeedback T γ sel v m) ℓ j t - intervalProb T μG j) := by
  unfold runRhat rhat gridReward FirstPriceLearning.Stochastic.expReward
  rw [Finset.sum_sub_distrib, sum_p T μG hG hK i hi]
  ring

/-! ### Properties of the centred contributions -/

theorem ind_meas (K j : ℕ) : Measurable (ind K j) := by
  unfold ind
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_lt measurable_const measurable_id).inter
    (measurableSet_le measurable_id measurable_const)

theorem ind_eq_indicator (K j : ℕ) (x : ℝ) :
    ind K j x = (Set.Ioc (grid K j) (grid K (j + 1))).indicator (1 : ℝ → ℝ) x := by
  unfold ind
  by_cases h : grid K j < x ∧ x ≤ grid K (j + 1)
  · have hx : x ∈ Set.Ioc (grid K j) (grid K (j + 1)) := h
    simp [h, hx]
  · have hx : x ∉ Set.Ioc (grid K j) (grid K (j + 1)) := h
    simp [h, hx]

theorem integral_ind (T : ℕ) (μG : Measure ℝ) [IsProbabilityMeasure μG] (j : ℕ) :
    ∫ x, ind (numGrid T) j x ∂μG = intervalProb T μG j := by
  rw [intervalProb_eq]
  simp only [ind_eq_indicator]
  exact integral_indicator_one measurableSet_Ioc

theorem ind_nonneg (K j : ℕ) (x : ℝ) : 0 ≤ ind K j x := by
  unfold ind; split_ifs <;> norm_num

theorem ind_le_one (K j : ℕ) (x : ℝ) : ind K j x ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

theorem ind_sq (K j : ℕ) (x : ℝ) : ind K j x ^ 2 = ind K j x := by
  unfold ind; split_ifs <;> norm_num

theorem sum_ind_le_one (K : ℕ) (hK : 1 ≤ K) (S : Finset ℕ) (x : ℝ) :
    ∑ j ∈ S, ind K j x ≤ 1 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold ind
  rw [Finset.sum_boole]
  have : (S.filter (fun j => grid K j < x ∧ x ≤ grid K (j + 1))).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    unfold grid at ha hb
    rw [div_lt_iff₀ hKr, le_div_iff₀ hKr] at ha hb
    push_cast at ha hb
    have h1 : (a : ℝ) < b + 1 := by nlinarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2]
    have h2 : (b : ℝ) < a + 1 := by nlinarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2]
    have h1' : a < b + 1 := by exact_mod_cast h1
    have h2' : b < a + 1 := by exact_mod_cast h2
    omega
  exact_mod_cast this

theorem cdf_nonneg' (μG : Measure ℝ) (x : ℝ) : 0 ≤ FirstPriceLearning.Stochastic.cdf μG x :=
  ENNReal.toReal_nonneg

theorem intervalProb_nonneg (T : ℕ) (μG : Measure ℝ) [IsProbabilityMeasure μG] (j : ℕ) :
    0 ≤ intervalProb T μG j := by
  rw [intervalProb_eq]; exact measureReal_nonneg

theorem nObs_mono (T : ℕ) (rec : ℕ → ℕ × ℕ) (ℓ t : ℕ) {i j : ℕ} (hij : i ≤ j) :
    nObs T rec ℓ i t ≤ nObs T rec ℓ j t := by
  unfold nObs obsCount
  apply Finset.card_le_card
  intro s hs
  simp only [Finset.mem_filter] at hs ⊢
  refine ⟨hs.1, hs.2.1, le_trans hs.2.2 ?_⟩
  unfold grid
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hij

theorem ind_integrable (K j : ℕ) (μG : Measure ℝ) [IsProbabilityMeasure μG] :
    Integrable (ind K j) μG :=
  Integrable.of_bound (ind_meas K j).aestronglyMeasurable 1 (ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (ind_nonneg K j x)]; exact ind_le_one K j x))

theorem sum_fin_reindex (T t : ℕ) (htT : t ≤ T) (Φ : Finset ℕ)
    (hΦ : ∀ s ∈ Φ, 1 ≤ s ∧ s ≤ t - 1) (F : ℕ → ℝ) :
    ∑ k : Fin T, (if k.val + 1 ∈ Φ then F (k.val + 1) else 0) = ∑ s ∈ Φ, F s := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun k _ => k.val + 1) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact hk
  · intro a _ b _ hab
    exact Fin.ext (by omega)
  · intro s hs
    have h1 := hΦ s hs
    refine ⟨⟨s - 1, by omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have : s - 1 + 1 = s := by omega
      rw [this]; exact hs
    · simp only; omega
  · intro k _; rfl

section gf

variable (T : ℕ) (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0)
  (rec : ℕ → ℕ × ℕ) (ℓ i t : ℕ) (hK : 1 ≤ numGrid T) (hi : i < numGrid T)
  (hn : ∀ j, 0 < nObs T rec ℓ j t)

include hn in
theorem wt_bounds (s j : ℕ) (hj : i ≤ j) :
    0 ≤ wt T rec ℓ t s j ∧ wt T rec ℓ t s j ≤ 1 / (nObs T rec ℓ i t : ℝ) := by
  unfold wt
  have hni : (0 : ℝ) < nObs T rec ℓ i t := by exact_mod_cast hn i
  have hnij : (nObs T rec ℓ i t : ℝ) ≤ nObs T rec ℓ j t := by
    exact_mod_cast nObs_mono T rec ℓ t hj
  split_ifs
  · refine ⟨by positivity, ?_⟩
    exact one_div_le_one_div_of_le hni hnij
  · exact ⟨le_rfl, by positivity⟩

theorem Gf_meas (k : Fin T) : Measurable (Gf T μG rec ℓ i t k) := by
  unfold Gf
  split_ifs
  · apply Finset.measurable_sum
    intro j _
    exact ((ind_meas _ j).sub measurable_const).const_mul _
  · exact measurable_const

include hG hK hn hi in
theorem Gf_bound (k : Fin T) (x : ℝ) :
    |Gf T μG rec ℓ i t k x| ≤ 1 / (nObs T rec ℓ i t : ℝ) := by
  set c := 1 / (nObs T rec ℓ i t : ℝ)
  have hc : 0 ≤ c := by positivity
  unfold Gf
  split_ifs
  · set S := Finset.Ico i (numGrid T)
    have hw := fun j (hj : j ∈ S) => wt_bounds T rec ℓ i t hn (k.val + 1) j (Finset.mem_Ico.mp hj).1
    have hsplit : ∑ j ∈ S, wt T rec ℓ t (k.val + 1) j * (ind (numGrid T) j x - intervalProb T μG j)
        = ∑ j ∈ S, wt T rec ℓ t (k.val + 1) j * ind (numGrid T) j x -
          ∑ j ∈ S, wt T rec ℓ t (k.val + 1) j * intervalProb T μG j := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; ring
    rw [hsplit]
    have hA0 : 0 ≤ ∑ j ∈ S, wt T rec ℓ t (k.val + 1) j * ind (numGrid T) j x :=
      Finset.sum_nonneg (fun j hj => mul_nonneg (hw j hj).1 (ind_nonneg _ _ _))
    have hA1 : ∑ j ∈ S, wt T rec ℓ t (k.val + 1) j * ind (numGrid T) j x ≤ c := by
      calc _ ≤ ∑ j ∈ S, c * ind (numGrid T) j x :=
            Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (hw j hj).2 (ind_nonneg _ _ _))
        _ = c * ∑ j ∈ S, ind (numGrid T) j x := by rw [Finset.mul_sum]
        _ ≤ c * 1 := mul_le_mul_of_nonneg_left (sum_ind_le_one _ hK S x) hc
        _ = c := mul_one c
    have hB0 : 0 ≤ ∑ j ∈ S, wt T rec ℓ t (k.val + 1) j * intervalProb T μG j :=
      Finset.sum_nonneg (fun j hj => mul_nonneg (hw j hj).1 (intervalProb_nonneg _ _ _))
    have hB1 : ∑ j ∈ S, wt T rec ℓ t (k.val + 1) j * intervalProb T μG j ≤ c := by
      calc _ ≤ ∑ j ∈ S, c * intervalProb T μG j :=
            Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (hw j hj).2
              (intervalProb_nonneg _ _ _))
        _ = c * ∑ j ∈ S, intervalProb T μG j := by rw [Finset.mul_sum]
        _ ≤ c * 1 := by
            apply mul_le_mul_of_nonneg_left _ hc
            rw [sum_p T μG hG hK i hi.le]
            linarith [cdf_nonneg' μG (grid (numGrid T) i)]
        _ = c := mul_one c
    rw [abs_le]; constructor <;> linarith
  · simp only [abs_zero]; positivity

theorem Gf_mean (k : Fin T) : ∫ x, Gf T μG rec ℓ i t k x ∂μG = 0 := by
  unfold Gf
  split_ifs
  · have hint : ∀ j ∈ Finset.Ico i (numGrid T), Integrable (fun x =>
        wt T rec ℓ t (k.val + 1) j * (ind (numGrid T) j x - intervalProb T μG j)) μG := by
      intro j _
      have := ((ind_integrable (numGrid T) j μG).sub
        (integrable_const (intervalProb T μG j))).const_mul (wt T rec ℓ t (k.val + 1) j)
      exact this
    rw [integral_finset_sum _ hint]
    apply Finset.sum_eq_zero
    intro j _
    rw [integral_const_mul]
    have : ∫ x, (ind (numGrid T) j x - intervalProb T μG j) ∂μG =
        ∫ x, ind (numGrid T) j x ∂μG - ∫ _x, intervalProb T μG j ∂μG :=
      integral_sub (ind_integrable _ j μG) (integrable_const _)
    rw [this, integral_ind]
    simp
  · simp

include hK in
theorem Gf_var (k : Fin T) :
    ∫ x, Gf T μG rec ℓ i t k x ^ 2 ∂μG ≤
      (if k.val + 1 ∈ levelSet rec ℓ (t - 1) then
        ∑ j ∈ Finset.Ico i (numGrid T), wt T rec ℓ t (k.val + 1) j ^ 2 * intervalProb T μG j
      else 0) := by
  unfold Gf
  split_ifs
  · set S := Finset.Ico i (numGrid T)
    set w := fun j => wt T rec ℓ t (k.val + 1) j
    set A := fun x => ∑ j ∈ S, w j * ind (numGrid T) j x
    set B := ∑ j ∈ S, w j * intervalProb T μG j
    have hAi : Integrable A μG :=
      integrable_finset_sum _ (fun j _ => (ind_integrable _ j μG).const_mul _)
    have hAmeas : Measurable A :=
      Finset.measurable_sum _ (fun j _ => (ind_meas _ j).const_mul _)
    have hA2i : Integrable (fun x => A x ^ 2) μG := by
      refine Integrable.of_bound (hAmeas.pow_const 2).aestronglyMeasurable
        ((∑ j ∈ S, |w j|) ^ 2) (ae_of_all _ (fun x => ?_))
      rw [Real.norm_eq_abs, abs_pow]
      apply pow_le_pow_left₀ (abs_nonneg _)
      calc |A x| ≤ ∑ j ∈ S, |w j * ind (numGrid T) j x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ S, |w j| := Finset.sum_le_sum (fun j _ => by
            rw [abs_mul, abs_of_nonneg (ind_nonneg _ _ _)]
            exact mul_le_of_le_one_right (abs_nonneg _) (ind_le_one _ _ _))
    have hEA : ∫ x, A x ∂μG = B := by
      simp only [A, B]
      rw [integral_finset_sum _ (fun j _ => (ind_integrable _ j μG).const_mul _)]
      apply Finset.sum_congr rfl; intro j _
      rw [integral_const_mul, integral_ind]
    have hrw : (fun x => (∑ j ∈ S, w j * (ind (numGrid T) j x - intervalProb T μG j)) ^ 2) =
        fun x => A x ^ 2 - 2 * B * A x + B ^ 2 := by
      funext x
      have : ∑ j ∈ S, w j * (ind (numGrid T) j x - intervalProb T μG j) = A x - B := by
        simp only [A, B]; rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
      rw [this]; ring
    have hI1 : Integrable (fun x => A x ^ 2 - 2 * B * A x) μG := by
      have := hA2i.sub (hAi.const_mul (2 * B)); exact this
    have e1 : ∫ x, (A x ^ 2 - 2 * B * A x + B ^ 2) ∂μG =
        ∫ x, (A x ^ 2 - 2 * B * A x) ∂μG + ∫ _x, B ^ 2 ∂μG :=
      integral_add hI1 (integrable_const _)
    have e2 : ∫ x, (A x ^ 2 - 2 * B * A x) ∂μG = ∫ x, A x ^ 2 ∂μG - ∫ x, 2 * B * A x ∂μG :=
      integral_sub hA2i (hAi.const_mul _)
    rw [hrw, e1, e2, integral_const_mul, hEA]
    have hu : μG.real Set.univ = 1 := by simp
    simp only [integral_const, hu, one_smul]
    -- `∫ A² ≤ Σ w² p`
    have hpt : ∀ x, A x ^ 2 ≤ ∑ j ∈ S, w j ^ 2 * ind (numGrid T) j x := by
      intro x
      have cs := Finset.sum_mul_sq_le_sq_mul_sq S (fun j => ind (numGrid T) j x)
        (fun j => w j * ind (numGrid T) j x)
      have e1 : ∑ j ∈ S, ind (numGrid T) j x * (w j * ind (numGrid T) j x) = A x := by
        simp only [A]; apply Finset.sum_congr rfl; intro j _
        rw [show ind (numGrid T) j x * (w j * ind (numGrid T) j x) =
          w j * ind (numGrid T) j x ^ 2 by ring, ind_sq]
      have e2 : ∑ j ∈ S, ind (numGrid T) j x ^ 2 = ∑ j ∈ S, ind (numGrid T) j x := by
        apply Finset.sum_congr rfl; intro j _; exact ind_sq _ _ _
      have e3 : ∑ j ∈ S, (w j * ind (numGrid T) j x) ^ 2 =
          ∑ j ∈ S, w j ^ 2 * ind (numGrid T) j x := by
        apply Finset.sum_congr rfl; intro j _
        rw [mul_pow, ind_sq]
      rw [e1, e2, e3] at cs
      have h0 : 0 ≤ ∑ j ∈ S, w j ^ 2 * ind (numGrid T) j x :=
        Finset.sum_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (ind_nonneg _ _ _))
      have h1 := sum_ind_le_one (numGrid T) hK S x
      nlinarith
    have hint2 : Integrable (fun x => ∑ j ∈ S, w j ^ 2 * ind (numGrid T) j x) μG :=
      integrable_finset_sum _ (fun j _ => (ind_integrable _ j μG).const_mul _)
    have hle := integral_mono hA2i hint2 hpt
    rw [integral_finset_sum _ (fun j _ => (ind_integrable _ j μG).const_mul _)] at hle
    simp only [integral_const_mul, integral_ind] at hle
    nlinarith [sq_nonneg B]
  · simp

include hn in
theorem var_sum (ht : 1 ≤ t) (htT : t ≤ T) :
    ∑ k : Fin T, (if k.val + 1 ∈ levelSet rec ℓ (t - 1) then
        ∑ j ∈ Finset.Ico i (numGrid T), wt T rec ℓ t (k.val + 1) j ^ 2 * intervalProb T μG j
      else 0) = ∑ j ∈ Finset.Ico i (numGrid T), intervalProb T μG j / (nObs T rec ℓ j t : ℝ) := by
  rw [sum_fin_reindex T t htT (levelSet rec ℓ (t - 1)) (by
      intro s hs; unfold levelSet at hs
      simp only [Finset.mem_filter, Finset.mem_Icc] at hs; exact hs.1)
    (fun s => ∑ j ∈ Finset.Ico i (numGrid T), wt T rec ℓ t s j ^ 2 * intervalProb T μG j)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hnj : (0 : ℝ) < nObs T rec ℓ j t := by exact_mod_cast hn j
  rw [← Finset.sum_mul]
  have : ∑ s ∈ levelSet rec ℓ (t - 1), wt T rec ℓ t s j ^ 2 =
      (1 / (nObs T rec ℓ j t : ℝ)) ^ 2 * ∑ s ∈ levelSet rec ℓ (t - 1),
        (if grid (numGrid T) (rec s).2 ≤ grid (numGrid T) j then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s _
    unfold wt; split_ifs <;> ring
  rw [this, ← nObs_eq_sum T rec ℓ j t ht]
  field_simp

end gf

/-! ### Bernstein bound for a fixed reference run -/

theorem exp_neg_four_log (x : ℝ) (hx : 0 < x) : Real.exp (-(4 * Real.log x)) = 1 / x ^ 4 := by
  rw [Real.exp_neg, show (4 : ℝ) * Real.log x = ((4 : ℕ) : ℝ) * Real.log x by norm_num,
    Real.exp_nat_mul, Real.exp_log hx]
  simp

theorem bern_algebra (a V c γ : ℝ) (ha : 0 < a) (hV : 0 ≤ V) (hc : 0 < c) (hγ : 3 ≤ γ) :
    4 * a ≤ (γ * (Real.sqrt (a * V) + a * c)) ^ 2 /
      (2 * ((V + c * (γ * (Real.sqrt (a * V) + a * c)) / 24) +
        c * (γ * (Real.sqrt (a * V) + a * c)) / 3)) := by
  set r := Real.sqrt (a * V) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = a * V := Real.sq_sqrt (by positivity)
  have hthr : 0 < γ * (r + a * c) := by positivity
  rw [le_div_iff₀ (by positivity)]
  have hV' : V = r ^ 2 / a := by rw [hr2]; field_simp
  rw [hV']
  have h1 : 0 ≤ a * c * r := by positivity
  have h2 : 0 ≤ a * c := by positivity
  have key : 8 * r ^ 2 + 3 * (a * c) * (γ * (r + a * c)) ≤ (γ * (r + a * c)) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg h2 hr0) (by linarith : (0:ℝ) ≤ γ - 3),
      mul_nonneg (mul_nonneg h2 h2) (by nlinarith : (0:ℝ) ≤ γ * γ - 3 * γ),
      mul_nonneg (sq_nonneg r) (by nlinarith : (0:ℝ) ≤ γ * γ - 8),
      mul_nonneg (mul_nonneg h2 hr0) (by nlinarith : (0:ℝ) ≤ 2 * γ * γ - 3 * γ)]
  have e : 4 * a * (2 * (r ^ 2 / a + c * (γ * (r + a * c)) / 24 + c * (γ * (r + a * c)) / 3)) =
      8 * r ^ 2 + 3 * (a * c) * (γ * (r + a * c)) := by
    field_simp; ring
  rw [e]; exact key

theorem D_bound (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (μG : Measure ℝ) [IsProbabilityMeasure μG]
    (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0) (rec : ℕ → ℕ × ℕ) (ℓ i t : ℕ) (hK : 1 ≤ numGrid T)
    (hi : i < numGrid T) (hn : ∀ j, 0 < nObs T rec ℓ j t) (ht : 1 ≤ t) (htT : t ≤ T)
    (ha : 0 < logFactor T)
    (hLKT : 0 < (numLevels T : ℝ) * (numGrid T : ℝ) * (T : ℝ)) :
    (Measure.pi fun _ : Fin T => μG)
      {m | γ * (Real.sqrt (logFactor T * ∑ j ∈ Finset.Ico i (numGrid T),
              intervalProb T μG j / (nObs T rec ℓ j t : ℝ))
            + logFactor T / (nObs T rec ℓ i t : ℝ))
          ≤ |∑ k : Fin T, Gf T μG rec ℓ i t k (m k)|}
      ≤ ENNReal.ofReal (2 / ((numLevels T : ℝ) * (numGrid T : ℝ) * (T : ℝ)) ^ 4) := by
  set a := logFactor T
  set V := ∑ j ∈ Finset.Ico i (numGrid T), intervalProb T μG j / (nObs T rec ℓ j t : ℝ)
  set c := 1 / (nObs T rec ℓ i t : ℝ) with hcdef
  have hni : (0 : ℝ) < nObs T rec ℓ i t := by exact_mod_cast hn i
  have hc : 0 < c := by positivity
  have hV : 0 ≤ V := Finset.sum_nonneg (fun j _ => div_nonneg (intervalProb_nonneg _ _ _)
    (Nat.cast_nonneg _))
  set thr := γ * (Real.sqrt (a * V) + a * c) with hthr
  have hthr' : γ * (Real.sqrt (a * V) + a / (nObs T rec ℓ i t : ℝ)) = thr := by
    rw [hthr, hcdef]; ring
  have hthr0 : 0 < thr := by
    have : 0 < Real.sqrt (a * V) + a * c := by positivity
    rw [hthr]; nlinarith
  set W := V + c * thr / 24 with hWdef
  have hW : 0 < W := by positivity
  have hvar : ∑ k, ∫ x, Gf T μG rec ℓ i t k x ^ 2 ∂μG ≤ W := by
    calc ∑ k, ∫ x, Gf T μG rec ℓ i t k x ^ 2 ∂μG
        ≤ ∑ k : Fin T, (if k.val + 1 ∈ levelSet rec ℓ (t - 1) then
          ∑ j ∈ Finset.Ico i (numGrid T), wt T rec ℓ t (k.val + 1) j ^ 2 * intervalProb T μG j
          else 0) := Finset.sum_le_sum (fun k _ => Gf_var T μG rec ℓ i t hK k)
      _ = V := var_sum T μG rec ℓ i t hn ht htT
      _ ≤ W := by
          have : 0 ≤ c * thr / 24 := by positivity
          rw [hWdef]; linarith
  have hexp : Real.exp (-(thr ^ 2 / (2 * (W + c * thr / 3)))) ≤
      1 / ((numLevels T : ℝ) * (numGrid T : ℝ) * (T : ℝ)) ^ 4 := by
    rw [← exp_neg_four_log _ hLKT]
    apply Real.exp_le_exp.mpr
    have := bern_algebra a V c γ ha hV hc hγ
    have hlog : a = Real.log ((numLevels T : ℝ) * (numGrid T : ℝ) * (T : ℝ)) := rfl
    rw [← hlog]
    linarith
  have hup := bernstein_pi μG (Gf T μG rec ℓ i t) (fun k => Gf_meas T μG rec ℓ i t k) c hc
    (fun k x => Gf_bound T μG hG rec ℓ i t hK hi hn k x) (fun k => Gf_mean T μG rec ℓ i t k)
    W hW hvar thr hthr0.le
  have hlo := bernstein_pi μG (fun k x => -Gf T μG rec ℓ i t k x)
    (fun k => (Gf_meas T μG rec ℓ i t k).neg) c hc
    (fun k x => by rw [abs_neg]; exact Gf_bound T μG hG rec ℓ i t hK hi hn k x)
    (fun k => by rw [integral_neg, Gf_mean T μG rec ℓ i t k, neg_zero])
    W hW (by simpa only [neg_sq] using hvar) thr hthr0.le
  rw [hthr']
  have hsub : {m : Fin T → ℝ | thr ≤ |∑ k : Fin T, Gf T μG rec ℓ i t k (m k)|} ⊆
      {m | thr ≤ ∑ k, Gf T μG rec ℓ i t k (m k)} ∪
      {m | thr ≤ ∑ k, (fun k x => -Gf T μG rec ℓ i t k x) k (m k)} := by
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    simp only [Set.mem_union, Set.mem_setOf_eq, Finset.sum_neg_distrib]
    rcases le_abs'.mp hm with h | h
    · right; linarith
    · left; exact h
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
  refine le_trans (add_le_add hup hlo) ?_
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  have : (2 : ℝ) / ((numLevels T : ℝ) * (numGrid T : ℝ) * (T : ℝ)) ^ 4 =
      1 / ((numLevels T : ℝ) * (numGrid T : ℝ) * (T : ℝ)) ^ 4 +
      1 / ((numLevels T : ℝ) * (numGrid T : ℝ) * (T : ℝ)) ^ 4 := by ring
  rw [this]
  linarith

/-! ### Assembly: conditioning on the truncated record -/

theorem target (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (v : Fin T → ℝ) (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (i : ℕ) (hi : i < numGrid T) (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 (numLevels T))
    (t : ℕ) (ht₀ : initLength T < t) (htT : t ≤ T) :
    (Measure.pi fun _ : Fin T => μG)
        {m | γ * (Real.sqrt (logFactor T * ∑ j ∈ Finset.Ico i (numGrid T),
                intervalProb T μG j / (runN T γ sel v m ℓ j t : ℝ))
              + logFactor T / (runN T γ sel v m ℓ i t : ℝ))
            ≤ |runRhat T γ sel v m ℓ i t - gridReward μG v i t|}
      ≤ ENNReal.ofReal (2 / ((numLevels T : ℝ) * (numGrid T : ℝ) * (T : ℝ)) ^ 4) := by
  classical
  set μ := Measure.pi fun _ : Fin T => μG with hμ
  have hT2 : 2 ≤ T := two_le_of_init T t ht₀ htT
  have hK2 := numGrid_two_le T hT2
  have hK : 1 ≤ numGrid T := by omega
  have hL := numLevels_pos T hT2
  obtain ⟨hℓ1, hℓL⟩ := Finset.mem_Icc.mp hℓ
  have ht1 : 1 ≤ t := by omega
  have ha : 0 < logFactor T := by linarith [one_le_logFactor T hT2]
  have hLKT : 0 < (numLevels T : ℝ) * (numGrid T : ℝ) * (T : ℝ) := by
    have : (0 : ℝ) < numLevels T := by exact_mod_cast (by omega : 0 < numLevels T)
    have : (0 : ℝ) < numGrid T := by exact_mod_cast (by omega : 0 < numGrid T)
    have : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
    positivity
  set B := ENNReal.ofReal (2 / ((numLevels T : ℝ) * (numGrid T : ℝ) * (T : ℝ)) ^ 4) with hB
  set R : (Fin T → ℝ) → ℕ → ℕ × ℕ := fun m => runRecord T γ sel v m with hR
  have hn : ∀ m j, 0 < nObs T (R m) ℓ j t := by
    intro m j
    exact nObs_pos T γ sel _ _ t ht₀ htT ℓ j hℓL
  -- the events of the truncated record
  set E : (Fin t → Option (ℕ × ℕ)) → Set (Fin T → ℝ) :=
    fun f => {m | ∀ u : Fin t, trunc ℓ (R m u.val) = f u} with hE
  set thr : (Fin T → ℝ) → ℝ := fun m0 => γ * (Real.sqrt (logFactor T *
      ∑ j ∈ Finset.Ico i (numGrid T), intervalProb T μG j / (nObs T (R m0) ℓ j t : ℝ))
      + logFactor T / (nObs T (R m0) ℓ i t : ℝ)) with hthr
  set D : (Fin T → ℝ) → Set (Fin T → ℝ) :=
    fun m0 => {m | thr m0 ≤ |∑ k : Fin T, Gf T μG (R m0) ℓ i t k (m k)|} with hD
  set DS : (Fin t → Option (ℕ × ℕ)) → Set (Fin T → ℝ) :=
    fun f => if h : (E f).Nonempty then D h.some else ∅ with hDS
  -- agreement inside one event
  have hagree : ∀ f m m0, m ∈ E f → m0 ∈ E f →
      ∀ u, u < t → trunc ℓ (R m u) = trunc ℓ (R m0 u) := by
    intro f m m0 hm hm0 u hu
    have h1 := hm ⟨u, hu⟩
    have h2 := hm0 ⟨u, hu⟩
    simp only at h1 h2
    rw [h1, h2]
  -- inclusion of the deviation event
  have hsub : {m : Fin T → ℝ | γ * (Real.sqrt (logFactor T * ∑ j ∈ Finset.Ico i (numGrid T),
                intervalProb T μG j / (runN T γ sel v m ℓ j t : ℝ))
              + logFactor T / (runN T γ sel v m ℓ i t : ℝ))
            ≤ |runRhat T γ sel v m ℓ i t - gridReward μG v i t|} ⊆ ⋃ f, (E f ∩ DS f) := by
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    set f : Fin t → Option (ℕ × ℕ) := fun u => trunc ℓ (R m u.val)
    have hmE : m ∈ E f := fun u => rfl
    have hne : (E f).Nonempty := ⟨m, hmE⟩
    refine Set.mem_iUnion.mpr ⟨f, hmE, ?_⟩
    simp only [hDS, dif_pos hne]
    set m0 := hne.some
    have hm0 : m0 ∈ E f := hne.some_mem
    have hag := hagree f m m0 hmE hm0
    have hN : ∀ j, runN T γ sel v m ℓ j t = nObs T (R m0) ℓ j t := fun j =>
      nObs_T T ℓ (R m) (R m0) t hag ht1 ℓ le_rfl j
    simp only [hN] at hm
    rw [rhat_sub T γ sel v m μG hG hK ℓ i t hi.le,
      err_eq T γ sel v μG ℓ i t ht1 htT m m0 hag (hn m0), abs_mul, abs_neg] at hm
    have hv1 : |paperSeq v t - grid (numGrid T) i| ≤ 1 := by
      have h1 := paperSeq_mem v hv t
      have h2 := grid_mem (numGrid T) i hi.le
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    show thr m0 ≤ _
    have habs := abs_nonneg (∑ k : Fin T, Gf T μG (R m0) ℓ i t k (m k))
    calc thr m0 ≤ _ := hm
      _ ≤ 1 * |∑ k : Fin T, Gf T μG (R m0) ℓ i t k (m k)| :=
          mul_le_mul_of_nonneg_right hv1 habs
      _ = _ := one_mul _
  -- measurability
  have hEmeas : ∀ f, MeasurableSet (E f) := by
    intro f
    have : E f = ⋂ u : Fin t, (fun m => R m u.val) ⁻¹' {r | trunc ℓ r = f u} := by
      ext m; simp [hE]
    rw [this]
    exact MeasurableSet.iInter (fun u => meas_runRecord T γ sel v u.val
      (Set.to_countable _).measurableSet)
  have hDmeas : ∀ m0, MeasurableSet (D m0) := by
    intro m0
    apply measurableSet_le measurable_const
    apply continuous_abs.measurable.comp
    exact Finset.measurable_sum _ (fun k _ =>
      (Gf_meas T μG (R m0) ℓ i t k).comp (measurable_pi_apply k))
  -- each piece
  have hpiece : ∀ f, μ (E f ∩ DS f) ≤ μ (E f) * B := by
    intro f
    by_cases hne : (E f).Nonempty
    · simp only [hDS, dif_pos hne]
      set m0 := hne.some
      have hm0 : m0 ∈ E f := hne.some_mem
      set S : Finset (Fin T) := Finset.univ.filter
        (fun k : Fin T => k.val + 1 < t ∧ (R m0 (k.val + 1)).1 < ℓ) with hS
      -- the event `E f` only depends on the coordinates in `S`
      have hEdep1 : ∀ m m' : Fin T → ℝ, (∀ k ∈ S, m k = m' k) → m ∈ E f → m' ∈ E f := by
        intro m m' hmm' hm
        have hag := hagree f m m0 hm hm0
        have hloc := run_trunc_local T γ sel v ℓ hℓ1 m m' t (by omega) (by
          intro u hu1 hut hlev
          have hr := trunc_eq_of_le (hag u hut) (by
            have : (R m u).1 = (runRecord T γ sel v m u).1 := rfl
            omega)
          apply hmm'
          simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
          have : u - 1 + 1 = u := by omega
          rw [this]
          refine ⟨hut, ?_⟩
          rw [← hr]; exact hlev)
        intro u
        rw [← hloc u.val u.isLt]
        exact hm u
      have hEdep : ∀ m m' : Fin T → ℝ, (∀ k ∈ S, m k = m' k) → (m ∈ E f ↔ m' ∈ E f) := by
        intro m m' h
        exact ⟨hEdep1 m m' h, hEdep1 m' m (fun k hk => (h k hk).symm)⟩
      have hDdep : ∀ m m' : Fin T → ℝ, (∀ k ∈ Sᶜ, m k = m' k) → (m ∈ D m0 ↔ m' ∈ D m0) := by
        intro m m' h
        have : ∑ k : Fin T, Gf T μG (R m0) ℓ i t k (m k) =
            ∑ k : Fin T, Gf T μG (R m0) ℓ i t k (m' k) := by
          apply Finset.sum_congr rfl
          intro k _
          unfold Gf
          split_ifs with hk
          · have hkS : k ∈ Sᶜ := by
              simp only [hS, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
                not_and, not_lt]
              intro _
              unfold levelSet at hk
              simp only [Finset.mem_filter] at hk
              omega
            rw [h k hkS]
          · rfl
        simp only [hD, Set.mem_setOf_eq, this]
      rw [indep_pi μG S (E f) (D m0) (hEmeas f) (hDmeas m0) hEdep hDdep]
      gcongr
      exact D_bound T γ hγ μG hG (R m0) ℓ i t hK hi (hn m0) ht1 htT ha hLKT
    · have : E f = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      rw [this, Set.empty_inter, measure_empty]
      exact bot_le
  -- summation
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro f f' hff'
    rw [Function.onFun, Set.disjoint_left]
    intro m hm hm'
    apply hff'
    funext u
    rw [← hm u, ← hm' u]
  calc μ _ ≤ μ (⋃ f, (E f ∩ DS f)) := measure_mono hsub
    _ ≤ ∑' f, μ (E f ∩ DS f) := measure_iUnion_le _
    _ ≤ ∑' f, μ (E f) * B := ENNReal.tsum_le_tsum hpiece
    _ = (∑' f, μ (E f)) * B := ENNReal.tsum_mul_right
    _ = μ (⋃ f, E f) * B := by rw [measure_iUnion hdisj hEmeas]
    _ ≤ 1 * B := by
        gcongr
        exact prob_le_one
    _ = B := one_mul B

end FPA2bTgt


open FirstPriceLearning.Adversarial in
theorem solution (T : ℕ) (γ : ℝ) (hγ : 3 ≤ γ) (sel : ℕ → ℕ → Finset ℕ → ℕ)
    (hsel : IsSelectionRule sel) (v : Fin T → ℝ) (hv : ∀ t, v t ∈ Set.Icc (0 : ℝ) 1)
    (μG : Measure ℝ) [IsProbabilityMeasure μG] (hG : μG (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (i : ℕ) (hi : i < numGrid T) (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 (numLevels T))
    (t : ℕ) (ht₀ : initLength T < t) (htT : t ≤ T) :
    (Measure.pi fun _ : Fin T => μG)
        {m | γ * (Real.sqrt (logFactor T * ∑ j ∈ Finset.Ico i (numGrid T),
                intervalProb T μG j / (runN T γ sel v m ℓ j t : ℝ))
              + logFactor T / (runN T γ sel v m ℓ i t : ℝ))
            ≤ |runRhat T γ sel v m ℓ i t - gridReward μG v i t|}
      ≤ ENNReal.ofReal (2 / ((numLevels T : ℝ) * (numGrid T : ℝ) * (T : ℝ)) ^ 4) :=
  FPA2bTgt.target T γ hγ sel v hv μG hG i hi ℓ hℓ t ht₀ htT
