-- Prove2me | solution 1 for FirstPriceLearning.NonIID.oracle_bid
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:49:46.727866+00:00
-- url     : https://prove2.me/submissions/84ac06a0-b34d-42ad-bc4c-9f0333b67c6a

import Mathlib
import Definitions.Def_FirstPriceLearning_Stochastic_Auction
import Definitions.Def_FirstPriceLearning_NonIID_ThresholdModel
import Definitions.Def_FirstPriceLearning_NonIID_HardInstance

set_option autoImplicit false
open MeasureTheory FirstPriceLearning.NonIID

namespace FNI

noncomputable def ue {T : ℕ} (u : Fin T → ℝ) (n : ℕ) : ℝ := if h : n < T then u ⟨n, h⟩ else 0

lemma ue_abs {T : ℕ} (u : Fin T → ℝ) (hu : ∀ s, u s = 1 ∨ u s = -1) (n : ℕ) : |ue u n| ≤ 1 := by
  unfold ue
  split_ifs with h
  · rcases hu ⟨n, h⟩ with h | h <;> simp [h]
  · simp

lemma ue_lt {T : ℕ} (u : Fin T → ℝ) (t : Fin T) : ue u t.val = u t := by
  unfold ue
  simp [t.2]

lemma valueAux_eq {T : ℕ} (u : Fin T → ℝ) (n : ℕ) :
    valueAux u n = 1 / 2 + ∑ s ∈ Finset.range n, ue u s / 2 ^ (s + 3) := by
  induction n with
  | zero => simp [valueAux]
  | succ n ih =>
    rw [valueAux, ih, Finset.sum_range_succ]
    unfold ue
    ring

lemma valueSeq_eq {T : ℕ} (u : Fin T → ℝ) (t : Fin T) :
    valueSeq u t = 1 / 2 + ∑ s ∈ Finset.range t.val, ue u s / 2 ^ (s + 3) := by
  unfold valueSeq
  exact valueAux_eq u t.val

lemma fval_eq {T : ℕ} (u : Fin T → ℝ) :
    fval u = 1 / 2 + ∑ s ∈ Finset.range T, ue u s / 2 ^ (s + 3) := by
  unfold fval
  rw [← Fin.sum_univ_eq_sum_range (fun s => ue u s / 2 ^ (s + 3)) T, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [ue_lt]
  rw [pow_add 2 (t.val) 3, pow_add 2 (t.val) 1]
  field_simp
  ring

lemma tail_bound (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) (a N : ℕ) (h : a ≤ N) :
    |∑ s ∈ Finset.Ico a N, c s / 2 ^ (s + 3)| ≤ 1 / 2 ^ (a + 2) - 1 / 2 ^ (N + 2) := by
  induction N, h using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN]
    have h1 : |c N / 2 ^ (N + 3)| ≤ 1 / 2 ^ (N + 3) := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (N + 3))]
      exact div_le_div_of_nonneg_right (hc N) (by positivity)
    have h2 : (1 : ℝ) / 2 ^ (N + 2) = 2 * (1 / 2 ^ (N + 3)) := by
      rw [pow_succ 2 (N + 2)]
      field_simp
    have h3 : (1 : ℝ) / 2 ^ (N + 1 + 2) = 1 / 2 ^ (N + 3) := by
      rfl
    calc _ ≤ |∑ s ∈ Finset.Ico a N, c s / 2 ^ (s + 3)| + |c N / 2 ^ (N + 3)| := abs_add_le _ _
      _ ≤ _ := by rw [h3]; rw [h2] at ih; linarith

lemma tail_lt (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) (a N : ℕ) (h : a ≤ N) :
    |∑ s ∈ Finset.Ico a N, c s / 2 ^ (s + 3)| < 1 / 2 ^ (a + 2) := by
  have := tail_bound c hc a N h
  have : (0 : ℝ) < 1 / 2 ^ (N + 2) := by positivity
  linarith

lemma diff_decomp {T : ℕ} (u : Fin T → ℝ) (t : Fin T) :
    fval u - valueSeq u t = ue u t.val / 2 ^ (t.val + 3) +
      ∑ s ∈ Finset.Ico (t.val + 1) T, ue u s / 2 ^ (s + 3) := by
  rw [fval_eq, valueSeq_eq, ← Finset.sum_range_add_sum_Ico _ (le_of_lt t.2),
    Finset.sum_eq_sum_Ico_succ_bot t.2]
  ring

lemma diff_tail {T : ℕ} (u : Fin T → ℝ) (hu : ∀ s, u s = 1 ∨ u s = -1) (t : Fin T) :
    |∑ s ∈ Finset.Ico (t.val + 1) T, ue u s / 2 ^ (s + 3)| < 1 / 2 ^ (t.val + 3) := by
  have := tail_lt (ue u) (ue_abs u hu) (t.val + 1) T t.2
  simpa using this

lemma f_gt_v {T : ℕ} (u : Fin T → ℝ) (hu : ∀ s, u s = 1 ∨ u s = -1) (t : Fin T) (h : u t = 1) :
    valueSeq u t < fval u := by
  have h1 := diff_decomp u t
  have h2 := diff_tail u hu t
  rw [ue_lt, h] at h1
  have h3 := (abs_lt.mp h2).1
  have h4 : (0 : ℝ) < 1 / 2 ^ (t.val + 3) := by positivity
  linarith

lemma f_lt_v {T : ℕ} (u : Fin T → ℝ) (hu : ∀ s, u s = 1 ∨ u s = -1) (t : Fin T) (h : u t = -1) :
    fval u < valueSeq u t := by
  have h1 := diff_decomp u t
  have h2 := diff_tail u hu t
  rw [ue_lt, h, neg_div] at h1
  have h3 := (abs_lt.mp h2).2
  linarith

lemma valueSeq_mem {T : ℕ} (u : Fin T → ℝ) (hu : ∀ s, u s = 1 ∨ u s = -1) (t : Fin T) :
    valueSeq u t ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) := by
  rw [valueSeq_eq]
  have := tail_bound (ue u) (ue_abs u hu) 0 t.val (Nat.zero_le _)
  rw [← Finset.range_eq_Ico] at this
  have e : (1 : ℝ) / 2 ^ (0 + 2) = 1 / 4 := by norm_num
  rw [e] at this
  have h5 : (0 : ℝ) < 1 / 2 ^ (t.val + 2) := by positivity
  obtain ⟨h6, h7⟩ := abs_le.mp this
  constructor <;> linarith

lemma fval_mem {T : ℕ} (u : Fin T → ℝ) (hu : ∀ s, u s = 1 ∨ u s = -1) :
    fval u ∈ Set.Icc (0 : ℝ) 1 := by
  rw [fval_eq]
  have := tail_bound (ue u) (ue_abs u hu) 0 T (Nat.zero_le _)
  rw [← Finset.range_eq_Ico] at this
  have e : (1 : ℝ) / 2 ^ (0 + 2) = 1 / 4 := by norm_num
  rw [e] at this
  have h5 : (0 : ℝ) < 1 / 2 ^ (T + 2) := by positivity
  obtain ⟨h6, h7⟩ := abs_le.mp this
  constructor <;> linarith

lemma valueSeq_congr {T : ℕ} (u u' : Fin T → ℝ) (s : Fin T)
    (h : ∀ r : Fin T, r < s → u r = u' r) : valueSeq u s = valueSeq u' s := by
  rw [valueSeq_eq, valueSeq_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_range] at hr
  have hrT : r < T := lt_trans hr s.2
  have := h ⟨r, hrT⟩ (by exact hr)
  unfold ue
  simp [hrT, this]

lemma prefix_sum {T : ℕ} (u : Fin T → ℝ) (t : Fin T) :
    (1 / 2 + 1 / 4 * ∑ s ∈ Finset.univ.filter (fun s : Fin T => s < t),
            u s / 2 ^ (s.val + 1)) = valueSeq u t := by
  rw [valueSeq_eq, Finset.sum_filter]
  have e1 : ∑ s : Fin T, (if s < t then u s / 2 ^ (s.val + 1) else 0) =
      ∑ s ∈ Finset.range T, (if s < t.val then ue u s / 2 ^ (s + 1) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun s => if s < t.val then ue u s / 2 ^ (s + 1) else 0) T]
    apply Finset.sum_congr rfl
    intro s _
    rw [ue_lt]
    rfl
  rw [e1, ← Finset.sum_range_add_sum_Ico _ (le_of_lt t.2)]
  have e2 : ∑ s ∈ Finset.Ico t.val T, (if s < t.val then ue u s / 2 ^ (s + 1) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    rw [Finset.mem_Ico] at hs
    simp [not_lt.mpr hs.1]
  rw [e2, add_zero, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mem_range] at hs
  rw [if_pos hs, pow_add 2 s 3, pow_add 2 s 1]
  field_simp
  ring

end FNI

namespace FNI

open FirstPriceLearning.Stochastic

lemma cdf_dirac (a x : ℝ) : cdf (Measure.dirac a) x = if a ≤ x then 1 else 0 := by
  unfold cdf
  rw [Measure.dirac_apply' _ measurableSet_Iic]
  by_cases h : a ≤ x <;> simp [Set.indicator, h]

lemma expReward_dirac (a v b : ℝ) :
    expReward (Measure.dirac a) v b = if a ≤ b then v - b else 0 := by
  unfold expReward
  rw [cdf_dirac]
  split_ifs <;> simp

lemma oracle_dirac (a v : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (hv : a ≤ v) :
    oracle (Measure.dirac a) v = v - a := by
  unfold oracle
  apply le_antisymm
  · apply ciSup_le
    intro b
    rw [expReward_dirac]
    have := b.2.1
    split_ifs with h <;> linarith
  · have hbdd : BddAbove (Set.range fun b : Set.Icc (0 : ℝ) 1 => expReward (Measure.dirac a) v b) := by
      refine ⟨|v| + 1, ?_⟩
      rintro _ ⟨b, rfl⟩
      beta_reduce
      rw [expReward_dirac]
      have := b.2.1
      have := le_abs_self v
      have := abs_nonneg v
      split_ifs <;> linarith
    refine le_trans ?_ (le_ciSup hbdd ⟨a, ha⟩)
    rw [expReward_dirac, if_pos le_rfl]

lemma law_eq_dirac {T : ℕ} (u : Fin T → ℝ) (t : Fin T) :
    hobLaw (Measure.dirac 0) (Measure.dirac (1 / 8 : ℝ)) (fval u) (valueSeq u t) =
      Measure.dirac (1 / 8 * (if fval u ≤ valueSeq u t then 1 else 0) : ℝ) := by
  unfold hobLaw
  by_cases h : fval u ≤ valueSeq u t
  · rw [if_neg (not_lt.mpr h), if_pos h]; norm_num
  · rw [if_pos (not_le.mp h), if_neg h]; norm_num

lemma m_mem {T : ℕ} (u : Fin T → ℝ) (t : Fin T) :
    (1 / 8 * (if fval u ≤ valueSeq u t then 1 else 0) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  split_ifs <;> constructor <;> norm_num

end FNI

theorem solution (T : ℕ) (u : Fin T → ℝ) (hu : ∀ s, u s = 1 ∨ u s = -1) (t : Fin T) :
    valueSeq u t ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) ∧
      FirstPriceLearning.Stochastic.oracle (hobLaw (Measure.dirac 0) (Measure.dirac (1 / 8)) (fval u) (valueSeq u t))
          (valueSeq u t) =
        valueSeq u t - 1 / 8 * (if fval u ≤ valueSeq u t then 1 else 0) ∧
      FirstPriceLearning.Stochastic.expReward (hobLaw (Measure.dirac 0) (Measure.dirac (1 / 8)) (fval u) (valueSeq u t))
          (valueSeq u t) (1 / 8 * (if fval u ≤ valueSeq u t then 1 else 0)) =
        FirstPriceLearning.Stochastic.oracle (hobLaw (Measure.dirac 0) (Measure.dirac (1 / 8)) (fval u) (valueSeq u t))
          (valueSeq u t) := by
  have hmem := FNI.valueSeq_mem u hu t
  have h1 := FNI.law_eq_dirac u t
  have h2 : FirstPriceLearning.Stochastic.oracle (Measure.dirac (1 / 8 * (if fval u ≤ valueSeq u t then 1 else 0) : ℝ)) (valueSeq u t) =
      valueSeq u t - 1 / 8 * (if fval u ≤ valueSeq u t then 1 else 0) := by
    apply FNI.oracle_dirac _ _ (FNI.m_mem u t)
    split_ifs <;> linarith [hmem.1]
  refine ⟨hmem, ?_, ?_⟩
  · rw [h1, h2]
  · rw [h1, h2, FNI.expReward_dirac, if_pos le_rfl]
