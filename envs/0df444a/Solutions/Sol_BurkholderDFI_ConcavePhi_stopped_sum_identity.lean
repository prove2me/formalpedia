-- Prove2me | solution 1 for BurkholderDFI.ConcavePhi.stopped_sum_identity
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:21:35.766738+00:00
-- url     : https://prove2.me/submissions/11e1804c-4da2-4fde-847a-1a2acfed3776

import Mathlib
import Definitions.Def_BurkholderDFI_ConcavePhi_Partial

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace BurkholderDFI.ConcavePhi

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

lemma Zpart_top (z : ℕ → Ω → ℝ≥0∞) (ω : Ω) : Zpart z ⊤ ω = ∑' k, z (k + 1) ω := by
  unfold Zpart; simp

lemma Wpart_top (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (ω : Ω) :
    Wpart ℱ P z ⊤ ω = ∑' k, condLExp (ℱ k) P (z (k + 1)) ω := by
  unfold Wpart; simp

lemma Wpart_nat (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) :
    Wpart ℱ P z n ω = ∑ k ∈ Finset.range n, condLExp (ℱ k) P (z (k + 1)) ω := by
  unfold Wpart
  rw [tsum_eq_sum (s := Finset.range n)]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [if_pos]
    exact_mod_cast hk
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [if_neg]
    intro h
    have : k + 1 ≤ n := by exact_mod_cast h
    omega

lemma Zpart_mono (z : ℕ → Ω → ℝ≥0∞) {m n : ℕ∞} (h : m ≤ n) (ω : Ω) :
    Zpart z m ω ≤ Zpart z n ω := by
  unfold Zpart
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : ((k + 1 : ℕ) : ℕ∞) ≤ m
  · rw [if_pos hk, if_pos (hk.trans h)]
  · rw [if_neg hk]; exact zero_le

lemma Wpart_mono (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) {m n : ℕ∞} (h : m ≤ n) (ω : Ω) :
    Wpart ℱ P z m ω ≤ Wpart ℱ P z n ω := by
  unfold Wpart
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : ((k + 1 : ℕ) : ℕ∞) ≤ m
  · rw [if_pos hk, if_pos (hk.trans h)]
  · rw [if_neg hk]; exact zero_le

lemma measurable_Wpart_succ (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (n : ℕ) :
    Measurable[ℱ n] (Wpart ℱ P z ((n + 1 : ℕ) : ℕ∞)) := by
  unfold Wpart
  apply Measurable.ennreal_tsum
  intro k
  by_cases hk : ((k + 1 : ℕ) : ℕ∞) ≤ ((n + 1 : ℕ) : ℕ∞)
  · simp only [hk, if_true]
    have hkn : k ≤ n := by
      have : k + 1 ≤ n + 1 := by exact_mod_cast hk
      omega
    exact (measurable_condLExp (ℱ k) P _).mono (ℱ.mono hkn) le_rfl
  · simp only [hk, if_false]
    exact measurable_const

lemma measurable_Wpart_top (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) :
    Measurable (Wpart ℱ P z ⊤) := by
  unfold Wpart
  apply Measurable.ennreal_tsum
  intro k
  simp only [le_top, if_true]
  exact measurable_condLExp' (ℱ k) P _

/-- `k ≤ τ ω` iff `W_{n+1} ω ≤ l` for all `n < k`. -/
lemma le_stopIdx_iff (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (l : ℝ≥0) (ω : Ω) (k : ℕ∞) :
    k ≤ stopIdx ℱ P z l ω ↔ ∀ n : ℕ, (l : ℝ≥0∞) < Wpart ℱ P z ((n + 1 : ℕ) : ℕ∞) ω → k ≤ n := by
  unfold stopIdx
  simp only [le_iInf_iff]

lemma stopIdx_lt_top_iff (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (l : ℝ≥0) (ω : Ω) :
    stopIdx ℱ P z l ω < ⊤ ↔ ∃ n : ℕ, (l : ℝ≥0∞) < Wpart ℱ P z ((n + 1 : ℕ) : ℕ∞) ω := by
  rw [lt_top_iff_ne_top]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    apply h
    apply top_le_iff.mp
    rw [le_stopIdx_iff]
    intro n hn
    exact absurd hn (not_lt.mpr (hc n))
  · rintro ⟨n, hn⟩ h
    have := (le_stopIdx_iff ℱ z l ω ⊤).mp (le_of_eq h.symm) n hn
    exact absurd this (by simp)

lemma lt_Wpart_top_iff (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (l : ℝ≥0) (ω : Ω) :
    (l : ℝ≥0∞) < Wpart ℱ P z ⊤ ω ↔
      ∃ n : ℕ, (l : ℝ≥0∞) < Wpart ℱ P z ((n + 1 : ℕ) : ℕ∞) ω := by
  constructor
  · intro h
    rw [Wpart_top, ENNReal.tsum_eq_iSup_nat, lt_iSup_iff] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨n, ?_⟩
    rw [← Wpart_nat] at hn
    exact hn.trans_le (Wpart_mono ℱ z (by exact_mod_cast Nat.le_succ n) ω)
  · rintro ⟨n, hn⟩
    exact hn.trans_le (Wpart_mono ℱ z le_top ω)

lemma measurableSet_le_stopIdx (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (l : ℝ≥0) (k : ℕ) :
    MeasurableSet[ℱ k] {ω | ((k + 1 : ℕ) : ℕ∞) ≤ stopIdx ℱ P z l ω} := by
  have : {ω | ((k + 1 : ℕ) : ℕ∞) ≤ stopIdx ℱ P z l ω}
      = ⋂ n : ℕ, {ω | (l : ℝ≥0∞) < Wpart ℱ P z ((n + 1 : ℕ) : ℕ∞) ω → ((k + 1 : ℕ) : ℕ∞) ≤ n} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, le_stopIdx_iff]
  rw [this]
  apply MeasurableSet.iInter
  intro n
  by_cases hn : ((k + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞)
  · simp only [hn, implies_true, Set.setOf_true]
    exact MeasurableSet.univ
  · simp only [hn, imp_false, not_lt]
    have hnk : n ≤ k := by
      have : ¬ (k + 1 ≤ n) := fun h => hn (by exact_mod_cast h)
      omega
    exact ((measurable_Wpart_succ ℱ z n).mono (ℱ.mono hnk) le_rfl) measurableSet_Iic

lemma Zpart_stop_eq (z : ℕ → Ω → ℝ≥0∞) (τ : Ω → ℕ∞) (ω : Ω) :
    Zpart z (τ ω) ω = ∑' k, ({ω | ((k + 1 : ℕ) : ℕ∞) ≤ τ ω}).indicator (z (k + 1)) ω := by
  unfold Zpart
  congr 1
  ext k
  simp [Set.indicator_apply]

lemma Wpart_stop_eq (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (τ : Ω → ℕ∞) (ω : Ω) :
    Wpart ℱ P z (τ ω) ω
      = ∑' k, ({ω | ((k + 1 : ℕ) : ℕ∞) ≤ τ ω}).indicator (condLExp (ℱ k) P (z (k + 1))) ω := by
  unfold Wpart
  congr 1
  ext k
  simp [Set.indicator_apply]

/-- The key identity `E Z_τ = E W_τ`. -/
lemma lintegral_Zpart_stop [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (z : ℕ → Ω → ℝ≥0∞) (hz : ∀ k, Measurable (z k)) (l : ℝ≥0) :
    ∫⁻ ω, Zpart z (stopIdx ℱ P z l ω) ω ∂P = ∫⁻ ω, Wpart ℱ P z (stopIdx ℱ P z l ω) ω ∂P := by
  simp_rw [Zpart_stop_eq, Wpart_stop_eq]
  have hs : ∀ k : ℕ, MeasurableSet {ω | ((k + 1 : ℕ) : ℕ∞) ≤ stopIdx ℱ P z l ω} :=
    fun k => ℱ.le k _ (measurableSet_le_stopIdx ℱ z l k)
  rw [lintegral_tsum (fun k => ((hz (k + 1)).indicator (hs k)).aemeasurable),
    lintegral_tsum (fun k => ((measurable_condLExp' (ℱ k) P _).indicator (hs k)).aemeasurable)]
  congr 1
  ext k
  rw [lintegral_indicator (hs k), lintegral_indicator (hs k),
    setLIntegral_condLExp (ℱ.le k) P (z (k + 1)) (measurableSet_le_stopIdx ℱ z l k)]

lemma Wpart_stop_le (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (l : ℝ≥0) (ω : Ω) :
    Wpart ℱ P z (stopIdx ℱ P z l ω) ω ≤ min (Wpart ℱ P z ⊤ ω) (l : ℝ≥0∞) := by
  refine le_min (Wpart_mono ℱ z le_top ω) ?_
  have hle := (le_stopIdx_iff ℱ z l ω (stopIdx ℱ P z l ω)).mp le_rfl
  generalize hτ : stopIdx ℱ P z l ω = τ at hle
  induction τ using ENat.recTopCoe with
  | top =>
    rw [Wpart_top]
    apply ENNReal.tsum_le_of_sum_range_le
    intro n
    rw [← Wpart_nat]
    have := hle n
    by_contra hc
    push_neg at hc
    have h2 : (l : ℝ≥0∞) < Wpart ℱ P z ((n + 1 : ℕ) : ℕ∞) ω :=
      hc.trans_le (Wpart_mono ℱ z (by exact_mod_cast Nat.le_succ n) ω)
    exact absurd (this h2) (by simp)
  | coe n =>
    cases n with
    | zero =>
      have h0 : Wpart ℱ P z ((0 : ℕ) : ℕ∞) ω = 0 := by rw [Wpart_nat]; simp
      rw [h0]; exact zero_le
    | succ m =>
      by_contra hc
      push_neg at hc
      have := hle m hc
      have : m + 1 ≤ m := by exact_mod_cast this
      omega

theorem stopped_sum_identity_core {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (z : ℕ → Ω → ℝ≥0∞) (hz : ∀ k, Measurable (z k)) (l : ℝ≥0) (hl : 0 < l) :
    (∀ ω, min (Zpart z ⊤ ω) (l : ℝ≥0∞) ≤ Zpart z (stopIdx ℱ P z l ω) ω
        + Set.indicator {ω | stopIdx ℱ P z l ω < ⊤} (fun _ => (l : ℝ≥0∞)) ω) ∧
    (∫⁻ ω, Zpart z (stopIdx ℱ P z l ω) ω ∂P = ∫⁻ ω, Wpart ℱ P z (stopIdx ℱ P z l ω) ω ∂P) ∧
    (∫⁻ ω, Wpart ℱ P z (stopIdx ℱ P z l ω) ω ∂P ≤ ∫⁻ ω, min (Wpart ℱ P z ⊤ ω) (l : ℝ≥0∞) ∂P) ∧
    (∫⁻ ω, Set.indicator {ω | stopIdx ℱ P z l ω < ⊤} (fun _ => (l : ℝ≥0∞)) ω ∂P
        = (l : ℝ≥0∞) * P {ω | (l : ℝ≥0∞) < Wpart ℱ P z ⊤ ω}) ∧
    ((l : ℝ≥0∞) * P {ω | (l : ℝ≥0∞) < Wpart ℱ P z ⊤ ω}
        ≤ ∫⁻ ω, min (Wpart ℱ P z ⊤ ω) (l : ℝ≥0∞) ∂P) := by
  have hset : {ω | stopIdx ℱ P z l ω < ⊤} = {ω | (l : ℝ≥0∞) < Wpart ℱ P z ⊤ ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, stopIdx_lt_top_iff, lt_Wpart_top_iff]
  have hmeas : MeasurableSet {ω | (l : ℝ≥0∞) < Wpart ℱ P z ⊤ ω} :=
    measurableSet_lt measurable_const (measurable_Wpart_top ℱ z)
  refine ⟨?_, lintegral_Zpart_stop ℱ z hz l, ?_, ?_, ?_⟩
  · intro ω
    by_cases h : stopIdx ℱ P z l ω < ⊤
    · rw [Set.indicator_of_mem (show ω ∈ {ω | stopIdx ℱ P z l ω < ⊤} from h)]
      exact (min_le_right _ _).trans le_add_self
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | stopIdx ℱ P z l ω < ⊤} from h), add_zero]
      have : stopIdx ℱ P z l ω = ⊤ := by
        rw [lt_top_iff_ne_top] at h; push_neg at h; exact h
      rw [this]
      exact min_le_left _ _
  · exact lintegral_mono (fun ω => Wpart_stop_le ℱ z l ω)
  · rw [hset, lintegral_indicator_const hmeas]
  · rw [← lintegral_indicator_const hmeas]
    apply lintegral_mono
    intro ω
    by_cases h : (l : ℝ≥0∞) < Wpart ℱ P z ⊤ ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | (l : ℝ≥0∞) < Wpart ℱ P z ⊤ ω} from h)]
      exact le_min h.le le_rfl
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | (l : ℝ≥0∞) < Wpart ℱ P z ⊤ ω} from h)]
      exact zero_le

end BurkholderDFI.ConcavePhi

open BurkholderDFI.ConcavePhi


theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (z : ℕ → Ω → ℝ≥0∞) (hz : ∀ k, Measurable (z k)) (l : ℝ≥0) (hl : 0 < l) :
    (∀ ω, min (Zpart z ⊤ ω) (l : ℝ≥0∞) ≤ Zpart z (stopIdx ℱ P z l ω) ω
        + Set.indicator {ω | stopIdx ℱ P z l ω < ⊤} (fun _ => (l : ℝ≥0∞)) ω) ∧
    (∫⁻ ω, Zpart z (stopIdx ℱ P z l ω) ω ∂P = ∫⁻ ω, Wpart ℱ P z (stopIdx ℱ P z l ω) ω ∂P) ∧
    (∫⁻ ω, Wpart ℱ P z (stopIdx ℱ P z l ω) ω ∂P ≤ ∫⁻ ω, min (Wpart ℱ P z ⊤ ω) (l : ℝ≥0∞) ∂P) ∧
    (∫⁻ ω, Set.indicator {ω | stopIdx ℱ P z l ω < ⊤} (fun _ => (l : ℝ≥0∞)) ω ∂P
        = (l : ℝ≥0∞) * P {ω | (l : ℝ≥0∞) < Wpart ℱ P z ⊤ ω}) ∧
    ((l : ℝ≥0∞) * P {ω | (l : ℝ≥0∞) < Wpart ℱ P z ⊤ ω}
        ≤ ∫⁻ ω, min (Wpart ℱ P z ⊤ ω) (l : ℝ≥0∞) ∂P) := by
  exact stopped_sum_identity_core ℱ z hz l hl
