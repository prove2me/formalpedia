-- Prove2me | solution 1 for BurkholderDFI.ConvexPhi.neveu_pair_ineq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:57:50.000149+00:00
-- url     : https://prove2.me/submissions/56579c1e-216a-409e-b8f6-16dfac6d1e2f

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BurkholderDFI.ConvexPhi

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- `W_n = Σ_{k<n} E(z_{k+1}|𝒜_k)`, `n ∈ ℕ∞`. -/
noncomputable def nW (ℱ : Filtration ℕ mΩ) (P : Measure Ω)
    (z : ℕ → Ω → ℝ≥0∞) (n : ℕ∞) (ω : Ω) : ℝ≥0∞ :=
  ∑' k : ℕ, if (((k + 1 : ℕ) : ℕ∞) ≤ n) then condLExp (ℱ k) P (z (k + 1)) ω else 0

/-- `τ = inf {n : W_{n+1} > l}`. -/
noncomputable def nStop (ℱ : Filtration ℕ mΩ) (P : Measure Ω)
    (z : ℕ → Ω → ℝ≥0∞) (l : ℝ≥0) (ω : Ω) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : (l : ℝ≥0∞) < nW ℱ P z ((n + 1 : ℕ) : ℕ∞) ω), (n : ℕ∞)

lemma nW_top (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (ω : Ω) :
    nW ℱ P z ⊤ ω = ∑' k, condLExp (ℱ k) P (z (k + 1)) ω := by
  unfold nW; simp

lemma nW_nat (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) :
    nW ℱ P z n ω = ∑ k ∈ Finset.range n, condLExp (ℱ k) P (z (k + 1)) ω := by
  unfold nW
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

lemma nW_mono (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) {m n : ℕ∞} (h : m ≤ n) (ω : Ω) :
    nW ℱ P z m ω ≤ nW ℱ P z n ω := by
  unfold nW
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : ((k + 1 : ℕ) : ℕ∞) ≤ m
  · rw [if_pos hk, if_pos (hk.trans h)]
  · rw [if_neg hk]; exact zero_le

lemma measurable_nW_succ (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (n : ℕ) :
    Measurable[ℱ n] (nW ℱ P z ((n + 1 : ℕ) : ℕ∞)) := by
  unfold nW
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

lemma measurable_nW_top (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) :
    Measurable (nW ℱ P z ⊤) := by
  unfold nW
  apply Measurable.ennreal_tsum
  intro k
  simp only [le_top, if_true]
  exact measurable_condLExp' (ℱ k) P _

lemma le_nStop_iff (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (l : ℝ≥0) (ω : Ω) (k : ℕ∞) :
    k ≤ nStop ℱ P z l ω ↔ ∀ n : ℕ, (l : ℝ≥0∞) < nW ℱ P z ((n + 1 : ℕ) : ℕ∞) ω → k ≤ n := by
  unfold nStop
  simp only [le_iInf_iff]

lemma nStop_lt_top_iff (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (l : ℝ≥0) (ω : Ω) :
    nStop ℱ P z l ω < ⊤ ↔ ∃ n : ℕ, (l : ℝ≥0∞) < nW ℱ P z ((n + 1 : ℕ) : ℕ∞) ω := by
  rw [lt_top_iff_ne_top]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    apply h
    apply top_le_iff.mp
    rw [le_nStop_iff]
    intro n hn
    exact absurd hn (not_lt.mpr (hc n))
  · rintro ⟨n, hn⟩ h
    have := (le_nStop_iff ℱ z l ω ⊤).mp (le_of_eq h.symm) n hn
    exact absurd this (by simp)

lemma lt_nW_top_iff (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (l : ℝ≥0) (ω : Ω) :
    (l : ℝ≥0∞) < nW ℱ P z ⊤ ω ↔
      ∃ n : ℕ, (l : ℝ≥0∞) < nW ℱ P z ((n + 1 : ℕ) : ℕ∞) ω := by
  constructor
  · intro h
    rw [nW_top, ENNReal.tsum_eq_iSup_nat, lt_iSup_iff] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨n, ?_⟩
    rw [← nW_nat] at hn
    exact hn.trans_le (nW_mono ℱ z (by exact_mod_cast Nat.le_succ n) ω)
  · rintro ⟨n, hn⟩
    exact hn.trans_le (nW_mono ℱ z le_top ω)

lemma measurableSet_le_nStop (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (l : ℝ≥0) (k : ℕ) :
    MeasurableSet[ℱ k] {ω | ((k + 1 : ℕ) : ℕ∞) ≤ nStop ℱ P z l ω} := by
  have : {ω | ((k + 1 : ℕ) : ℕ∞) ≤ nStop ℱ P z l ω}
      = ⋂ n : ℕ, {ω | (l : ℝ≥0∞) < nW ℱ P z ((n + 1 : ℕ) : ℕ∞) ω → ((k + 1 : ℕ) : ℕ∞) ≤ n} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, le_nStop_iff]
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
    exact ((measurable_nW_succ ℱ z n).mono (ℱ.mono hnk) le_rfl) measurableSet_Iic

lemma measurableSet_nStop_lt (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (l : ℝ≥0) (k : ℕ) :
    MeasurableSet[ℱ k] {ω | ¬ ((k + 1 : ℕ) : ℕ∞) ≤ nStop ℱ P z l ω} :=
  (measurableSet_le_nStop ℱ z l k).compl

/-- `W_τ ≤ l`. -/
lemma nW_stop_le (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (l : ℝ≥0) (ω : Ω) :
    nW ℱ P z (nStop ℱ P z l ω) ω ≤ (l : ℝ≥0∞) := by
  have hle := (le_nStop_iff ℱ z l ω (nStop ℱ P z l ω)).mp le_rfl
  generalize hτ : nStop ℱ P z l ω = τ at hle
  induction τ using ENat.recTopCoe with
  | top =>
    rw [nW_top]
    apply ENNReal.tsum_le_of_sum_range_le
    intro n
    rw [← nW_nat]
    have := hle n
    by_contra hc
    push_neg at hc
    have h2 : (l : ℝ≥0∞) < nW ℱ P z ((n + 1 : ℕ) : ℕ∞) ω :=
      hc.trans_le (nW_mono ℱ z (by exact_mod_cast Nat.le_succ n) ω)
    exact absurd (this h2) (by simp)
  | coe n =>
    cases n with
    | zero =>
      have h0 : nW ℱ P z ((0 : ℕ) : ℕ∞) ω = 0 := by rw [nW_nat]; simp
      rw [h0]; exact zero_le
    | succ m =>
      by_contra hc
      push_neg at hc
      have := hle m hc
      have : m + 1 ≤ m := by exact_mod_cast this
      omega

/-- The tail `W − W_τ` as a sum of indicators. -/
noncomputable def nR (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (z : ℕ → Ω → ℝ≥0∞) (l : ℝ≥0)
    (ω : Ω) : ℝ≥0∞ :=
  ∑' k, ({ω | ¬ ((k + 1 : ℕ) : ℕ∞) ≤ nStop ℱ P z l ω}).indicator (condLExp (ℱ k) P (z (k + 1))) ω

noncomputable def nR' (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (z : ℕ → Ω → ℝ≥0∞) (l : ℝ≥0)
    (ω : Ω) : ℝ≥0∞ :=
  ∑' k, ({ω | ¬ ((k + 1 : ℕ) : ℕ∞) ≤ nStop ℱ P z l ω}).indicator (z (k + 1)) ω

lemma nW_top_eq_stop_add (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (l : ℝ≥0) (ω : Ω) :
    nW ℱ P z ⊤ ω = nW ℱ P z (nStop ℱ P z l ω) ω + nR ℱ P z l ω := by
  rw [nW_top]
  unfold nW nR
  rw [← ENNReal.tsum_add]
  congr 1
  ext k
  by_cases h : ((k + 1 : ℕ) : ℕ∞) ≤ nStop ℱ P z l ω
  · rw [if_pos h, Set.indicator_of_notMem (by simpa using h), add_zero]
  · rw [if_neg h, Set.indicator_of_mem (by simpa using h), zero_add]

lemma nR_le_nR' [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (z : ℕ → Ω → ℝ≥0∞) (hz : ∀ k, Measurable (z k)) (l : ℝ≥0) :
    ∫⁻ ω, nR ℱ P z l ω ∂P = ∫⁻ ω, nR' ℱ P z l ω ∂P := by
  unfold nR nR'
  have hs : ∀ k : ℕ, MeasurableSet {ω | ¬ ((k + 1 : ℕ) : ℕ∞) ≤ nStop ℱ P z l ω} :=
    fun k => ℱ.le k _ (measurableSet_nStop_lt ℱ z l k)
  rw [lintegral_tsum (fun k => ((hz (k + 1)).indicator (hs k)).aemeasurable),
    lintegral_tsum (fun k => ((measurable_condLExp' (ℱ k) P _).indicator (hs k)).aemeasurable)]
  congr 1
  ext k
  rw [lintegral_indicator (hs k), lintegral_indicator (hs k),
    setLIntegral_condLExp (ℱ.le k) P (z (k + 1)) (measurableSet_nStop_lt ℱ z l k)]

lemma nR'_le (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (l : ℝ≥0) (ω : Ω) :
    nR' ℱ P z l ω ≤ ∑' k, z (k + 1) ω := by
  unfold nR'
  apply ENNReal.tsum_le_tsum
  intro k
  exact Set.indicator_le_self _ _ ω

lemma nR'_eq_zero (ℱ : Filtration ℕ mΩ) (z : ℕ → Ω → ℝ≥0∞) (l : ℝ≥0) (ω : Ω)
    (h : ¬ (l : ℝ≥0∞) < nW ℱ P z ⊤ ω) : nR' ℱ P z l ω = 0 := by
  have hτ : nStop ℱ P z l ω = ⊤ := by
    by_contra hc
    have : nStop ℱ P z l ω < ⊤ := lt_top_iff_ne_top.mpr hc
    rw [nStop_lt_top_iff, ← lt_nW_top_iff] at this
    exact h this
  unfold nR'
  simp [hτ]

theorem neveu_pair_ineq_core {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (z : ℕ → Ω → ℝ≥0∞) (hz : ∀ k, Measurable (z k)) :
    ∀ l : ℝ, 0 < l →
      (∫⁻ ω in {ω | ENNReal.ofReal l <
        ∑' k : ℕ, condLExp (ℱ k) P (z (k + 1)) ω},
        ((∑' k : ℕ, condLExp (ℱ k) P (z (k + 1)) ω) - ENNReal.ofReal l) ∂P)
      ≤ (∫⁻ ω in {ω | ENNReal.ofReal l <
        ∑' k : ℕ, condLExp (ℱ k) P (z (k + 1)) ω},
        (∑' k : ℕ, z (k + 1) ω) ∂P) := by
  intro l hl
  set l' : ℝ≥0 := l.toNNReal with hl'
  have hof : ENNReal.ofReal l = (l' : ℝ≥0∞) := rfl
  simp_rw [hof, ← nW_top (P := P) ℱ z]
  have hA : MeasurableSet {ω | (l' : ℝ≥0∞) < nW ℱ P z ⊤ ω} :=
    measurableSet_lt measurable_const (measurable_nW_top ℱ z)
  calc ∫⁻ ω in {ω | (l' : ℝ≥0∞) < nW ℱ P z ⊤ ω}, (nW ℱ P z ⊤ ω - l') ∂P
      ≤ ∫⁻ ω in {ω | (l' : ℝ≥0∞) < nW ℱ P z ⊤ ω}, nR ℱ P z l' ω ∂P := by
        apply lintegral_mono
        intro ω
        calc nW ℱ P z ⊤ ω - l' ≤ nW ℱ P z ⊤ ω - nW ℱ P z (nStop ℱ P z l' ω) ω :=
              tsub_le_tsub_left (nW_stop_le ℱ z l' ω) _
          _ ≤ nR ℱ P z l' ω := by
              rw [tsub_le_iff_right, add_comm]
              exact (nW_top_eq_stop_add ℱ z l' ω).le
    _ ≤ ∫⁻ ω, nR ℱ P z l' ω ∂P := setLIntegral_le_lintegral _ _
    _ = ∫⁻ ω, nR' ℱ P z l' ω ∂P := nR_le_nR' ℱ z hz l'
    _ = ∫⁻ ω, ({ω | (l' : ℝ≥0∞) < nW ℱ P z ⊤ ω}).indicator (nR' ℱ P z l') ω ∂P := by
        congr 1
        ext ω
        by_cases h : (l' : ℝ≥0∞) < nW ℱ P z ⊤ ω
        · rw [Set.indicator_of_mem (show ω ∈ {ω | (l' : ℝ≥0∞) < nW ℱ P z ⊤ ω} from h)]
        · rw [Set.indicator_of_notMem (show ω ∉ {ω | (l' : ℝ≥0∞) < nW ℱ P z ⊤ ω} from h)]
          exact nR'_eq_zero ℱ z l' ω h
    _ = ∫⁻ ω in {ω | (l' : ℝ≥0∞) < nW ℱ P z ⊤ ω}, nR' ℱ P z l' ω ∂P := lintegral_indicator hA _
    _ ≤ ∫⁻ ω in {ω | (l' : ℝ≥0∞) < nW ℱ P z ⊤ ω}, (∑' k : ℕ, z (k + 1) ω) ∂P :=
        lintegral_mono (fun ω => nR'_le ℱ z l' ω)

end BurkholderDFI.ConvexPhi

open BurkholderDFI.ConvexPhi


theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (z : ℕ → Ω → ℝ≥0∞) (hz : ∀ k, Measurable (z k)) :
    ∀ l : ℝ, 0 < l →
      (∫⁻ ω in {ω | ENNReal.ofReal l <
        ∑' k : ℕ, condLExp (ℱ k) P (z (k + 1)) ω},
        ((∑' k : ℕ, condLExp (ℱ k) P (z (k + 1)) ω) - ENNReal.ofReal l) ∂P)
      ≤ (∫⁻ ω in {ω | ENNReal.ofReal l <
        ∑' k : ℕ, condLExp (ℱ k) P (z (k + 1)) ω},
        (∑' k : ℕ, z (k + 1) ω) ∂P) := by
  exact neveu_pair_ineq_core P ℱ z hz
