-- Prove2me | solution 1 for DirectFidelity.State.dfe_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:08:50.309717+00:00
-- url     : https://prove2.me/submissions/27b78987-42f3-4bfb-ae21-3f3f54d588dc

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_DirectFidelity_State_Setting
import Theorems.Thm_DirectFidelity_State_prob_normalized
import Theorems.Thm_DirectFidelity_State_eq_5
import Theorems.Thm_DirectFidelity_State_eq_8
open scoped ComplexOrder
set_option autoImplicit false

open DirectFidelity.State

private lemma pauli1_star (c : Fin 4) (a b : Fin 2) :
    star (pauli1 c b a) = pauli1 c a b := by
  fin_cases c <;> fin_cases a <;> fin_cases b <;> simp [pauli1]

private lemma W_conjTranspose {n : ℕ} (k : P n) :
    (W k).conjTranspose = W k := by
  ext x y
  simp only [Matrix.conjTranspose_apply, W, star_prod]
  exact Finset.prod_congr rfl fun i _ => pauli1_star (k i) (x i) (y i)

private lemma pauli1_sq (c : Fin 4) (a b : Fin 2) :
    (∑ z : Fin 2, pauli1 c a z * pauli1 c z b) = if a = b then 1 else 0 := by
  fin_cases c <;> fin_cases a <;> fin_cases b <;>
    simp [pauli1, Fin.sum_univ_two]

private lemma W_mul_self {n : ℕ} (k : P n) :
    W k * W k = 1 := by
  ext x y
  simp only [Matrix.mul_apply, W, Matrix.one_apply]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin n) (z : Fin 2) =>
    pauli1 (k i) (x i) z * pauli1 (k i) z (y i))]
  simp_rw [pauli1_sq]
  by_cases hxy : x = y
  · subst hxy
    simp
  · have hne : ∃ i : Fin n, x i ≠ y i := by
      by_contra h
      exact hxy (funext fun i => not_ne_iff.mp (fun hi => h ⟨i, hi⟩))
    rcases hne with ⟨i, hi⟩
    rw [if_neg hxy]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

private lemma trace_W_bounds {n : ℕ} (σ : Matrix (Q n) (Q n) ℂ)
    (hσ : WildeQIT.IsDensityOperator σ) (k : P n) :
    -1 ≤ ((σ * W k).trace).re ∧ ((σ * W k).trace).re ≤ 1 := by
  set U := W k
  set A : Matrix (Q n) (Q n) ℂ := 1 - U
  set B : Matrix (Q n) (Q n) ℂ := 1 + U
  have hA_conj : A.conjTranspose = A := by
    simp [A, U, Matrix.conjTranspose_sub, W_conjTranspose]
  have hB_conj : B.conjTranspose = B := by
    simp [B, U, Matrix.conjTranspose_add, W_conjTranspose]
  have hA_sq : A * A = 1 + 1 - (U + U) := by
    simp only [A, sub_mul, mul_sub, mul_one, one_mul, U, W_mul_self]
    abel
  have hB_sq : B * B = 1 + 1 + (U + U) := by
    simp only [B, add_mul, mul_add, mul_one, one_mul, U, W_mul_self]
    abel
  have hA_nonneg : 0 ≤ ((A.conjTranspose * σ * A).trace).re :=
    (Complex.nonneg_iff.mp (hσ.1.conjTranspose_mul_mul_same A).trace_nonneg).1
  have hB_nonneg : 0 ≤ ((B.conjTranspose * σ * B).trace).re :=
    (Complex.nonneg_iff.mp (hσ.1.conjTranspose_mul_mul_same B).trace_nonneg).1
  have htrA : (A.conjTranspose * σ * A).trace = 1 + 1 - ((σ * U).trace + (σ * U).trace) := by
    rw [Matrix.trace_mul_comm (A.conjTranspose * σ) A, ← Matrix.mul_assoc, hA_conj, hA_sq]
    simp only [sub_mul, add_mul, one_mul, Matrix.trace_sub, Matrix.trace_add, hσ.2,
      Matrix.trace_mul_comm U σ]
  have htrB : (B.conjTranspose * σ * B).trace = 1 + 1 + ((σ * U).trace + (σ * U).trace) := by
    rw [Matrix.trace_mul_comm (B.conjTranspose * σ) B, ← Matrix.mul_assoc, hB_conj, hB_sq]
    simp only [add_mul, one_mul, Matrix.trace_add, hσ.2, Matrix.trace_mul_comm U σ]
  have htrA_re : ((A.conjTranspose * σ * A).trace).re =
      1 + 1 - (((σ * U).trace).re + ((σ * U).trace).re) := by
    rw [htrA]
    simp
  have htrB_re : ((B.conjTranspose * σ * B).trace).re =
      1 + 1 + (((σ * U).trace).re + ((σ * U).trace).re) := by
    rw [htrB]
    simp
  constructor <;> linarith

private lemma isProbabilityMeasure_outcomeLaw {n : ℕ} (σ : Matrix (Q n) (Q n) ℂ)
    (hσ : WildeQIT.IsDensityOperator σ) (k : P n) :
    MeasureTheory.IsProbabilityMeasure (outcomeLaw σ k) := by
  obtain ⟨h1, h2⟩ := trace_W_bounds σ hσ k
  refine ⟨?_⟩
  simp only [outcomeLaw, MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply,
    MeasureTheory.Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply,
    ENNReal.smul_def, smul_eq_mul, mul_one, ← ENNReal.coe_add]
  have hp : 0 ≤ (1 + ((σ * W k).trace).re) / 2 := by linarith
  have hq : 0 ≤ (1 - ((σ * W k).trace).re) / 2 := by linarith
  rw [← Real.toNNReal_add hp hq]
  have hsum : (1 + ((σ * W k).trace).re) / 2 + (1 - ((σ * W k).trace).re) / 2 = 1 := by ring
  rw [hsum, Real.toNNReal_one, ENNReal.coe_one]

theorem solution (n : ℕ) (ρ σ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ)
    (hσ : WildeQIT.IsDensityOperator σ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    1 - 2 * δ ≤
      ∑ ks : Fin (ell ε δ) → P n, (∏ i, prob ρ (ks i)) *
        (outcomes σ ks (mVec ρ ε δ ks)).real
          {A | |Yt ρ ks (mVec ρ ε δ ks) A - ((ρ * σ).trace).re| ≤ 2 * ε} := by
  have h_prod_nonneg : ∀ ks : Fin (ell ε δ) → P n, 0 ≤ ∏ i, prob ρ (ks i) := by
    intro ks
    refine Finset.prod_nonneg fun i _ => ?_
    unfold prob
    positivity
  have h_term_nonneg : ∀ ks : Fin (ell ε δ) → P n,
      0 ≤ (∏ i, prob ρ (ks i)) *
        (outcomes σ ks (mVec ρ ε δ ks)).real
          {A | |Yt ρ ks (mVec ρ ε δ ks) A - ((ρ * σ).trace).re| ≤ 2 * ε} :=
    fun ks => mul_nonneg (h_prod_nonneg ks) MeasureTheory.measureReal_nonneg
  by_cases hδ1 : δ ≤ 1
  · have hprob1 : ∑ k : P n, prob ρ k = 1 := by
      have hp := DirectFidelity.State.prob_normalized n ρ hρ
      exact hp.1.trans hp.2
    have hsum_all : (∑ ks : Fin (ell ε δ) → P n, ∏ i, prob ρ (ks i)) = 1 := by
      rw [← Fintype.prod_sum]
      simp [hprob1]
    set Bad := Finset.univ.filter
      (fun ks : Fin (ell ε δ) → P n => ε ≤ |Y ρ σ ks - ((ρ * σ).trace).re|)
    set Good := Finset.univ.filter
      (fun ks : Fin (ell ε δ) → P n => ¬ ε ≤ |Y ρ σ ks - ((ρ * σ).trace).re|)
    have h_part : (∑ ks ∈ Bad, ∏ i, prob ρ (ks i)) + (∑ ks ∈ Good, ∏ i, prob ρ (ks i)) = 1 := by
      rw [Finset.sum_filter_add_sum_filter_not, hsum_all]
    have h5 : (∑ ks ∈ Bad, ∏ i, prob ρ (ks i)) ≤ δ :=
      DirectFidelity.State.eq_5 n ρ σ hρ hσ ε δ hε hδ
    have h_good_sum : 1 - δ ≤ ∑ ks ∈ Good, ∏ i, prob ρ (ks i) := by linarith
    have h_good_term : ∀ ks ∈ Good,
        (∏ i, prob ρ (ks i)) * (1 - δ) ≤
          (∏ i, prob ρ (ks i)) *
            (outcomes σ ks (mVec ρ ε δ ks)).real
              {A | |Yt ρ ks (mVec ρ ε δ ks) A - ((ρ * σ).trace).re| ≤ 2 * ε} := by
      intro ks hks_good
      have hY_lt : |Y ρ σ ks - ((ρ * σ).trace).re| < ε :=
        not_le.mp (Finset.mem_filter.mp hks_good).2
      by_cases hks : ∀ i, chi ρ (ks i) ≠ 0
      · refine mul_le_mul_of_nonneg_left ?_ (h_prod_nonneg ks)
        have : ∀ s : Slot (mVec ρ ε δ ks),
            MeasureTheory.IsProbabilityMeasure (outcomeLaw σ (ks s.1)) :=
          fun s => isProbabilityMeasure_outcomeLaw σ hσ (ks s.1)
        have : MeasureTheory.IsProbabilityMeasure (outcomes σ ks (mVec ρ ε δ ks)) := by
          unfold outcomes
          infer_instance
        set μ := outcomes σ ks (mVec ρ ε δ ks)
        set S₁ : Set (Slot (mVec ρ ε δ ks) → ℝ) :=
          {A | |Yt ρ ks (mVec ρ ε δ ks) A - ((ρ * σ).trace).re| ≤ 2 * ε}
        set S₂ : Set (Slot (mVec ρ ε δ ks) → ℝ) :=
          {A | ε ≤ |Yt ρ ks (mVec ρ ε δ ks) A - Y ρ σ ks|}
        have h_sub : (Set.univ : Set (Slot (mVec ρ ε δ ks) → ℝ)) ⊆ S₁ ∪ S₂ := by
          intro A _
          by_cases hA : ε ≤ |Yt ρ ks (mVec ρ ε δ ks) A - Y ρ σ ks|
          · exact Or.inr hA
          · left
            simp only [S₁, Set.mem_setOf_eq]
            have hA_lt : |Yt ρ ks (mVec ρ ε δ ks) A - Y ρ σ ks| < ε := not_le.mp hA
            have h_tri := abs_sub_le (Yt ρ ks (mVec ρ ε δ ks) A) (Y ρ σ ks) ((ρ * σ).trace).re
            linarith
        have h_meas_le : (1 : ENNReal) ≤ μ S₁ + μ S₂ := by
          rw [← MeasureTheory.measure_univ (μ := μ)]
          exact (MeasureTheory.measure_mono h_sub).trans (MeasureTheory.measure_union_le S₁ S₂)
        have h_ne1 : μ S₁ ≠ ⊤ := MeasureTheory.measure_ne_top μ S₁
        have h_ne2 : μ S₂ ≠ ⊤ := MeasureTheory.measure_ne_top μ S₂
        have h_real_le : 1 ≤ μ.real S₁ + μ.real S₂ := by
          have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h_ne1, h_ne2⟩) h_meas_le
          simpa [MeasureTheory.measureReal_def, ENNReal.toReal_add h_ne1 h_ne2] using h1
        have h8 : μ.real S₂ ≤ δ :=
          DirectFidelity.State.eq_8 n ρ σ hρ hσ ε δ hε hδ ks hks
        linarith
      · push_neg at hks
        rcases hks with ⟨i₀, hi₀⟩
        have hpi0 : prob ρ (ks i₀) = 0 := by simp [prob, hi₀]
        have hprod0 : (∏ i, prob ρ (ks i)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i₀) hpi0
        simp [hprod0]
    have h_sum_good_le :
        (∑ ks ∈ Good, ∏ i, prob ρ (ks i)) * (1 - δ) ≤
          ∑ ks ∈ Good, (∏ i, prob ρ (ks i)) *
            (outcomes σ ks (mVec ρ ε δ ks)).real
              {A | |Yt ρ ks (mVec ρ ε δ ks) A - ((ρ * σ).trace).re| ≤ 2 * ε} := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum h_good_term
    have h_good_le_univ :
        (∑ ks ∈ Good, (∏ i, prob ρ (ks i)) *
          (outcomes σ ks (mVec ρ ε δ ks)).real
            {A | |Yt ρ ks (mVec ρ ε δ ks) A - ((ρ * σ).trace).re| ≤ 2 * ε}) ≤
        ∑ ks : Fin (ell ε δ) → P n, (∏ i, prob ρ (ks i)) *
          (outcomes σ ks (mVec ρ ε δ ks)).real
            {A | |Yt ρ ks (mVec ρ ε δ ks) A - ((ρ * σ).trace).re| ≤ 2 * ε} :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Good)
        (fun ks _ _ => h_term_nonneg ks)
    have h_sq : (1 - δ) * (1 - δ) ≤ (∑ ks ∈ Good, ∏ i, prob ρ (ks i)) * (1 - δ) :=
      mul_le_mul_of_nonneg_right h_good_sum (by linarith)
    have h_δ_sq : 0 ≤ δ ^ 2 := sq_nonneg δ
    nlinarith
  · have h_sum_nonneg : 0 ≤
        ∑ ks : Fin (ell ε δ) → P n, (∏ i, prob ρ (ks i)) *
          (outcomes σ ks (mVec ρ ε δ ks)).real
            {A | |Yt ρ ks (mVec ρ ε δ ks) A - ((ρ * σ).trace).re| ≤ 2 * ε} :=
      Finset.sum_nonneg fun ks _ => h_term_nonneg ks
    linarith
