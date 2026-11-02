-- Prove2me | solution 1 for DirectFidelity.State.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:56:48.313226+00:00
-- url     : https://prove2.me/submissions/1f679c59-766f-4657-815f-e3c1df650fe1

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_DirectFidelity_State_Setting
import Theorems.Thm_DirectFidelity_State_eq_16
import Theorems.Thm_DirectFidelity_State_eq_18
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
      push_neg at h
      exact hxy (funext h)
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
    (hσ : WildeQIT.IsDensityOperator σ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (ks : Fin (ell ε δ) → P n) (hks : ∀ i, chi ρ (ks i) ≠ 0) :
    (outcomes σ ks (mVec ρ ε δ ks)).real
        {A | ε ≤ |Yt ρ ks (mVec ρ ε δ ks) A - Y ρ σ ks|} ≤ δ := by
  by_cases hδ1 : δ < 1
  · let ℓ := ell ε δ
    have h_pos_arg : 0 < 1 / (ε ^ 2 * δ) := by positivity
    have hℓ : 0 < ℓ := Nat.ceil_pos.mpr h_pos_arg
    have hℓ_r : 0 < (ℓ : ℝ) := Nat.cast_pos.mpr hℓ
    have hdim : 0 < dim n := by unfold dim; positivity
    have h2δ : 1 < 2 / δ := (one_lt_div hδ).mpr (by linarith)
    have hlog : 0 < Real.log (2 / δ) := Real.log_pos h2δ
    have hm : ∀ i : Fin ℓ, 0 < mVec ρ ε δ ks i := by
      intro i
      simp only [mVec, mDFE]
      have hchi2 : 0 < chi ρ (ks i) ^ 2 := sq_pos_of_ne_zero (hks i)
      exact Nat.ceil_pos.mpr (by positivity)
    have h16 := DirectFidelity.State.eq_16 n ℓ ρ σ hρ hσ hℓ ks hks (mVec ρ ε δ ks) hm ε hε
    obtain ⟨hC_eq, hC_le⟩ := DirectFidelity.State.eq_18 n ℓ ρ ε δ hε hδ hδ1 hℓ ks hks
    set C := Chof ρ ks (mVec ρ ε δ ks)
    have hC_pos : 0 < C := by
      rw [hC_eq]
      have : Nonempty (Fin ℓ) := ⟨⟨0, hℓ⟩⟩
      refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
      have hmi : 0 < (mVec ρ ε δ ks i : ℝ) := Nat.cast_pos.mpr (hm i)
      have hchi2 : 0 < chi ρ (ks i) ^ 2 := sq_pos_of_ne_zero (hks i)
      positivity
    have hC_mul : C * Real.log (2 / δ) ≤ 2 * ε ^ 2 := (le_div_iff₀ hlog).mp hC_le
    have h_log_le : Real.log (2 / δ) ≤ 2 * ε ^ 2 / C := (le_div_iff₀' hC_pos).mpr hC_mul
    have h_exp_arg : -2 * ε ^ 2 / C ≤ Real.log (δ / 2) := by
      have h1 : -2 * ε ^ 2 / C = -(2 * ε ^ 2 / C) := by ring
      have h2 : -Real.log (2 / δ) = Real.log (δ / 2) := by
        rw [← Real.log_inv, inv_div]
      linarith
    have h_exp_le : Real.exp (-2 * ε ^ 2 / C) ≤ δ / 2 := by
      calc
        Real.exp (-2 * ε ^ 2 / C) ≤ Real.exp (Real.log (δ / 2)) :=
          Real.exp_le_exp.mpr h_exp_arg
        _ = δ / 2 := Real.exp_log (by positivity)
    linarith
  · have hδ_ge : 1 ≤ δ := not_lt.mp hδ1
    have : ∀ s : Slot (mVec ρ ε δ ks),
        MeasureTheory.IsProbabilityMeasure (outcomeLaw σ (ks s.1)) :=
      fun s => isProbabilityMeasure_outcomeLaw σ hσ (ks s.1)
    have : MeasureTheory.IsProbabilityMeasure (outcomes σ ks (mVec ρ ε δ ks)) := by
      unfold outcomes
      infer_instance
    rw [MeasureTheory.measureReal_def]
    have h1 : outcomes σ ks (mVec ρ ε δ ks)
        {A | ε ≤ |Yt ρ ks (mVec ρ ε δ ks) A - Y ρ σ ks|} ≤
        outcomes σ ks (mVec ρ ε δ ks) Set.univ :=
      MeasureTheory.measure_mono (Set.subset_univ _)
    rw [MeasureTheory.measure_univ] at h1
    have hle1 : (outcomes σ ks (mVec ρ ε δ ks)
        {A | ε ≤ |Yt ρ ks (mVec ρ ε δ ks) A - Y ρ σ ks|}).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top h1
    linarith
