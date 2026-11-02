-- Prove2me | solution 1 for DirectFidelity.State.eq_16
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:19:55.548231+00:00
-- url     : https://prove2.me/submissions/3785d7b4-3b1d-4ded-9a1e-1fd7317b5f7c

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_DirectFidelity_State_Setting
open scoped ComplexOrder NNReal ENNReal
set_option autoImplicit false

open DirectFidelity.State MeasureTheory ProbabilityTheory

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
    IsProbabilityMeasure (outcomeLaw σ k) := by
  obtain ⟨h1, h2⟩ := trace_W_bounds σ hσ k
  refine ⟨?_⟩
  simp only [outcomeLaw, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply,
    ENNReal.smul_def, smul_eq_mul, mul_one, ← ENNReal.coe_add]
  have hp : 0 ≤ (1 + ((σ * W k).trace).re) / 2 := by linarith
  have hq : 0 ≤ (1 - ((σ * W k).trace).re) / 2 := by linarith
  rw [← Real.toNNReal_add hp hq]
  have hsum : (1 + ((σ * W k).trace).re) / 2 + (1 - ((σ * W k).trace).re) / 2 = 1 := by ring
  rw [hsum, Real.toNNReal_one, ENNReal.coe_one]

private lemma hasSubgaussianMGF_outcomeLaw {n : ℕ} (σ : Matrix (Q n) (Q n) ℂ)
    (hσ : WildeQIT.IsDensityOperator σ) (k : P n) :
    HasSubgaussianMGF (fun x : ℝ => x - ((σ * W k).trace).re) 1 (outcomeLaw σ k) := by
  have : IsProbabilityMeasure (outcomeLaw σ k) := isProbabilityMeasure_outcomeLaw σ hσ k
  obtain ⟨h1, h2⟩ := trace_W_bounds σ hσ k
  set μ_k : ℝ := ((σ * W k).trace).re
  have hm : AEMeasurable (fun x : ℝ => x - μ_k) (outcomeLaw σ k) :=
    (measurable_id.sub measurable_const).aemeasurable
  have hb : ∀ᵐ x ∂(outcomeLaw σ k), x - μ_k ∈ Set.Icc (-1 - μ_k) (1 - μ_k) := by
    rw [ae_iff]
    simp [outcomeLaw]
  have hc : ∫ x : ℝ, (x - μ_k) ∂(outcomeLaw σ k) = 0 := by
    set p : ℝ≥0 := Real.toNNReal ((1 + μ_k) / 2)
    set q : ℝ≥0 := Real.toNNReal ((1 - μ_k) / 2)
    have h_int1 : Integrable (fun x : ℝ => x - μ_k) (p • Measure.dirac (1 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure ENNReal.coe_ne_top
    have h_int2 : Integrable (fun x : ℝ => x - μ_k) (q • Measure.dirac (-1 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure ENNReal.coe_ne_top
    change ∫ x : ℝ, (x - μ_k) ∂(p • Measure.dirac (1 : ℝ) + q • Measure.dirac (-1 : ℝ)) = 0
    rw [integral_add_measure h_int1 h_int2, integral_smul_nnreal_measure,
      integral_smul_nnreal_measure, integral_dirac, integral_dirac]
    have hp : (p : ℝ) = (1 + μ_k) / 2 := Real.coe_toNNReal _ (by linarith)
    have hq : (q : ℝ) = (1 - μ_k) / 2 := Real.coe_toNNReal _ (by linarith)
    simp only [NNReal.smul_def, smul_eq_mul, hp, hq]
    ring
  have h_subg := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm hb hc
  have h_param : ((‖(1 - μ_k) - (-1 - μ_k)‖₊ / 2) ^ 2 : ℝ≥0) = 1 := by
    have h_diff : (1 - μ_k) - (-1 - μ_k) = 2 := by ring
    rw [h_diff]
    ext
    norm_num
  rwa [h_param] at h_subg

private lemma hasSubgaussianMGF_scaled {n : ℕ} (σ : Matrix (Q n) (Q n) ℂ)
    (hσ : WildeQIT.IsDensityOperator σ) (k : P n) (r : ℝ) :
    HasSubgaussianMGF (fun x : ℝ => r * (x - ((σ * W k).trace).re))
      (Real.toNNReal (r ^ 2)) (outcomeLaw σ k) := by
  have h1 := (hasSubgaussianMGF_outcomeLaw σ hσ k).const_mul r
  convert h1 using 2
  erw [mul_one]
  ext
  exact Real.coe_toNNReal (r ^ 2) (sq_nonneg r)

theorem solution (n ℓ : ℕ) (ρ σ : Matrix (Q n) (Q n) ℂ) (hρ : IsPure ρ)
    (hσ : WildeQIT.IsDensityOperator σ) (hℓ : 0 < ℓ) (ks : Fin ℓ → P n)
    (hks : ∀ i, chi ρ (ks i) ≠ 0) (m : Fin ℓ → ℕ) (hm : ∀ i, 0 < m i) (t : ℝ) (ht : 0 < t) :
    (outcomes σ ks m).real {A | t ≤ |Yt ρ ks m A - Y ρ σ ks|} ≤
      2 * Real.exp (-2 * t ^ 2 / Chof ρ ks m) := by
  rcases hρ with ⟨_, _, _⟩
  have : ∀ s : Slot m, IsProbabilityMeasure (outcomeLaw σ (ks s.1)) :=
    fun s => isProbabilityMeasure_outcomeLaw σ hσ (ks s.1)
  have : IsProbabilityMeasure (outcomes σ ks m) := by
    unfold outcomes
    infer_instance
  let g : Slot m → ℝ → ℝ := fun s x =>
    cHoef ρ ks m s.1 * (x - ((σ * W (ks s.1)).trace).re)
  let Z : Slot m → (Slot m → ℝ) → ℝ := fun s A => g s (A s)
  let c : Slot m → ℝ≥0 := fun s => Real.toNNReal ((cHoef ρ ks m s.1) ^ 2)
  have h_indep : iIndepFun Z (outcomes σ ks m) := by
    unfold outcomes Z
    exact iIndepFun_pi fun s => (by fun_prop : Measurable (g s)).aemeasurable
  have h_subG : ∀ s ∈ (Finset.univ : Finset (Slot m)),
      HasSubgaussianMGF (Z s) (c s) (outcomes σ ks m) := by
    intro s _
    have h1 : HasSubgaussianMGF (g s) (c s) (outcomeLaw σ (ks s.1)) :=
      hasSubgaussianMGF_scaled σ hσ (ks s.1) (cHoef ρ ks m s.1)
    have h_map : (outcomes σ ks m).map (Function.eval s) = outcomeLaw σ (ks s.1) := by
      unfold outcomes
      exact (measurePreserving_eval (fun s : Slot m => outcomeLaw σ (ks s.1)) s).map_eq
    have hY : AEMeasurable (Function.eval s) (outcomes σ ks m) :=
      (measurable_pi_apply s).aemeasurable
    refine ⟨fun u => ?_, fun u => ?_⟩
    · have hint := h1.integrable_exp_mul u
      rw [← h_map] at hint
      exact (integrable_map_measure hint.aestronglyMeasurable hY).mp hint
    · have hint := (h1.integrable_exp_mul u).1
      rw [← h_map] at hint
      have hmgf := h1.mgf_le u
      rw [← h_map, mgf_map hY hint] at hmgf
      exact hmgf
  have h_sum_subG : HasSubgaussianMGF (fun A : Slot m → ℝ => ∑ s : Slot m, Z s A)
      (∑ s : Slot m, c s) (outcomes σ ks m) :=
    HasSubgaussianMGF.sum_of_iIndepFun h_indep h_subG
  have h_right := h_sum_subG.measure_ge_le ht.le
  have h_left := h_sum_subG.neg.measure_ge_le ht.le
  have h_Yt_sub_Y : ∀ A : Slot m → ℝ, Yt ρ ks m A - Y ρ σ ks = ∑ s : Slot m, Z s A := by
    intro A
    have hYt : Yt ρ ks m A = ∑ s : Slot m, cHoef ρ ks m s.1 * A s := by
      rw [Fintype.sum_sigma]
      unfold Yt Xt cHoef
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    have hY : Y ρ σ ks = ∑ s : Slot m, cHoef ρ ks m s.1 * ((σ * W (ks s.1)).trace).re := by
      rw [Fintype.sum_sigma]
      unfold Y X cHoef
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hmi_ne : (m i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (hm i))
      have hℓ_ne : (ℓ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hℓ)
      have hdim_pos : 0 < dim n := by unfold dim; positivity
      have hsqrt_ne : Real.sqrt (dim n) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hdim_pos)
      have hchi_ne : chi ρ (ks i) ≠ 0 := hks i
      unfold chi at *
      field_simp [hmi_ne, hℓ_ne, hsqrt_ne, hchi_ne]
    rw [hYt, hY, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Z, g, mul_sub]
  have h_Chof : Chof ρ ks m = 4 * (↑(∑ s : Slot m, c s) : ℝ) := by
    unfold Chof
    rw [NNReal.coe_sum, Fintype.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => ?_
    have hc_coe : ((c ⟨i, ‹_›⟩ : ℝ≥0) : ℝ) = (cHoef ρ ks m i) ^ 2 :=
      Real.coe_toNNReal _ (sq_nonneg _)
    rw [hc_coe]
    ring
  have h_exp_eq : -t ^ 2 / (2 * (↑(∑ s : Slot m, c s) : ℝ)) = -2 * t ^ 2 / Chof ρ ks m := by
    rw [h_Chof]
    calc
      -t ^ 2 / (2 * (↑(∑ s : Slot m, c s) : ℝ))
          = (2 * (-t ^ 2)) / (2 * (2 * (↑(∑ s : Slot m, c s) : ℝ))) := by
            symm
            exact mul_div_mul_left (-t ^ 2) (2 * (↑(∑ s : Slot m, c s) : ℝ)) (by norm_num)
      _ = -2 * t ^ 2 / (4 * (↑(∑ s : Slot m, c s) : ℝ)) := by ring
  set μ := outcomes σ ks m
  set S : Set (Slot m → ℝ) := {A | t ≤ |Yt ρ ks m A - Y ρ σ ks|}
  set S₁ : Set (Slot m → ℝ) := {A | t ≤ ∑ s : Slot m, Z s A}
  set S₂ : Set (Slot m → ℝ) := {A | t ≤ -(∑ s : Slot m, Z s A)}
  have h_sub : S ⊆ S₁ ∪ S₂ := by
    intro A hA
    simp only [S, Set.mem_setOf_eq, h_Yt_sub_Y A] at hA
    exact le_abs.mp hA
  have h_meas_le : μ S ≤ μ S₁ + μ S₂ :=
    (measure_mono h_sub).trans (measure_union_le S₁ S₂)
  have h_ne1 : μ S₁ ≠ ⊤ := measure_ne_top μ S₁
  have h_ne2 : μ S₂ ≠ ⊤ := measure_ne_top μ S₂
  have h_real_le : μ.real S ≤ μ.real S₁ + μ.real S₂ := by
    have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h_ne1, h_ne2⟩) h_meas_le
    simpa [measureReal_def, ENNReal.toReal_add h_ne1 h_ne2] using h1
  have h_r : μ.real S₁ ≤ Real.exp (-2 * t ^ 2 / Chof ρ ks m) := by
    rw [← h_exp_eq]
    exact h_right
  have h_l : μ.real S₂ ≤ Real.exp (-2 * t ^ 2 / Chof ρ ks m) := by
    rw [← h_exp_eq]
    exact h_left
  linarith
