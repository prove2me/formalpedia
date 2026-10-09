-- Prove2me | solution 1 for GaussianMatrix.inverse_wishart_offdiag_sq_moment
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T06:25:49.548679+00:00
-- url     : https://prove2.me/submissions/6b94f201-c9b1-41f2-8cec-736434b9f501

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_full_rank_ae
import Theorems.Thm_GaussianMatrix_schur_diag_inv
import Theorems.Thm_GaussianMatrix_schur_offdiag_inv
import Theorems.Thm_GaussianMatrix_residual_law
import Theorems.Thm_GaussianMatrix_regression_residual_indep
import Theorems.Thm_GaussianMatrix_inv_sq_chi_square_moment
import Theorems.Thm_GaussianMatrix_inverse_wishart_mean

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

lemma iwg_measurable_inv_entry {r k : ℕ} (i j : Fin r) :
    Measurable (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j) := by
  have hc : Continuous (fun G : Fin r → Fin k → ℝ => Matrix.of G * (Matrix.of G)ᵀ) :=
    Continuous.matrix_mul continuous_id (Continuous.matrix_transpose continuous_id)
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (hc.matrix_det.measurable.inv).mul (hc.matrix_adjugate.matrix_elem i j).measurable

lemma iwg_det_ne_zero_of_rank {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (h : M.rank = n) :
    M.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hker : v ∈ LinearMap.ker M.mulVecLin := by simpa using hMv
  have h1 : 0 < Module.finrank ℝ (LinearMap.ker M.mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hker⟩, by simpa using hv⟩
  have h2 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Matrix.rank] at h
  simp only [Module.finrank_fin_fun] at h2
  omega

/-- Squared inverse residual: `E[Q_H(g)^{-2}] = 1/((k-n-2)(k-n-4))` for a fixed full-rank `H`. -/
lemma iwg_resid_sq_moment {n k : ℕ} (hnk : n + 5 ≤ k) (H : Matrix (Fin n) (Fin k) ℝ)
    (hH : H.rank = n) :
    Integrable (fun g : Fin k → ℝ => ((g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))⁻¹) ^ 2)
        (Measure.pi fun _ : Fin k => gaussianReal 0 1) ∧
    ∫ g, ((g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))⁻¹) ^ 2
        ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1)
      = 1 / (((k : ℝ) - n - 2) * ((k : ℝ) - n - 4)) := by
  have hq : Measurable (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g))) := by
    apply Continuous.measurable
    fun_prop
  have hlaw := residual_law H hH
  obtain ⟨hint, hval⟩ := inv_sq_chi_square_moment (d := k - n) (by omega)
  have hφ : Measurable (fun s : ℝ => (s⁻¹) ^ 2) := by fun_prop
  have hS : Measurable (fun x : Fin (k - n) → ℝ => ∑ j, x j ^ 2) := by fun_prop
  constructor
  · have h := (integrable_map_measure hφ.aestronglyMeasurable hS.aemeasurable).mpr hint
    rw [← hlaw] at h
    exact (integrable_map_measure hφ.aestronglyMeasurable hq.aemeasurable).mp h
  · rw [← integral_map hq.aemeasurable hφ.aestronglyMeasurable, hlaw,
      integral_map hS.aemeasurable hφ.aestronglyMeasurable, hval,
      Nat.cast_sub (by omega : n ≤ k)]

/-- Second moment of a linear form of a standard Gaussian vector: `E[(w·g)²] = w·w`. -/
lemma iwg_gauss_sq {k : ℕ} (w : Fin k → ℝ) :
    Integrable (fun g : Fin k → ℝ => (w ⬝ᵥ g) ^ 2) (Measure.pi fun _ : Fin k => gaussianReal 0 1) ∧
    ∫ g, (w ⬝ᵥ g) ^ 2 ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1) = w ⬝ᵥ w := by
  set μ := Measure.pi fun _ : Fin k => gaussianReal 0 1 with hμ
  have hmono : ∀ (a b : Fin k) (g : Fin k → ℝ),
      g a * g b = ∏ c, g c ^ ((if a = c then 1 else 0) + (if b = c then 1 else 0)) := by
    intro a b g
    simp only [pow_add, Finset.prod_mul_distrib, Finset.prod_pow_boole, Finset.mem_univ, if_true]
  have gint : ∀ m : ℕ, Integrable (fun x : ℝ => x ^ m) (gaussianReal 0 1) := by
    intro m
    have h := (memLp_id_gaussianReal (μ := 0) (v := 1) (m : NNReal)).integrable_norm_pow'
    refine h.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    simp [norm_pow]
  have hint2 : ∀ a b : Fin k, Integrable (fun g : Fin k → ℝ => g a * g b) μ := by
    intro a b
    simp_rw [hmono a b]
    exact Integrable.fintype_prod (f := fun c (x : ℝ) =>
      x ^ ((if a = c then 1 else 0) + (if b = c then 1 else 0))) (fun c => gint _)
  have gm2 : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
    have h := variance_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_of_integral_eq_zero aemeasurable_id
      (by simp [integral_id_gaussianReal (μ := 0) (v := 1)])] at h
    simpa using h
  have gm1 : ∫ x, x ^ 1 ∂(gaussianReal 0 1) = 0 := by
    simp [integral_id_gaussianReal (μ := 0) (v := 1)]
  have hval2 : ∀ a b : Fin k, ∫ g, g a * g b ∂μ = if a = b then 1 else 0 := by
    intro a b
    simp_rw [hmono a b]
    rw [hμ, integral_fintype_prod_eq_prod (fun c (x : ℝ) =>
      x ^ ((if a = c then 1 else 0) + (if b = c then 1 else 0)))]
    by_cases h : a = b
    · subst h
      rw [Finset.prod_eq_single a]
      · simp [gm2]
      · intro c _ hc; simp [Ne.symm hc]
      · simp
    · rw [if_neg h]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [Ne.symm h])
  have hexp : (fun g : Fin k → ℝ => (w ⬝ᵥ g) ^ 2)
      = fun g => ∑ a, ∑ b, (w a * w b) * (g a * g b) := by
    funext g
    simp only [dotProduct, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hexp]
  refine ⟨integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (hint2 a b).const_mul _, ?_⟩
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint2 a b).const_mul _]
  simp_rw [integral_finsetSum _ fun b _ => (hint2 _ b).const_mul _, integral_const_mul, hval2]
  simp [dotProduct]

/-- Conditional moment: for fixed full-rank `H`, with `c = (HHᵀ)⁻¹ H g` the regression
coefficients and `Q` the residual, `E[c_a² / Q²] = ((HHᵀ)⁻¹)_{aa} / ((k-n-2)(k-n-4))`. -/
lemma iwg_cond {n k : ℕ} (hnk : n + 5 ≤ k) (H : Matrix (Fin n) (Fin k) ℝ) (hH : H.rank = n)
    (a : Fin n) :
    Integrable (fun g : Fin k → ℝ => (((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)) a) ^ 2 *
        ((g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))⁻¹) ^ 2)
        (Measure.pi fun _ : Fin k => gaussianReal 0 1) ∧
    ∫ g, (((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)) a) ^ 2 *
        ((g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))⁻¹) ^ 2
        ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1)
      = (H * Hᵀ)⁻¹ a a * (1 / (((k : ℝ) - n - 2) * ((k : ℝ) - n - 4))) := by
  set μ := Measure.pi fun _ : Fin k => gaussianReal 0 1 with hμ
  set N := (H * Hᵀ)⁻¹ with hN
  have hdet : IsUnit (H * Hᵀ).det := by
    refine isUnit_iff_ne_zero.mpr (iwg_det_ne_zero_of_rank _ ?_)
    rw [Matrix.rank_self_mul_transpose, hH]
  have hind := regression_residual_indep H hH
  set X : (Fin k → ℝ) → (Fin n → ℝ) := fun g => H *ᵥ g with hX
  set Y : (Fin k → ℝ) → ℝ := fun g => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ (N *ᵥ (H *ᵥ g)) with hY
  set f : (Fin n → ℝ) → ℝ := fun y => ((N *ᵥ y) a) ^ 2 with hf
  set h : ℝ → ℝ := fun q => (q⁻¹) ^ 2 with hh
  have hXm : Measurable X := by
    refine measurable_pi_lambda _ fun b => ?_
    simp only [hX, Matrix.mulVec, dotProduct]; fun_prop
  have hYm : Measurable Y := by apply Continuous.measurable; simp only [hY]; fun_prop
  have hfm : Measurable f := by
    simp only [hf, Matrix.mulVec, dotProduct]; fun_prop
  have hhm : Measurable h := by simp only [hh]; fun_prop
  -- the coefficient is a linear form `w ⬝ᵥ g`
  set w : Fin k → ℝ := (N * H) a with hw
  have hfX : ∀ g, f (X g) = (w ⬝ᵥ g) ^ 2 := by
    intro g
    simp only [hf, hX, hw, Matrix.mulVec_mulVec]
    rfl
  have hww : w ⬝ᵥ w = N a a := by
    have h1 : w ⬝ᵥ w = (N * H * (N * H)ᵀ) a a := by
      simp [hw, Matrix.mul_apply, dotProduct, mul_comm]
    have hNt : Nᵀ = N := by
      rw [hN, Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [h1, Matrix.transpose_mul, hNt, show N * H * (Hᵀ * N) = N * (H * Hᵀ) * N by
      simp [Matrix.mul_assoc], hN, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  obtain ⟨hwint, hwval⟩ := iwg_gauss_sq (k := k) w
  obtain ⟨hqint, hqval⟩ := iwg_resid_sq_moment hnk H hH
  have hfXint : Integrable (fun g => f (X g)) μ := by simp_rw [hfX]; exact hwint
  have hhYint : Integrable (fun g => h (Y g)) μ := hqint
  have hind' := hind.comp hfm hhm
  constructor
  · exact hind'.integrable_mul hfXint hhYint
  · have := hind.integral_fun_comp_mul_comp hXm.aemeasurable hYm.aemeasurable
      hfm.aestronglyMeasurable hhm.aestronglyMeasurable
    change ∫ g, f (X g) * h (Y g) ∂μ = _
    rw [this]
    simp_rw [hfX]
    rw [hwval, hww]
    change N a a * ∫ g, ((g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))⁻¹) ^ 2 ∂μ = _
    rw [hqval]

end GaussianMatrix

namespace GaussianMatrix

lemma iwg_offdiag_sq {n k : ℕ} (hnk : n + 5 ≤ k) (i : Fin (n + 1)) (a : Fin n) :
    Integrable (fun G : Fin (n + 1) → Fin k → ℝ =>
        (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i (i.succAbove a) ^ 2) (gaussianMatrix (n + 1) k) ∧
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i (i.succAbove a) ^ 2 ∂(gaussianMatrix (n + 1) k)
      = (1 / ((k : ℝ) - n - 1)) * (1 / (((k : ℝ) - n - 2) * ((k : ℝ) - n - 4))) := by
  set μ : Measure (Fin k → ℝ) := Measure.pi fun _ : Fin k => gaussianReal 0 1 with hμ
  set ν : Measure (Fin n → Fin k → ℝ) := Measure.pi fun _ : Fin n => μ with hν
  set C : ℝ := 1 / (((k : ℝ) - n - 2) * ((k : ℝ) - n - 4)) with hC
  set F : (Fin (n + 1) → Fin k → ℝ) → ℝ :=
    fun G => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i (i.succAbove a) ^ 2 with hF
  have hFm : Measurable F := (iwg_measurable_inv_entry i (i.succAbove a)).pow_const 2
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin k → ℝ) i with he
  have hmp : MeasurePreserving e (gaussianMatrix (n + 1) k) (μ.prod ν) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  set Φ : (Fin k → ℝ) × (Fin n → Fin k → ℝ) → ℝ := fun p => F (e.symm p) with hΦ
  have hΦm : Measurable Φ := hFm.comp e.symm.measurable
  have hΦnn : ∀ p, 0 ≤ Φ p := fun p => sq_nonneg _
  have hschur : ∀ H : Fin n → Fin k → ℝ, (Matrix.of H).rank = n → ∀ g : Fin k → ℝ,
      Φ (g, H) = ((((Matrix.of H) * (Matrix.of H)ᵀ)⁻¹ *ᵥ (Matrix.of H *ᵥ g)) a) ^ 2 *
        ((g ⬝ᵥ g - (Matrix.of H *ᵥ g) ⬝ᵥ
          ((Matrix.of H * (Matrix.of H)ᵀ)⁻¹ *ᵥ (Matrix.of H *ᵥ g)))⁻¹) ^ 2 := by
    intro H hH g
    set G0 : Fin (n + 1) → Fin k → ℝ := Fin.insertNth i g H with hG0
    have hsub : (Matrix.of G0).submatrix i.succAbove id = Matrix.of H := by
      ext a b; simp [hG0]
    have hrow : Matrix.of G0 i = g := by funext b; simp [hG0]
    have hdet : ((Matrix.of G0).submatrix i.succAbove id *
        ((Matrix.of G0).submatrix i.succAbove id)ᵀ).det ≠ 0 := by
      rw [hsub]
      exact iwg_det_ne_zero_of_rank _ (by rw [Matrix.rank_self_mul_transpose, hH])
    have h1 := schur_diag_inv (Matrix.of G0) i hdet
    have h2 := schur_offdiag_inv (Matrix.of G0) i a hdet
    rw [hsub, hrow] at h1 h2
    rw [h1] at h2
    have : Φ (g, H) = (Matrix.of G0 * (Matrix.of G0)ᵀ)⁻¹ i (i.succAbove a) ^ 2 := rfl
    rw [this, h2]
    ring
  have hrank : ∀ᵐ H ∂ν, (Matrix.of H).rank = n := by
    have := full_rank_ae n k
    filter_upwards [this] with H hH
    rw [hH]; omega
  have hinner : ∀ᵐ H ∂ν, Integrable (fun g => Φ (g, H)) μ ∧
      ∫ g, Φ (g, H) ∂μ = (Matrix.of H * (Matrix.of H)ᵀ)⁻¹ a a * C := by
    filter_upwards [hrank] with H hH
    simp_rw [hschur H hH]
    exact iwg_cond hnk (Matrix.of H) hH a
  obtain ⟨hmint, hmval⟩ := inverse_wishart_mean (r := n) (k := k) (by omega)
  have hmint' : Integrable (fun H : Fin n → Fin k → ℝ =>
      (Matrix.of H * (Matrix.of H)ᵀ)⁻¹ a a * C) ν := (hmint a a).mul_const C
  have hint : Integrable Φ (μ.prod ν) := by
    rw [integrable_prod_iff' hΦm.aestronglyMeasurable]
    refine ⟨hinner.mono fun H h => h.1, ?_⟩
    refine hmint'.congr ?_
    filter_upwards [hinner] with H hH
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hΦnn _)]
    exact hH.2.symm
  constructor
  · have := (hmp.integrable_comp_emb e.measurableEmbedding (g := Φ)).mpr hint
    refine this.congr (Filter.Eventually.of_forall fun G => ?_)
    simp [hΦ, hF]
  · have h1 := hmp.integral_comp' Φ
    simp only [hΦ, MeasurableEquiv.symm_apply_apply] at h1
    rw [h1, integral_prod_symm Φ hint]
    rw [integral_congr_ae (hinner.mono fun H h => h.2)]
    rw [integral_mul_const]
    change (∫ H, (Matrix.of H * (Matrix.of H)ᵀ)⁻¹ a a ∂(gaussianMatrix n k)) * C = _
    rw [hmval a a, Matrix.one_apply_eq, mul_one]

end GaussianMatrix

open GaussianMatrix

theorem solution {r k : ℕ} (hrk : r + 4 ≤ k) (i j : Fin r) (hij : i ≠ j) :
    Integrable (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ^ 2)
      (gaussianMatrix r k) ∧
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ^ 2 ∂(gaussianMatrix r k)
      = 1 / (((k : ℝ) - r) * ((k : ℝ) - r - 1) * ((k : ℝ) - r - 3)) := by
  cases r with
  | zero => exact i.elim0
  | succ n =>
    obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
    obtain ⟨h1, h2⟩ := iwg_offdiag_sq (by omega : n + 5 ≤ k) i a
    refine ⟨h1, ?_⟩
    rw [h2]
    have hx : (4 : ℝ) ≤ (k : ℝ) - (n + 1) := by
      have : ((n + 1 + 4 : ℕ) : ℝ) ≤ k := by exact_mod_cast hrk
      push_cast at this; linarith
    have h3 : (k : ℝ) - n - 1 ≠ 0 := by linarith
    have h4 : (k : ℝ) - n - 2 ≠ 0 := by linarith
    have h5 : (k : ℝ) - n - 4 ≠ 0 := by linarith
    push_cast
    rw [div_mul_div_comm, one_mul]
    congr 1
    ring
