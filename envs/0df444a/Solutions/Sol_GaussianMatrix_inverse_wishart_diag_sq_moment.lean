-- Prove2me | solution 1 for GaussianMatrix.inverse_wishart_diag_sq_moment
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T06:22:38.776056+00:00
-- url     : https://prove2.me/submissions/4281d795-34e6-4d9a-8ab2-a1aba90a548b

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_full_rank_ae
import Theorems.Thm_GaussianMatrix_schur_diag_inv
import Theorems.Thm_GaussianMatrix_residual_law
import Theorems.Thm_GaussianMatrix_inv_sq_chi_square_moment

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

lemma iwd_measurable_inv_entry {r k : ℕ} (i j : Fin r) :
    Measurable (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j) := by
  have hc : Continuous (fun G : Fin r → Fin k → ℝ => Matrix.of G * (Matrix.of G)ᵀ) :=
    Continuous.matrix_mul continuous_id (Continuous.matrix_transpose continuous_id)
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (hc.matrix_det.measurable.inv).mul (hc.matrix_adjugate.matrix_elem i j).measurable

lemma iwd_det_ne_zero_of_rank {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (h : M.rank = n) :
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
lemma iwd_resid_sq_moment {n k : ℕ} (hnk : n + 5 ≤ k) (H : Matrix (Fin n) (Fin k) ℝ)
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

lemma iwd_diag_sq {n k : ℕ} (hnk : n + 5 ≤ k) (i : Fin (n + 1)) :
    Integrable (fun G : Fin (n + 1) → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ^ 2)
        (gaussianMatrix (n + 1) k) ∧
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ^ 2 ∂(gaussianMatrix (n + 1) k)
      = 1 / (((k : ℝ) - n - 2) * ((k : ℝ) - n - 4)) := by
  set μ : Measure (Fin k → ℝ) := Measure.pi fun _ : Fin k => gaussianReal 0 1 with hμ
  set ν : Measure (Fin n → Fin k → ℝ) := Measure.pi fun _ : Fin n => μ with hν
  set F : (Fin (n + 1) → Fin k → ℝ) → ℝ :=
    fun G => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ^ 2 with hF
  have hFm : Measurable F := (iwd_measurable_inv_entry i i).pow_const 2
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin k → ℝ) i with he
  have hmp : MeasurePreserving e (gaussianMatrix (n + 1) k) (μ.prod ν) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  set Φ : (Fin k → ℝ) × (Fin n → Fin k → ℝ) → ℝ := fun p => F (e.symm p) with hΦ
  have hΦm : Measurable Φ := hFm.comp e.symm.measurable
  have hΦnn : ∀ p, 0 ≤ Φ p := fun p => sq_nonneg _
  have hschur : ∀ H : Fin n → Fin k → ℝ, (Matrix.of H).rank = n → ∀ g : Fin k → ℝ,
      Φ (g, H) = ((g ⬝ᵥ g - (Matrix.of H *ᵥ g) ⬝ᵥ
        ((Matrix.of H * (Matrix.of H)ᵀ)⁻¹ *ᵥ (Matrix.of H *ᵥ g)))⁻¹) ^ 2 := by
    intro H hH g
    set G0 : Fin (n + 1) → Fin k → ℝ := Fin.insertNth i g H with hG0
    have hsub : (Matrix.of G0).submatrix i.succAbove id = Matrix.of H := by
      ext a b; simp [hG0]
    have hrow : Matrix.of G0 i = g := by funext b; simp [hG0]
    have hdet : ((Matrix.of G0).submatrix i.succAbove id *
        ((Matrix.of G0).submatrix i.succAbove id)ᵀ).det ≠ 0 := by
      rw [hsub]
      exact iwd_det_ne_zero_of_rank _ (by rw [Matrix.rank_self_mul_transpose, hH])
    have := schur_diag_inv (Matrix.of G0) i hdet
    rw [hsub, hrow] at this
    simp only [hΦ, hF, he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    rw [← this]
    rfl
  have hrank : ∀ᵐ H ∂ν, (Matrix.of H).rank = n := by
    have := full_rank_ae n k
    filter_upwards [this] with H hH
    rw [hH]; omega
  have hinner : ∀ᵐ H ∂ν, Integrable (fun g => Φ (g, H)) μ ∧
      ∫ g, Φ (g, H) ∂μ = 1 / (((k : ℝ) - n - 2) * ((k : ℝ) - n - 4)) := by
    filter_upwards [hrank] with H hH
    simp_rw [hschur H hH]
    exact iwd_resid_sq_moment hnk (Matrix.of H) hH
  have hint : Integrable Φ (μ.prod ν) := by
    rw [integrable_prod_iff' hΦm.aestronglyMeasurable]
    refine ⟨hinner.mono fun H h => h.1, ?_⟩
    refine (integrable_const (1 / (((k : ℝ) - n - 2) * ((k : ℝ) - n - 4)))).congr ?_
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
    simp

end GaussianMatrix

open GaussianMatrix

theorem solution {r k : ℕ} (hrk : r + 4 ≤ k) (i : Fin r) :
    Integrable (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ^ 2)
      (gaussianMatrix r k) ∧
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ^ 2 ∂(gaussianMatrix r k)
      = 1 / (((k : ℝ) - r - 1) * ((k : ℝ) - r - 3)) := by
  cases r with
  | zero => exact i.elim0
  | succ n =>
    obtain ⟨h1, h2⟩ := iwd_diag_sq (by omega : n + 5 ≤ k) i
    refine ⟨h1, ?_⟩
    rw [h2]
    push_cast
    ring_nf
