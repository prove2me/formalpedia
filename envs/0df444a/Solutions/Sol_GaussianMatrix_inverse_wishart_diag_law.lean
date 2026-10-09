-- Prove2me | solution 1 for GaussianMatrix.inverse_wishart_diag_law
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T05:04:12.355546+00:00
-- url     : https://prove2.me/submissions/f3229cd0-bdde-4cba-83e8-c724240cde50

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_full_rank_ae
import Theorems.Thm_GaussianMatrix_schur_diag_inv
import Theorems.Thm_GaussianMatrix_residual_law

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

lemma iwdl_measurable_inv_entry {r k : ℕ} (i j : Fin r) :
    Measurable (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j) := by
  have hc : Continuous (fun G : Fin r → Fin k → ℝ => Matrix.of G * (Matrix.of G)ᵀ) :=
    Continuous.matrix_mul continuous_id (Continuous.matrix_transpose continuous_id)
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (hc.matrix_det.measurable.inv).mul (hc.matrix_adjugate.matrix_elem i j).measurable

lemma iwdl_det_ne_zero_of_rank {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (h : M.rank = n) :
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

/-- The law of the inverse squared residual of a standard Gaussian vector against a fixed
full-rank `n × k` matrix is the law of `1/χ²_{k-n}`. -/
lemma iwdl_resid_inv_law {n k : ℕ} (H : Matrix (Fin n) (Fin k) ℝ) (hH : H.rank = n) :
    Measure.map (fun g : Fin k → ℝ => (g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))⁻¹)
        (Measure.pi fun _ : Fin k => gaussianReal 0 1)
      = Measure.map (fun x : Fin (k - n) → ℝ => (∑ j, x j ^ 2)⁻¹)
        (Measure.pi fun _ : Fin (k - n) => gaussianReal 0 1) := by
  have hq : Measurable (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g))) := by
    apply Continuous.measurable
    fun_prop
  have hS : Measurable (fun x : Fin (k - n) → ℝ => ∑ j, x j ^ 2) := by fun_prop
  have h1 := Measure.map_map (μ := Measure.pi fun _ : Fin k => gaussianReal 0 1) measurable_inv hq
  have h2 := Measure.map_map (μ := Measure.pi fun _ : Fin (k - n) => gaussianReal 0 1)
    measurable_inv hS
  rw [Function.comp_def] at h1 h2
  rw [← h1, ← h2, residual_law H hH]

lemma iwdl_main {n k : ℕ} (hnk : n ≤ k) (i : Fin (n + 1)) :
    Measure.map (fun G : Fin (n + 1) → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i)
        (gaussianMatrix (n + 1) k)
      = Measure.map (fun x : Fin (k - n) → ℝ => (∑ j, x j ^ 2)⁻¹)
        (Measure.pi fun _ : Fin (k - n) => gaussianReal 0 1) := by
  set μ : Measure (Fin k → ℝ) := Measure.pi fun _ : Fin k => gaussianReal 0 1 with hμ
  set ν : Measure (Fin n → Fin k → ℝ) := Measure.pi fun _ : Fin n => μ with hν
  set F : (Fin (n + 1) → Fin k → ℝ) → ℝ := fun G => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i with hF
  have hFm : Measurable F := iwdl_measurable_inv_entry i i
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin k → ℝ) i with he
  have hmp : MeasurePreserving e (gaussianMatrix (n + 1) k) (μ.prod ν) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  set Φ : (Fin k → ℝ) × (Fin n → Fin k → ℝ) → ℝ := fun p => F (e.symm p) with hΦ
  have hΦm : Measurable Φ := hFm.comp e.symm.measurable
  have hschur : ∀ H : Fin n → Fin k → ℝ, (Matrix.of H).rank = n → ∀ g : Fin k → ℝ,
      Φ (g, H) = (g ⬝ᵥ g - (Matrix.of H *ᵥ g) ⬝ᵥ
        ((Matrix.of H * (Matrix.of H)ᵀ)⁻¹ *ᵥ (Matrix.of H *ᵥ g)))⁻¹ := by
    intro H hH g
    set G0 : Fin (n + 1) → Fin k → ℝ := Fin.insertNth i g H with hG0
    have hsub : (Matrix.of G0).submatrix i.succAbove id = Matrix.of H := by
      ext a b; simp [hG0]
    have hrow : Matrix.of G0 i = g := by funext b; simp [hG0]
    have hdet : ((Matrix.of G0).submatrix i.succAbove id *
        ((Matrix.of G0).submatrix i.succAbove id)ᵀ).det ≠ 0 := by
      rw [hsub]
      exact iwdl_det_ne_zero_of_rank _ (by rw [Matrix.rank_self_mul_transpose, hH])
    have := schur_diag_inv (Matrix.of G0) i hdet
    rw [hsub, hrow] at this
    simp only [hΦ, hF, he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    exact this
  have hrank : ∀ᵐ H ∂ν, (Matrix.of H).rank = n := by
    have := full_rank_ae n k
    filter_upwards [this] with H hH
    rw [hH]; omega
  have hmap : Measure.map F (gaussianMatrix (n + 1) k) = Measure.map Φ (μ.prod ν) := by
    rw [← hmp.map_eq, Measure.map_map hΦm e.measurable]
    congr 1
    funext G
    simp [hΦ]
  rw [hmap]
  ext s hs
  rw [Measure.map_apply hΦm hs, Measure.prod_apply_symm (hΦm hs)]
  have hinner : ∀ᵐ H ∂ν, μ ((fun g => (g, H)) ⁻¹' (Φ ⁻¹' s))
      = (Measure.map (fun x : Fin (k - n) → ℝ => (∑ j, x j ^ 2)⁻¹)
          (Measure.pi fun _ : Fin (k - n) => gaussianReal 0 1)) s := by
    filter_upwards [hrank] with H hH
    have hq : Measurable (fun g : Fin k → ℝ => (g ⬝ᵥ g - (Matrix.of H *ᵥ g) ⬝ᵥ
        ((Matrix.of H * (Matrix.of H)ᵀ)⁻¹ *ᵥ (Matrix.of H *ᵥ g)))⁻¹) := by
      apply Measurable.inv
      apply Continuous.measurable
      fun_prop
    rw [← iwdl_resid_inv_law (Matrix.of H) hH, Measure.map_apply hq hs]
    congr 1
    ext g
    simp only [Set.mem_preimage]
    rw [hschur H hH g]
  rw [lintegral_congr_ae hinner, lintegral_const, measure_univ, mul_one]

end GaussianMatrix

open GaussianMatrix

theorem solution {r k : ℕ} (hrk : r ≤ k) (i : Fin r) :
    Measure.map (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i)
        (gaussianMatrix r k)
      = Measure.map (fun x : Fin (k - r + 1) → ℝ => (∑ j, x j ^ 2)⁻¹)
        (Measure.pi fun _ : Fin (k - r + 1) => gaussianReal 0 1) := by
  cases r with
  | zero => exact i.elim0
  | succ n =>
    have h : k - (n + 1) + 1 = k - n := by omega
    rw [h]
    exact iwdl_main (by omega) i
