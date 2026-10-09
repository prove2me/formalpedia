-- Prove2me | solution 1 for GaussianMatrix.inverse_wishart_mean
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:42:54.303741+00:00
-- url     : https://prove2.me/submissions/b04a6e03-3e8b-425b-9ad6-76ec2f3ab371

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_rotation_invariance
import Theorems.Thm_GaussianMatrix_full_rank_ae
import Theorems.Thm_GaussianMatrix_schur_diag_inv
import Theorems.Thm_GaussianMatrix_residual_law
import Theorems.Thm_GaussianMatrix_inv_chi_square_moment

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

lemma iwm_measurable_inv_entry {r k : ℕ} (i j : Fin r) :
    Measurable (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j) := by
  have hc : Continuous (fun G : Fin r → Fin k → ℝ => Matrix.of G * (Matrix.of G)ᵀ) :=
    Continuous.matrix_mul continuous_id (Continuous.matrix_transpose continuous_id)
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (hc.matrix_det.measurable.inv).mul (hc.matrix_adjugate.matrix_elem i j).measurable

lemma iwm_det_ne_zero_of_rank {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (h : M.rank = n) :
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

lemma iwm_psd_inv {r k : ℕ} (G : Fin r → Fin k → ℝ) :
    ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹).PosSemidef := by
  have := Matrix.posSemidef_self_mul_conjTranspose (Matrix.of G)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  exact this.inv

lemma iwm_psd_offdiag {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ) (hM : M.PosSemidef) (i j : Fin r) :
    |M i j| ≤ M i i + M j j := by
  have hs : M j i = M i j := by
    have := hM.isHermitian.apply i j
    simpa using this
  by_cases hij : i = j
  · subst hij
    have := hM.diag_nonneg (i := i)
    rw [abs_of_nonneg this]; linarith
  have h1 := hM.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have h2 := hM.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, dotProduct_add,
    sub_dotProduct, dotProduct_sub, Matrix.mulVec_single, single_dotProduct,
    hs] at h1 h2
  rw [abs_le]; constructor <;> linarith

lemma iwm_offdiag_integral {r k : ℕ} (i j : Fin r) (hij : i ≠ j) :
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ∂(gaussianMatrix r k) = 0 := by
  classical
  set D : Matrix (Fin r) (Fin r) ℝ := Matrix.diagonal fun a => if a = i then -1 else 1 with hD
  have hDD : D * D = 1 := by
    rw [hD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; split_ifs <;> norm_num
  have hDt : Dᵀ = D := Matrix.diagonal_transpose _
  have hU : Dᵀ * D = 1 := by rw [hDt, hDD]
  have hrot := rotation_invariance D (1 : Matrix (Fin k) (Fin k) ℝ) hU (by simp)
  have hmeas : Measurable (fun G : Fin r → Fin k → ℝ => Matrix.of.symm (D * Matrix.of G * (1 : Matrix (Fin k) (Fin k) ℝ))) := by
    refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    simp only [Matrix.of_symm_apply, Matrix.mul_one, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have hDinv : D⁻¹ = D := Matrix.inv_eq_left_inv hDD
  have key : ∀ G : Fin r → Fin k → ℝ,
      (Matrix.of (Matrix.of.symm (D * Matrix.of G * (1 : Matrix (Fin k) (Fin k) ℝ))) *
        (Matrix.of (Matrix.of.symm (D * Matrix.of G * (1 : Matrix (Fin k) (Fin k) ℝ))))ᵀ)⁻¹ i j
        = -(Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j := by
    intro G
    simp only [Equiv.apply_symm_apply, Matrix.mul_one, Matrix.transpose_mul, hDt]
    rw [show D * Matrix.of G * ((Matrix.of G)ᵀ * D) = D * (Matrix.of G * (Matrix.of G)ᵀ) * D by
      simp [Matrix.mul_assoc]]
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hDinv, hD]
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Ne.symm hij]
  have h1 : ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ∂(gaussianMatrix r k) =
      ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j
        ∂(Measure.map (fun G => Matrix.of.symm (D * Matrix.of G * (1 : Matrix (Fin k) (Fin k) ℝ))) (gaussianMatrix r k)) := by
    rw [hrot]
  rw [integral_map hmeas.aemeasurable (iwm_measurable_inv_entry i j).aestronglyMeasurable] at h1
  simp_rw [key, integral_neg] at h1
  linarith

lemma iwm_resid_moment {n k : ℕ} (hnk : n + 3 ≤ k) (H : Matrix (Fin n) (Fin k) ℝ)
    (hH : H.rank = n) :
    Integrable (fun g : Fin k → ℝ => (g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))⁻¹)
        (Measure.pi fun _ : Fin k => gaussianReal 0 1) ∧
    ∫ g, (g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))⁻¹
        ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1) = 1 / ((k : ℝ) - n - 2) := by
  have hq : Measurable (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g))) := by
    apply Continuous.measurable
    fun_prop
  have hlaw := residual_law H hH
  obtain ⟨hint, hval⟩ := inv_chi_square_moment (d := k - n) (by omega)
  have hφ : Measurable (fun s : ℝ => s⁻¹) := measurable_inv
  have hS : Measurable (fun x : Fin (k - n) → ℝ => ∑ j, x j ^ 2) := by fun_prop
  constructor
  · have h := (integrable_map_measure hφ.aestronglyMeasurable hS.aemeasurable).mpr hint
    rw [← hlaw] at h
    exact (integrable_map_measure hφ.aestronglyMeasurable hq.aemeasurable).mp h
  · rw [← integral_map hq.aemeasurable hφ.aestronglyMeasurable, hlaw,
      integral_map hS.aemeasurable hφ.aestronglyMeasurable, hval,
      Nat.cast_sub (by omega : n ≤ k)]

lemma iwm_diag {n k : ℕ} (hnk : n + 3 ≤ k) (i : Fin (n + 1)) :
    Integrable (fun G : Fin (n + 1) → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i)
        (gaussianMatrix (n + 1) k) ∧
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ∂(gaussianMatrix (n + 1) k)
      = 1 / ((k : ℝ) - n - 2) := by
  set μ : Measure (Fin k → ℝ) := Measure.pi fun _ : Fin k => gaussianReal 0 1 with hμ
  set ν : Measure (Fin n → Fin k → ℝ) := Measure.pi fun _ : Fin n => μ with hν
  set F : (Fin (n + 1) → Fin k → ℝ) → ℝ := fun G => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i with hF
  have hFm : Measurable F := iwm_measurable_inv_entry i i
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin k → ℝ) i with he
  have hmp : MeasurePreserving e (gaussianMatrix (n + 1) k) (μ.prod ν) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  set Φ : (Fin k → ℝ) × (Fin n → Fin k → ℝ) → ℝ := fun p => F (e.symm p) with hΦ
  have hΦm : Measurable Φ := hFm.comp e.symm.measurable
  have hΦnn : ∀ p, 0 ≤ Φ p := fun p => (iwm_psd_inv _).diag_nonneg
  -- on the full-rank event, the inner integrand is the inverse residual
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
      exact iwm_det_ne_zero_of_rank _ (by rw [Matrix.rank_self_mul_transpose, hH])
    have := schur_diag_inv (Matrix.of G0) i hdet
    rw [hsub, hrow] at this
    simp only [hΦ, hF, he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    exact this
  have hrank : ∀ᵐ H ∂ν, (Matrix.of H).rank = n := by
    have := full_rank_ae n k
    filter_upwards [this] with H hH
    rw [hH]; omega
  have hinner : ∀ᵐ H ∂ν, Integrable (fun g => Φ (g, H)) μ ∧
      ∫ g, Φ (g, H) ∂μ = 1 / ((k : ℝ) - n - 2) := by
    filter_upwards [hrank] with H hH
    simp_rw [hschur H hH]
    exact iwm_resid_moment hnk (Matrix.of H) hH
  have hint : Integrable Φ (μ.prod ν) := by
    rw [integrable_prod_iff' hΦm.aestronglyMeasurable]
    refine ⟨hinner.mono fun H h => h.1, ?_⟩
    refine (integrable_const (1 / ((k : ℝ) - n - 2))).congr ?_
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

theorem solution {r k : ℕ} (hrk : r + 2 ≤ k) :
    (∀ i j : Fin r, Integrable (fun G : Fin r → Fin k → ℝ =>
        (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j) (gaussianMatrix r k)) ∧
    ∀ i j : Fin r, ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ∂(gaussianMatrix r k)
      = (1 / ((k : ℝ) - r - 1)) * (1 : Matrix (Fin r) (Fin r) ℝ) i j := by
  have hdiag : ∀ i : Fin r, Integrable (fun G : Fin r → Fin k → ℝ =>
      (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i) (gaussianMatrix r k) := by
    intro i
    cases r with
    | zero => exact i.elim0
    | succ n => exact (iwm_diag (by omega) i).1
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · refine Integrable.mono' ((hdiag i).add (hdiag j))
      (iwm_measurable_inv_entry i j).aestronglyMeasurable (Filter.Eventually.of_forall fun G => ?_)
    rw [Real.norm_eq_abs]
    exact iwm_psd_offdiag _ (iwm_psd_inv G) i j
  · by_cases hij : i = j
    · subst hij
      cases r with
      | zero => exact i.elim0
      | succ n =>
        rw [(iwm_diag (by omega) i).2, Matrix.one_apply_eq, mul_one]
        push_cast
        ring_nf
    · rw [iwm_offdiag_integral i j hij, Matrix.one_apply_ne hij, mul_zero]
