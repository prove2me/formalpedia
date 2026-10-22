-- Prove2me | solution 2 for GaussianMatrix.pinv_spectral_expectation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:38:03.934914+00:00
-- url     : https://prove2.me/submissions/9c4f3cb8-9c94-4d9a-aa12-9ec30281a663
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_integral_le_of_tail_bound
import Theorems.Thm_GaussianMatrix_specNorm_pinvR_sq
import Theorems.Thm_GaussianMatrix_specNorm_inv_gram_eq
import Theorems.Thm_GaussianMatrix_pinv_spectral_tail
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator
open GaussianMatrix
instance Matrix.measureSpaceOfPi {m n : Type*} : MeasurableSpace (Matrix m n ℝ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℝ))
instance Matrix.opensMeasureSpaceOfPi {m n : Type*} [Countable m] [Countable n] :
    OpensMeasurableSpace (Matrix m n ℝ) :=
  inferInstanceAs (OpensMeasurableSpace (m → n → ℝ))
theorem measurable_inv_gram_entry {r k : ℕ} (a b : Fin r) :
    Measurable (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ a b) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  have hc : Continuous (fun G : Fin r → Fin k → ℝ => Matrix.of G * (Matrix.of G)ᵀ) := by
    fun_prop
  refine Measurable.mul ?_ ?_
  · exact (hc.matrix_det.measurable).inv
  · exact ((hc.matrix_adjugate).matrix_elem a b).measurable

theorem measurable_specNorm_pinvR_aux {r k : ℕ} :
    Measurable (fun G : Fin r → Fin k → ℝ => pinvR (Matrix.of G)) := by
  refine measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun i => ?_
  simp only [pinvR, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun a _ => ?_
  refine Measurable.mul ?_ (measurable_inv_gram_entry a i)
  exact (measurable_pi_apply a).eval
theorem measurable_specNorm_pinvR {r k : ℕ} :
    Measurable (fun G : Fin r → Fin k → ℝ => specNorm (pinvR (Matrix.of G))) := by
  have h2 : Continuous (fun M : Matrix (Fin k) (Fin r) ℝ => ‖M‖) := continuous_norm
  exact h2.measurable.comp measurable_specNorm_pinvR_aux
theorem solution {r k : ℕ} (hr : 2 ≤ r) (hrk : r + 1 ≤ k) :
    Integrable (fun G : Fin r → Fin k → ℝ => specNorm (pinvR (Matrix.of G))) (gaussianMatrix r k) ∧
    ∫ G, specNorm (pinvR (Matrix.of G)) ∂(gaussianMatrix r k)
      ≤ Real.exp 1 * Real.sqrt k / ((k : ℝ) - r) := by
  have hprob : IsProbabilityMeasure (gaussianMatrix r k) := inferInstance
  have hmeas : Measurable (fun G : Fin r → Fin k → ℝ => specNorm (pinvR (Matrix.of G))) :=
    measurable_specNorm_pinvR
  have hae : AEMeasurable (fun G : Fin r → Fin k → ℝ => specNorm (pinvR (Matrix.of G))) (gaussianMatrix r k) :=
    hmeas.aemeasurable
  have hnn : 0 ≤ᵐ[gaussianMatrix r k] (fun G : Fin r → Fin k → ℝ => specNorm (pinvR (Matrix.of G))) := by
    filter_upwards with G
    exact norm_nonneg _
  set m : ℝ := (k : ℝ) - r + 1 with hm_def
  have hm : 1 < m := by
    rw [hm_def]
    have hrk' : (r : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hrk
    linarith
  have hm_pos : 0 < m := by linarith [hm]
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hBpos : (0 : ℝ) < Real.exp 1 * Real.sqrt k / m := by
    apply div_pos _ hm_pos
    apply mul_pos (Real.exp_pos 1)
    exact Real.sqrt_pos.mpr hk_pos
  have h2pim_pos : (0 : ℝ) < 2 * Real.pi * m := by
    apply mul_pos
    apply mul_pos
    · norm_num
    · exact Real.pi_pos
    · exact hm_pos
  set C : ℝ := (1 / Real.sqrt (2 * Real.pi * m)) * (Real.exp 1 * Real.sqrt k / m) ^ m with hC_def
  have hC : 0 < C := by
    rw [hC_def]
    apply mul_pos
    · apply one_div_pos.mpr
      exact Real.sqrt_pos.mpr h2pim_pos
    · exact Real.rpow_pos_of_pos hBpos m
  have htail : ∀ t : ℝ, 0 < t → (gaussianMatrix r k) {G | t < specNorm (pinvR (Matrix.of G))}
      ≤ ENNReal.ofReal (C * t ^ (-m)) := by
    intro t ht
    -- the Chen--Dongarra tail bound `pinv_spectral_tail`, re-expressed with
    -- `m = k - r + 1` and `C = (1/sqrt(2*pi*m)) * (e*sqrt(k)/m)^m`
    have hrk' : r ≤ k := by omega
    have hpt := pinv_spectral_tail hr hrk' t ht
    have hNm : m = (k : ℝ) - r + 1 := by rw [hm_def]
    have hNm2 : (k : ℝ) - r + 1 = m := hNm.symm
    rw [hNm2] at hpt
    have hCeq : (1 / Real.sqrt (2 * Real.pi * ((k : ℝ) - r + 1)))
          * (Real.exp 1 * Real.sqrt k / ((k : ℝ) - r + 1)) ^ ((k : ℝ) - r + 1)
          = C := by
      rw [hC_def, hm_def]
    rw [hCeq] at hpt
    exact hpt
  have hbound := integral_le_of_tail_bound (gaussianMatrix r k)
    (fun G : Fin r → Fin k → ℝ => specNorm (pinvR (Matrix.of G))) hae hnn C m hC hm htail
  refine ⟨hbound.1, ?_⟩
  have hm1 : m - 1 = (k : ℝ) - r := by rw [hm_def]; ring
  have hB : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt k / m := hBpos.le
  have h1x0 : (0 : ℝ) ≤ 1 / Real.sqrt (2 * Real.pi * m) := by
    apply one_div_nonneg.mpr
    exact Real.sqrt_nonneg _
  have hsplit : C ^ (1 / m)
      = (1 / Real.sqrt (2 * Real.pi * m)) ^ (1 / m)
        * ((Real.exp 1 * Real.sqrt k / m) ^ m) ^ (1 / m) := by
    rw [hC_def]
    exact Real.mul_rpow h1x0 (Real.rpow_nonneg hB m)
  have htower : ((Real.exp 1 * Real.sqrt k / m) ^ m) ^ (1 / m)
      = Real.exp 1 * Real.sqrt k / m := by
    rw [← Real.rpow_mul hB]
    have e : m * (1 / m) = 1 := by rw [mul_one_div, div_self (ne_of_gt hm_pos)]
    rw [e, Real.rpow_one]
  have hfirst : (1 / Real.sqrt (2 * Real.pi * m)) ^ (1 / m) ≤ 1 := by
    have hsq1 : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * m) := by
      have h1m : (1 : ℝ) ≤ 2 * Real.pi * m := by
        have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
        have hm1le : (1 : ℝ) ≤ m := by linarith [hm]
        nlinarith [hpi3, hm1le]
      calc (1 : ℝ) = Real.sqrt 1 := by rw [Real.sqrt_one]
        _ ≤ Real.sqrt (2 * Real.pi * m) := Real.sqrt_le_sqrt h1m
    have h1x1 : 1 / Real.sqrt (2 * Real.pi * m) ≤ 1 := by
      rw [div_le_one (Real.sqrt_pos.mpr h2pim_pos)]
      exact hsq1
    calc (1 / Real.sqrt (2 * Real.pi * m)) ^ (1 / m)
        ≤ (1 : ℝ) ^ (1 / m) := by
          apply Real.rpow_le_rpow h1x0 h1x1
          exact div_nonneg zero_le_one hm_pos.le
      _ = 1 := Real.one_rpow _
  have hfactor : C ^ (1 / m) ≤ Real.exp 1 * Real.sqrt k / m := by
    rw [hsplit, htower]
    have h := mul_le_mul_of_nonneg_right hfirst hB
    rwa [one_mul] at h
  have hstep : C ^ (1 / m) * m / (m - 1)
      ≤ (Real.exp 1 * Real.sqrt k / m) * m / (m - 1) := by
    simp only [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (by linarith [hm] : (0 : ℝ) ≤ m - 1))
    exact mul_le_mul_of_nonneg_right hfactor hm_pos.le
  have heq : (Real.exp 1 * Real.sqrt k / m) * m / (m - 1)
      = Real.exp 1 * Real.sqrt k / ((k : ℝ) - r) := by
    rw [hm1]
    field_simp
  calc ∫ G, specNorm (pinvR (Matrix.of G)) ∂(gaussianMatrix r k)
      ≤ C ^ (1 / m) * m / (m - 1) := hbound.2
    _ ≤ (Real.exp 1 * Real.sqrt k / m) * m / (m - 1) := hstep
    _ = Real.exp 1 * Real.sqrt k / ((k : ℝ) - r) := heq
