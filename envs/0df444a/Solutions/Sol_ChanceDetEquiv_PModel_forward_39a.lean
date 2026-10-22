-- Prove2me | solution 1 for ChanceDetEquiv.PModel.forward_39a
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:26:53.246345+00:00
-- url     : https://prove2.me/submissions/f2227a66-b1bb-475a-9ba7-f13d14068c78

import Mathlib
import Definitions.Def_ChanceDetEquiv_PModel_Model

set_option autoImplicit false
open MeasureTheory
open ChanceDetEquiv.PModel

section CDLib
variable {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}

lemma cdl_meanObj (d : Model Ω m n) (t : ℝ) (D : Matrix (Fin n) (Fin m) ℝ) :
    meanObjective d (t • D) = t * meanObjective d D := by
  unfold meanObjective
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.smul_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma cdl_Vbar (d : Model Ω m n) (t : ℝ) (D : Matrix (Fin n) (Fin m) ℝ) :
    Vbar d (t • D) t = t ^ 2 * V d D := by
  unfold Vbar V
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  have : (∑ j : Fin n, d.c ω j * (t * D.mulVec (d.b ω) j)) = t * ∑ j : Fin n, d.c ω j * D.mulVec (d.b ω) j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [this]; ring

lemma cdl_muBar (d : Model Ω m n) (i : Fin m) (t : ℝ) (D : Matrix (Fin n) (Fin m) ℝ) :
    muBar d i (t • D) t = t * muRow d i D := by
  unfold muBar muRow
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma cdl_sigma (d : Model Ω m n) (i : Fin m) (t : ℝ) (D : Matrix (Fin n) (Fin m) ℝ) :
    sigmaBarSq d i (t • D) t = t ^ 2 * sigmaSq d i D := by
  unfold sigmaBarSq sigmaSq rowResidual
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  ring

end CDLib

theorem solution {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) [IsProbabilityMeasure d.P]
    (hm : 0 < m) (hn : 0 < n)
    (hMoments : MomentAssumptions d) (hNormal : NormalRows d)
    (hConfidence : Confidence d)
    (p : Point38 m n) (hp : p ∈ feasible38 d) :
    forward p ∈ feasible39 d ∧ value39 (forward p) = value38 p := by
  obtain ⟨D, v, v0, w0⟩ := p
  obtain ⟨h1, h2, h3, h4⟩ := hp
  simp only at h1 h2 h3 h4
  have ht : 0 < 1 / w0 := by positivity
  have htw : 1 / w0 * w0 = 1 := by field_simp
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show meanObjective d ((1 / w0) • D) - 1 / w0 * v0 ≥ 1 / w0 * d.z0
      rw [cdl_meanObj]
      nlinarith [mul_le_mul_of_nonneg_left h1 ht.le]
    · show -Vbar d ((1 / w0) • D) (1 / w0) + (1 / w0 * w0) ^ 2 ≥ 0
      rw [cdl_Vbar, htw]
      nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg (1 / w0)), mul_self_nonneg (1 / w0), htw]
    · intro i
      obtain ⟨a1, a2, a3⟩ := h3 i
      refine ⟨?_, ?_, ?_⟩
      · show muBar d i ((1 / w0) • D) (1 / w0) - (1 / w0) * v i ≥ 0
        rw [cdl_muBar]
        nlinarith [mul_le_mul_of_nonneg_left a1 ht.le]
      · show -(K d i ^ 2) * sigmaBarSq d i ((1 / w0) • D) (1 / w0) +
          K d i ^ 2 * muBar d i ((1 / w0) • D) (1 / w0) ^ 2 + ((1 / w0) * v i) ^ 2 ≥ 0
        rw [cdl_sigma, cdl_muBar]
        nlinarith [mul_le_mul_of_nonneg_left a2 (sq_nonneg (1 / w0))]
      · show 0 ≤ (1 / w0) * v i
        exact mul_nonneg ht.le a3
    · exact htw
    · exact ht.le
  · show 1 / w0 * v0 = v0 / w0
    ring
