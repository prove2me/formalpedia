-- Prove2me | solution 1 for ChanceDetEquiv.PModel.backward_39a
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:27:23.08841+00:00
-- url     : https://prove2.me/submissions/5cac8d4a-3699-4010-9245-eed5193036d2

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
    (p : Point39 m n) (hp : p ∈ feasible39 d) (ht : 0 < p.2.2.2.2) :
    backward p ∈ feasible38 d ∧ value38 (backward p) = value39 p := by
  obtain ⟨Db, v, v0, w0, t⟩ := p
  obtain ⟨g1, g2, g3, g4, g5⟩ := hp
  simp only at g1 g2 g3 g4 g5 ht
  have hs : 0 < t⁻¹ := inv_pos.mpr ht
  have hst : t⁻¹ * t = 1 := inv_mul_cancel₀ ht.ne'
  have hback : t • (t⁻¹ • Db) = Db := by rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hV : V d (t⁻¹ • Db) = t⁻¹ ^ 2 * Vbar d Db t := by
    have := cdl_Vbar d t (t⁻¹ • Db)
    rw [hback] at this
    rw [this]; field_simp
  have hmu : ∀ i, muRow d i (t⁻¹ • Db) = t⁻¹ * muBar d i Db t := by
    intro i
    have := cdl_muBar d i t (t⁻¹ • Db)
    rw [hback] at this
    rw [this]; field_simp
  have hsg : ∀ i, sigmaSq d i (t⁻¹ • Db) = t⁻¹ ^ 2 * sigmaBarSq d i Db t := by
    intro i
    have := cdl_sigma d i t (t⁻¹ • Db)
    rw [hback] at this
    rw [this]; field_simp
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · show meanObjective d (t⁻¹ • Db) - t⁻¹ * v0 ≥ d.z0
      rw [cdl_meanObj]
      have h := mul_le_mul_of_nonneg_left g1 hs.le
      have e : t⁻¹ * (t * d.z0) = d.z0 := by field_simp
      rw [e] at h
      linarith
    · show -V d (t⁻¹ • Db) + (t⁻¹) ^ 2 ≥ 0
      rw [hV]
      subst g4
      nlinarith [mul_le_mul_of_nonneg_left g2 (sq_nonneg t⁻¹)]
    · intro i
      obtain ⟨a1, a2, a3⟩ := g3 i
      refine ⟨?_, ?_, ?_⟩
      · show muRow d i (t⁻¹ • Db) - t⁻¹ * v i ≥ 0
        rw [hmu]
        nlinarith [mul_le_mul_of_nonneg_left a1 hs.le]
      · show -(K d i ^ 2) * sigmaSq d i (t⁻¹ • Db) + K d i ^ 2 * muRow d i (t⁻¹ • Db) ^ 2 +
          (t⁻¹ * v i) ^ 2 ≥ 0
        rw [hsg, hmu]
        nlinarith [mul_le_mul_of_nonneg_left a2 (sq_nonneg t⁻¹)]
      · show 0 ≤ t⁻¹ * v i
        exact mul_nonneg hs.le a3
    · exact hs
  · show t⁻¹ * v0 / t⁻¹ = v0
    field_simp
