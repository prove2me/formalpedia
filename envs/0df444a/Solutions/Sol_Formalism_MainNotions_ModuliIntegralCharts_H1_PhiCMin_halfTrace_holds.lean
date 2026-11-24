-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.halfTrace_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:06:47.138228+00:00
-- url     : https://prove2.me/submissions/59f46d3b-61dd-418a-9516-d3ee028c1e4e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinE
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_bessel2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
open Matrix
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
theorem _root_.solution : HalfTraceStatement := by
  intro d L G K R hLR hR hG hKG hKL hK x
  have hRi : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR
  have hiR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hR
  have hRt : Rᵀ * (R⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, hiR, Matrix.transpose_one]
  have htR : (R⁻¹)ᵀ * Rᵀ = 1 := by rw [← Matrix.transpose_mul, hRi, Matrix.transpose_one]

  have hCpsd : (R * G * Rᵀ).PosSemidef := by
    have := hG.mul_mul_conjTranspose_same R
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hCtr : trace (R * G * Rᵀ) = trace (L * G) := by
    rw [Matrix.trace_mul_cycle, hLR]
  have hJ' : (R⁻¹)ᵀ * K * Rᵀ = -(R * Kᵀ * R⁻¹) := by
    have h2 : (R⁻¹)ᵀ * (K * L) * R⁻¹ = (R⁻¹)ᵀ * (-(L * Kᵀ)) * R⁻¹ := by rw [hKL]
    rw [hLR] at h2
    have e1 : (R⁻¹)ᵀ * (K * (Rᵀ * R)) * R⁻¹ = (R⁻¹)ᵀ * K * Rᵀ := by
      simp only [Matrix.mul_assoc, hRi, Matrix.mul_one]
    have e2 : (R⁻¹)ᵀ * (-(Rᵀ * R * Kᵀ)) * R⁻¹ = -(R * Kᵀ * R⁻¹) := by
      rw [Matrix.mul_neg, Matrix.neg_mul]
      congr 1
      simp only [← Matrix.mul_assoc, htR, Matrix.one_mul]
    rw [← e1, h2, e2]
  have hJskew : ((R⁻¹)ᵀ * K * Rᵀ)ᵀ = -((R⁻¹)ᵀ * K * Rᵀ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose, hJ', neg_neg, Matrix.mul_assoc]
  have hCJ : (R * G * Rᵀ) * ((R⁻¹)ᵀ * K * Rᵀ) = ((R⁻¹)ᵀ * K * Rᵀ) * (R * G * Rᵀ) := by
    have l1 : (R * G * Rᵀ) * ((R⁻¹)ᵀ * K * Rᵀ) = R * (G * K) * Rᵀ := by
      calc (R * G * Rᵀ) * ((R⁻¹)ᵀ * K * Rᵀ) = R * G * (Rᵀ * (R⁻¹)ᵀ) * K * Rᵀ := by
            simp only [Matrix.mul_assoc]
        _ = R * (G * K) * Rᵀ := by rw [hRt, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    have l2 : ((R⁻¹)ᵀ * K * Rᵀ) * (R * G * Rᵀ) = R * (G * K) * Rᵀ := by
      calc ((R⁻¹)ᵀ * K * Rᵀ) * (R * G * Rᵀ) = (R⁻¹)ᵀ * (K * (Rᵀ * R)) * G * Rᵀ := by
            simp only [Matrix.mul_assoc]
        _ = (R⁻¹)ᵀ * (-(Rᵀ * R * Kᵀ)) * G * Rᵀ := by rw [← hLR, hKL, hLR]
        _ = -(((R⁻¹)ᵀ * Rᵀ) * R * (Kᵀ * G) * Rᵀ) := by
            simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
        _ = R * (G * K) * Rᵀ := by
            rw [htR, hKG, Matrix.one_mul]
            simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [l1, l2]
  have hJdet : IsUnit ((R⁻¹)ᵀ * K * Rᵀ).det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose]
    exact ((Matrix.isUnit_nonsing_inv_det R hR).mul hK).mul hR
  set C := R * G * Rᵀ with hCdef
  set J := (R⁻¹)ᵀ * K * Rᵀ with hJdef
  have hJinj : ∀ v : Fin d → ℝ, J *ᵥ v = 0 → v = 0 := by
    intro v hv
    have : (J⁻¹ * J) *ᵥ v = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    rwa [Matrix.nonsing_inv_mul J hJdet, Matrix.one_mulVec] at this
  have hH : C.IsHermitian := hCpsd.1
  have hCt : Cᵀ = C := by
    have := hH.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hsym : ∀ v w : Fin d → ℝ, (C *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (C *ᵥ w) := by
    intro v w
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hCt, dotProduct_comm]

  let ev : Fin d → (Fin d → ℝ) := fun j => ⇑(hH.eigenvectorBasis j)
  let lam : Fin d → ℝ := hH.eigenvalues
  have hCev : ∀ j, C *ᵥ ev j = lam j • ev j := fun j => hH.mulVec_eigenvectorBasis j
  have hort : ∀ i j, ev i ⬝ᵥ ev j = if j = i then 1 else 0 := by
    intro i j
    have := (orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal) j i
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    simpa [ev, star_trivial] using this
  have hinner : ∀ (v : Fin d → ℝ) j,
      inner ℝ (WithLp.toLp 2 v) (hH.eigenvectorBasis j) = ev j ⬝ᵥ v := by
    intro v j
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [ev, star_trivial]
  have hinner' : ∀ (v : Fin d → ℝ) j,
      inner ℝ (hH.eigenvectorBasis j) (WithLp.toLp 2 v) = ev j ⬝ᵥ v := by
    intro v j
    rw [real_inner_comm]; exact hinner v j
  have hquad : ∀ v : Fin d → ℝ, v ⬝ᵥ (C *ᵥ v) = ∑ j, lam j * (ev j ⬝ᵥ v) ^ 2 := by
    intro v
    have h := hH.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 v) (WithLp.toLp 2 (C *ᵥ v))
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simp only [hinner, hinner', star_trivial, WithLp.ofLp_toLp] at h
    rw [dotProduct_comm, ← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dotProduct_comm (ev j), ← hsym, hCev, smul_dotProduct, smul_eq_mul, dotProduct_comm v]
    ring
  have hpars : ∀ v : Fin d → ℝ, ∑ j, (ev j ⬝ᵥ v) ^ 2 = v ⬝ᵥ v := by
    intro v
    have h := hH.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 v) (WithLp.toLp 2 v)
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simp only [hinner, hinner', star_trivial, WithLp.ofLp_toLp] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hlam0 : ∀ j, 0 ≤ lam j := fun j => hCpsd.eigenvalues_nonneg j
  have htr : trace C = ∑ j, lam j := by simpa using hH.trace_eq_sum_eigenvalues

  have hlam : ∀ i, lam i ≤ trace C / 2 := by
    intro i
    set u := J *ᵥ ev i with hu
    have hCu : C *ᵥ u = lam i • u := by
      rw [hu, Matrix.mulVec_mulVec, hCJ, ← Matrix.mulVec_mulVec, hCev, Matrix.mulVec_smul]
    have hvu : ev i ⬝ᵥ u = 0 := by
      have h1 : ev i ⬝ᵥ u = (Jᵀ *ᵥ ev i) ⬝ᵥ ev i := by
        rw [hu, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
      rw [hJskew, Matrix.neg_mulVec, neg_dotProduct, ← hu, dotProduct_comm] at h1
      have h2 : u ⬝ᵥ ev i = 0 := by linarith
      rw [dotProduct_comm]; exact h2
    have hv1 : ev i ⬝ᵥ ev i = 1 := by rw [hort, if_pos rfl]
    have hu0 : u ≠ 0 := by
      intro h0
      have : ev i = 0 := hJinj _ (by rw [← hu, h0])
      rw [this, dotProduct_zero] at hv1
      exact zero_ne_one hv1
    have huu : 0 < u ⬝ᵥ u := by
      rcases (show 0 ≤ u ⬝ᵥ u from Finset.sum_nonneg fun k _ => mul_self_nonneg _).lt_or_eq with h | h
      · exact h
      · exact absurd (dotProduct_self_eq_zero.mp h.symm) hu0
    have hq1 : u ⬝ᵥ (C *ᵥ u) = lam i * (u ⬝ᵥ u) := by
      rw [hCu, dotProduct_smul, smul_eq_mul]
    have hq2 := hquad u
    have hsum1 : ∑ j, lam j * ((ev j ⬝ᵥ ev i) ^ 2 * (u ⬝ᵥ u)) = lam i * (u ⬝ᵥ u) := by
      simp only [hort]
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    have hbes : ∑ j, lam j * ((ev j ⬝ᵥ ev i) ^ 2 * (u ⬝ᵥ u) + (ev j ⬝ᵥ u) ^ 2) ≤
        ∑ j, lam j * (u ⬝ᵥ u) := by
      refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hlam0 j)
      exact bessel2 (ev j) (ev i) u (by rw [hort, if_pos rfl]) hv1 hvu huu
    simp only [mul_add, Finset.sum_add_distrib] at hbes
    rw [hsum1, ← hq2, hq1, ← Finset.sum_mul, ← htr] at hbes
    nlinarith

  have hcore : ∀ w : Fin d → ℝ, w ⬝ᵥ (C *ᵥ w) ≤ trace C / 2 * (w ⬝ᵥ w) := by
    intro w
    rw [hquad, ← hpars, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hlam j) (sq_nonneg _)

  have hx : x ⬝ᵥ (G *ᵥ x) = ((R⁻¹)ᵀ *ᵥ x) ⬝ᵥ (C *ᵥ ((R⁻¹)ᵀ *ᵥ x)) := by
    have e1 : C *ᵥ ((R⁻¹)ᵀ *ᵥ x) = R *ᵥ (G *ᵥ x) := by
      rw [hCdef, Matrix.mulVec_mulVec, Matrix.mul_assoc, hRt, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    rw [e1, Matrix.dotProduct_mulVec ((R⁻¹)ᵀ *ᵥ x) R, ← Matrix.mulVec_transpose,
      Matrix.mulVec_mulVec, hRt, Matrix.one_mulVec]
  rw [hx]
  have := hcore ((R⁻¹)ᵀ *ᵥ x)
  rw [hCtr] at this
  linarith
end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
