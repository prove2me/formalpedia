-- Prove2me | solution 1 for Formalism.L2.DIV.trace_inv_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:21.478802+00:00
-- url     : https://prove2.me/submissions/4ab69a5f-232d-4feb-94ee-86c8ba9a59e6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℂ) {N : ℕ} (hN : N ≠ 0)
    (hB : B ^ N = 1) (hC : C * B = 1) : C.trace = starRingEnd ℂ B.trace := by
  set H : Matrix (Fin n) (Fin n) ℂ := ∑ k ∈ Finset.range N, (B ^ k)ᴴ * B ^ k with hH
  have hshift : Bᴴ * H * B = H := by
    rw [hH, Finset.mul_sum, Finset.sum_mul]
    have : ∀ k, Bᴴ * ((B ^ k)ᴴ * B ^ k) * B = (B ^ (k + 1))ᴴ * B ^ (k + 1) := by
      intro k
      rw [pow_succ, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [Finset.sum_congr rfl fun k _ => this k]
    have h1 := Finset.sum_range_succ' (fun k => (B ^ k)ᴴ * B ^ k) N
    have h2 := Finset.sum_range_succ (fun k => (B ^ k)ᴴ * B ^ k) N
    rw [h2] at h1
    simp only [hB, pow_zero] at h1
    exact (add_right_cancel h1).symm
  have hpos : H.PosDef := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := Nat.exists_eq_succ_of_ne_zero hN
    rw [hH, Finset.sum_range_succ']
    simp only [pow_zero, Matrix.conjTranspose_one, Matrix.one_mul]
    refine Matrix.PosDef.posSemidef_add ?_ Matrix.PosDef.one
    exact Matrix.posSemidef_sum _ fun k _ => Matrix.posSemidef_conjTranspose_mul_self _
  have hu : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det _).mp hpos.isUnit
  have hCe : C = H⁻¹ * Bᴴ * H := by
    have h3 : (H⁻¹ * Bᴴ * H) * B = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Bᴴ, hshift, Matrix.nonsing_inv_mul _ hu]
    have h4 : B * C = 1 := mul_eq_one_comm.mp hC
    calc C = (H⁻¹ * Bᴴ * H) * B * C := by rw [h3, Matrix.one_mul]
      _ = H⁻¹ * Bᴴ * H := by rw [Matrix.mul_assoc _ B C, h4, Matrix.mul_one]
  rw [hCe, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul,
    Matrix.trace_conjTranspose]
  rfl
end Formalism.L2.DIV
