-- Prove2me | solution 1 for EntanglingOps.BinaryPhase.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T03:17:01.023852+00:00
-- url     : https://prove2.me/submissions/179121e3-66b7-4602-ba79-0f3d3c067155

import Mathlib
import Definitions.Def_EntanglingOps_BinaryPhase_Model

open Matrix
open scoped Kronecker
open EntanglingOps.BinaryPhase

lemma sqrt_inv_four (d : ℕ) :
    ((Real.sqrt d : ℂ))⁻¹ * ((Real.sqrt d : ℂ))⁻¹ * (((Real.sqrt d : ℂ))⁻¹ * ((Real.sqrt d : ℂ))⁻¹) =
      ((d : ℂ) ^ 2)⁻¹ := by
  have h : (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = d := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]; simp
  rw [← mul_inv, ← mul_inv, h]; ring

lemma projPhiPair_apply (d : ℕ) (u v u' v' : Fin d × Fin d) :
    projPhiPair d (u, v) (u', v') = if u = v ∧ u' = v' then ((d : ℂ) ^ 2)⁻¹ else 0 := by
  obtain ⟨a2, b2⟩ := u
  obtain ⟨a3, b3⟩ := v
  obtain ⟨a2', b2'⟩ := u'
  obtain ⟨a3', b3'⟩ := v'
  simp only [projPhiPair, regroup, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.prodProdProdComm_symm, Equiv.prodProdProdComm_apply, Matrix.kroneckerMap_apply,
    projPhi, vecMulVec_apply, Pi.star_apply, phiVec, Prod.mk.injEq]
  by_cases h1 : a2 = a3 <;> by_cases h2 : b2 = b3 <;> by_cases h3 : a2' = a3' <;>
    by_cases h4 : b2' = b3' <;> simp [h1, h2, h3, h4, Complex.conj_ofReal]
  exact sqrt_inv_four d

theorem solution (d : ℕ) (hd : 0 < d) (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    ((d : ℂ) ^ 2) • WildeQIT.partialTraceRight
      (((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ ρ) * projPhiPair d) = ρᵀ := by
  ext i j
  simp only [WildeQIT.partialTraceRight, Matrix.smul_apply, Matrix.of_apply, Matrix.mul_apply]
  rw [Fintype.sum_eq_single j (fun k hk => Finset.sum_eq_zero (fun m _ => by
    obtain ⟨m1, m2⟩ := m
    rw [projPhiPair_apply, if_neg (by tauto), mul_zero]))]
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single i (fun m1 hm1 => Finset.sum_eq_zero (fun m2 _ => by
    rw [Matrix.kroneckerMap_apply, Matrix.one_apply, if_neg (Ne.symm hm1), zero_mul, zero_mul]))]
  rw [Fintype.sum_eq_single i (fun m2 hm2 => by
    rw [projPhiPair_apply, if_neg (by tauto), mul_zero])]
  rw [projPhiPair_apply, if_pos ⟨rfl, rfl⟩, Matrix.kroneckerMap_apply, Matrix.one_apply_eq,
    one_mul, Matrix.transpose_apply, smul_eq_mul]
  have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
