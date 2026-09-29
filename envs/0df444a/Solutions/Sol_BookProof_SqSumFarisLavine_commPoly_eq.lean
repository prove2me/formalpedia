-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.commPoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:38.613978+00:00
-- url     : https://prove2.me/submissions/d6f48b9c-4d7c-4ebb-bd6f-436917e86e52

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.commPoly_eq
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Theorems.Thm_BookProof_SqSumFarisLavine_sqSumPoly_apply
import Theorems.Thm_BookProof_SqSumFarisLavine_coreD_neg
import Theorems.Thm_BookProof_SqSumFarisLavine_pderiv_potPoly
import Theorems.Thm_BookProof_SqSumFarisLavine_pderiv_gradPoly_self
import Theorems.Thm_BookProof_SqSumFarisLavine_pderiv_harmPoly
import Theorems.Thm_BookProof_SqSumFarisLavine_pderiv_pderiv_harmPoly
import Theorems.Thm_BookProof_SqSumFarisLavine_kin_mul_comm
import Theorems.Thm_BookProof_SqSumFarisLavine_kin_kin_comm
open BookProof.SqSumFarisLavine













open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

set_option maxHeartbeats 1000000 in
theorem solution (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) (p : MvPolynomial (Fin D) ℂ) :
    commPoly kappa v p
      = ((commConst kappa v : ℝ) : ℂ) • p
        + (∑ j : Fin D, ((-(kappa j) / 2 : ℝ) : ℂ) • (X j * coreD j p))
        + (2 : ℂ) • ∑ k : Fin D, gradPoly v k * coreD k p := by

  classical
  set c : Fin D → ℂ := fun j => ((-(kappa j) / 2 : ℝ) : ℂ) with hcdef
  -- the two second-order parts, as functions of a polynomial
  have hKadd : ∀ u w : MvPolynomial (Fin D) ℂ,
      (∑ j : Fin D, c j • coreD j (coreD j (u + w)))
        = (∑ j : Fin D, c j • coreD j (coreD j u))
          + ∑ j : Fin D, c j • coreD j (coreD j w) := by
    intro u w
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [coreD_add, coreD_add, smul_add]
  have hKneg : ∀ u : MvPolynomial (Fin D) ℂ,
      (∑ j : Fin D, c j • coreD j (coreD j (-u)))
        = -∑ j : Fin D, c j • coreD j (coreD j u) := by
    intro u
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [coreD_neg, coreD_neg, smul_neg]
  have hLadd : ∀ u w : MvPolynomial (Fin D) ℂ,
      (∑ k : Fin D, coreD k (coreD k (u + w)))
        = (∑ k : Fin D, coreD k (coreD k u)) + ∑ k : Fin D, coreD k (coreD k w) := by
    intro u w
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [coreD_add, coreD_add]
  -- the harmonic commutator
  have gKW : (∑ j : Fin D, c j • coreD j (coreD j (harmPoly * p)))
        - harmPoly * ∑ j : Fin D, c j • coreD j (coreD j p)
      = (∑ j : Fin D, c j * (1 / 2 : ℂ)) • p
        + ∑ j : Fin D, c j • (X j * coreD j p) := by
    rw [kin_mul_comm c harmPoly p, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h2mul : (2 : ℂ) • (C (1 / 2 : ℂ) * X j * coreD j p) = X j * coreD j p := by
      rw [MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← mul_assoc, ← map_mul]
      norm_num
    rw [pderiv_pderiv_harmPoly, pderiv_harmPoly, h2mul, smul_add,
      ← MvPolynomial.smul_eq_C_mul, smul_smul]
  -- the potential commutator
  have gLV : (∑ k : Fin D, coreD k (coreD k (potPoly v * p)))
        - potPoly v * ∑ k : Fin D, coreD k (coreD k p)
      = ((∑ k : Fin D, ((∑ r : R, (v r k) ^ 2 : ℝ) : ℂ))) • p
        + (2 : ℂ) • ∑ k : Fin D, gradPoly v k * coreD k p := by
    have h1 := kin_mul_comm (fun _ => (1 : ℂ)) (potPoly v) p
    simp only [one_smul] at h1
    rw [h1, Finset.sum_smul, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pderiv_potPoly, pderiv_gradPoly_self, ← MvPolynomial.smul_eq_C_mul]
  -- the two Laplacians commute
  have gKL := kin_kin_comm c p
  -- assemble
  have hcp : commPoly kappa v p
      = ((∑ j : Fin D, c j • coreD j (coreD j (harmPoly * p)))
          - harmPoly * ∑ j : Fin D, c j • coreD j (coreD j p))
        + ((∑ k : Fin D, coreD k (coreD k (potPoly v * p)))
          - potPoly v * ∑ k : Fin D, coreD k (coreD k p)) := by
    rw [commPoly, sqSumPoly_apply, sqSumPoly_apply, harmP, harmP, kinPoly, kinPoly, kinPart,
      kinPart, hKadd, hKneg, hLadd]
    rw [← gKL]
    ring
  rw [hcp, gKW, gLV]
  have hconst : ((commConst kappa v : ℝ) : ℂ)
      = (∑ j : Fin D, c j * (1 / 2 : ℂ)) + ∑ k : Fin D, ((∑ r : R, (v r k) ^ 2 : ℝ) : ℂ) := by
    rw [commConst, hcdef]
    push_cast
    rw [Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_comm
  rw [hconst, add_smul]
  abel
