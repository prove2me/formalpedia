-- Prove2me | solution 1 for Formalism.REAL.polar_log_anticommutes_signature
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:14:34.526602+00:00
-- url     : https://prove2.me/submissions/2ca4e501-ab02-4f2c-9ecc-2a1caa7d2242

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Theorems.Thm_Formalism_REAL_exp_signature_conj
import Theorems.Thm_Formalism_REAL_exp_injective_hermitian
import Theorems.Thm_Formalism_REAL_matrix_exp_neg_mul_exp
import Theorems.Thm_Formalism_REAL_eq_of_add_self_eq_add_self
import Theorems.Thm_Formalism_REAL_indefinite_unitary_preserves_form
import Theorems.Thm_Formalism_REAL_polar_log_hermitian
import Theorems.Thm_Formalism_REAL_exp_polarLog_double
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Formalism.REAL
variable {n : ℕ}
private lemma Jm_mul_Jm_eq_one (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> norm_num
private lemma Jm_conjTranspose_eq_self (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp
end Formalism.REAL
end
end

set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open Formalism Formalism.REAL
variable {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Jm ε * polarLog g * Jm ε = -polarLog g := by
  set L := polarLog g with hL
  have hH : Lᴴ = L := polar_log_hermitian g
  have hP : NormedSpace.exp (L + L) = gᴴ * g := exp_polarLog_double hg
  have hgJ : g * Jm ε * gᴴ = Jm ε := (indefinite_unitary_preserves_form hg).1
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hX : (Jm ε * (gᴴ * g) * Jm ε) * (gᴴ * g) = 1 := by
    calc (Jm ε * (gᴴ * g) * Jm ε) * (gᴴ * g) = Jm ε * gᴴ * (g * Jm ε * gᴴ) * g := by
          simp only [mul_assoc]
      _ = Jm ε * (gᴴ * Jm ε * g) := by rw [hgJ]; simp only [mul_assoc]
      _ = 1 := by rw [hg', Jm_mul_Jm_eq_one]
  have hE : NormedSpace.exp (-(L + L)) = Jm ε * (gᴴ * g) * Jm ε := by
    have h0 : NormedSpace.exp (-(L + L)) * (gᴴ * g) = 1 := by
      rw [← hP]
      exact matrix_exp_neg_mul_exp _
    have h2 : (gᴴ * g) * (Jm ε * (gᴴ * g) * Jm ε) = 1 := by
      have h1 := hX
      first
      | exact mul_eq_one_comm.mp h1
      | exact (Matrix.mul_eq_one_comm).mp h1
      | exact Matrix.mul_eq_one_comm.1 h1
    calc NormedSpace.exp (-(L + L))
        = NormedSpace.exp (-(L + L)) * ((gᴴ * g) * (Jm ε * (gᴴ * g) * Jm ε)) := by rw [h2, mul_one]
      _ = Jm ε * (gᴴ * g) * Jm ε := by rw [← mul_assoc, h0, one_mul]
  have hA : (Jm ε * (L + L) * Jm ε)ᴴ = Jm ε * (L + L) * Jm ε := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTranspose_eq_self, Matrix.conjTranspose_add, hH,
      mul_assoc]
  have hB : (-(L + L))ᴴ = -(L + L) := by
    rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_add, hH]
  have hEq : Jm ε * (L + L) * Jm ε = -(L + L) :=
    exp_injective_hermitian hA hB (by rw [exp_signature_conj, hP, hE])
  apply eq_of_add_self_eq_add_self
  rw [← neg_add, ← hEq]
  simp only [mul_add, add_mul]
end Formalism.REAL
