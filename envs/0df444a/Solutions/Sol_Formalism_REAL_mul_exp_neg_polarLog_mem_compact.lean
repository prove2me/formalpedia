-- Prove2me | solution 1 for Formalism.REAL.mul_exp_neg_polarLog_mem_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:29:55.006127+00:00
-- url     : https://prove2.me/submissions/f0fedbb1-62ff-42ec-a49f-17dc6e2d8113

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Theorems.Thm_Formalism_REAL_exp_signature_conj
import Theorems.Thm_Formalism_REAL_exp_conjTranspose_of_hermitian
import Theorems.Thm_Formalism_REAL_matrix_exp_neg_mul_exp
import Theorems.Thm_Formalism_REAL_matrix_exp_mul_exp_neg
import Theorems.Thm_Formalism_REAL_exp_add_self
import Theorems.Thm_Formalism_REAL_indefinite_unitary_preserves_form
import Theorems.Thm_Formalism_REAL_polar_log_hermitian
import Theorems.Thm_Formalism_REAL_exp_polarLog_double
import Theorems.Thm_Formalism_REAL_polar_log_anticommutes_signature
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
    g * NormedSpace.exp (-polarLog g) ∈ Kset ε := by
  set L := polarLog g with hL
  have hH : Lᴴ = L := polar_log_hermitian g
  have hFF : NormedSpace.exp L * NormedSpace.exp L = gᴴ * g := by
    rw [← exp_add_self]
    exact exp_polarLog_double hg
  have hEF : NormedSpace.exp (-L) * NormedSpace.exp L = 1 := matrix_exp_neg_mul_exp L
  have hFE : NormedSpace.exp L * NormedSpace.exp (-L) = 1 := matrix_exp_mul_exp_neg L
  have hEH : (NormedSpace.exp (-L))ᴴ = NormedSpace.exp (-L) :=
    exp_conjTranspose_of_hermitian (by rw [Matrix.conjTranspose_neg, hH])
  have hJE : NormedSpace.exp (-L) = Jm ε * NormedSpace.exp L * Jm ε := by
    rw [← exp_signature_conj, polar_log_anticommutes_signature hg]
  have hgJ : g * Jm ε * gᴴ = Jm ε := (indefinite_unitary_preserves_form hg).1
  unfold Kset
  rw [Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    calc star (g * NormedSpace.exp (-L)) * (g * NormedSpace.exp (-L))
        = NormedSpace.exp (-L) * (gᴴ * g) * NormedSpace.exp (-L) := by
          rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, hEH]
          simp only [mul_assoc]
      _ = 1 := by
          rw [← hFF]
          simp only [← mul_assoc]
          rw [hEF, one_mul, hFE]
  · have h4 : g * Jm ε * (NormedSpace.exp L * NormedSpace.exp L) = Jm ε * g := by
      rw [hFF, ← mul_assoc, hgJ]
    calc g * NormedSpace.exp (-L) * Jm ε = g * Jm ε * NormedSpace.exp L := by
          rw [hJE]
          simp only [mul_assoc, Jm_mul_Jm_eq_one, mul_one]
      _ = Jm ε * (g * NormedSpace.exp (-L)) := by
          rw [← mul_assoc, ← h4]
          simp only [mul_assoc]
          rw [hFE, mul_one]
end Formalism.REAL
