-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.two_coeff_two_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:11:30.632074+00:00
-- url     : https://prove2.me/submissions/92a4904a-9cd8-4519-b177-5aeac0cc904b

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_DetMulDiagonalMulEqSum
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_coeff_prod_one_add
import Theorems.Thm_Formalism_NuclearRankWeightBounds_P_moment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Matrix Polynomial Finset
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (hM : M.IsHermitian) :
    2 * (det (1 + (X : ℂ[X]) • M.map C)).coeff 2 = (trace M) ^ 2 - trace (M * M) := by
  set V : Matrix (Fin k) (Fin k) ℂ := (hM.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) with hVdef
  set L : Fin k → ℂ := RCLike.ofReal ∘ hM.eigenvalues with hLdef
  have hVV : V * Vᴴ = 1 := by
    simpa [V, star_eq_conjTranspose] using Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have hVV' : Vᴴ * V = 1 := by
    simpa [V, star_eq_conjTranspose] using Unitary.coe_star_mul_self hM.eigenvectorUnitary
  have hspec : M = V * diagonal L * Vᴴ := by
    conv_lhs => rw [hM.spectral_theorem]
    simp [V, L, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  have hMM : M * M = V * diagonal (fun a => L a * L a) * Vᴴ := by
    rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, hVV', Matrix.one_mul, ← Matrix.mul_assoc (diagonal L) (diagonal L),
      diagonal_mul_diagonal]
  have hu : powersetCard k (univ : Finset (Fin k)) = {univ} := by
    simpa using Finset.powersetCard_self (univ : Finset (Fin k))
  have hone : ((Vᴴ * V).submatrix (fun x : (univ : Finset (Fin k)) => (x : Fin k))
      (fun x : (univ : Finset (Fin k)) => (x : Fin k))).det = 1 := by
    rw [hVV']
    exact (Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (fun x => mem_univ x)) 1).trans
      det_one
  have single : ∀ (ν : Fin k → ℂ) (m : ℕ),
      (det (1 + (X : ℂ[X]) • (V * diagonal ν * Vᴴ).map C)).coeff m
        = (∏ j ∈ (univ : Finset (Fin k)), (1 + X * C (ν j))).coeff m := by
    intro ν m
    rw [← moment V hVV ν m, hu, sum_singleton, hone, mul_one]
  have htr : trace M = ∑ j, L j := by
    rw [← coeff_det_one_add_X_smul_one, hspec, single, (coeff_prod_one_add L univ).2.1]
  have htr2 : trace (M * M) = ∑ j, L j ^ 2 := by
    rw [← coeff_det_one_add_X_smul_one, hMM, single,
      (coeff_prod_one_add (fun a => L a * L a) univ).2.1]
    simp [pow_two]
  rw [htr, htr2, hspec, single, (coeff_prod_one_add L univ).2.2]
end Formalism.NuclearRankWeightBounds.P
