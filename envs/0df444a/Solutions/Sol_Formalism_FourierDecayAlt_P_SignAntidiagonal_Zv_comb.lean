-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.Zv_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:50:27.110236+00:00
-- url     : https://prove2.me/submissions/d75528a2-a135-4621-be03-575dd89cba80

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DpsiIsDerivation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangularFactorMiddleRow
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_Ym_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val



set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (hdet : (Ym k r j hj y).det ≠ 0) (a : Fin j) (p : Fin (2 * r + k + 1)) :
    ∑ c : Fin j, Zv k r j hj y c p * y a (esI k r (Fin.castLE hj c)) = y a p := by
  have hYG : Ym k r j hj y * (Ym k r j hj y)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  unfold Zv
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single a]
  · have := congrFun (congrFun hYG a) a
    rw [Matrix.mul_apply, Matrix.one_apply, if_pos rfl] at this
    simp only [Ym_apply] at this
    calc ∑ c, (Ym k r j hj y)⁻¹ c a * y a p * y a (esI k r (Fin.castLE hj c))
        = (∑ c, y a (esI k r (Fin.castLE hj c)) * (Ym k r j hj y)⁻¹ c a) * y a p := by
          rw [Finset.sum_mul]; congr 1; ext c; ring
      _ = y a p := by rw [this, one_mul]
  · intro a' _ ha'
    have := congrFun (congrFun hYG a) a'
    rw [Matrix.mul_apply, Matrix.one_apply, if_neg (Ne.symm ha')] at this
    simp only [Ym_apply] at this
    calc ∑ c, (Ym k r j hj y)⁻¹ c a' * y a' p * y a (esI k r (Fin.castLE hj c))
        = (∑ c, y a (esI k r (Fin.castLE hj c)) * (Ym k r j hj y)⁻¹ c a') * y a' p := by
          rw [Finset.sum_mul]; congr 1; ext c; ring
      _ = 0 := by rw [this, zero_mul]
  · simp
end Formalism.FourierDecayAlt.P.SignAntidiagonal
