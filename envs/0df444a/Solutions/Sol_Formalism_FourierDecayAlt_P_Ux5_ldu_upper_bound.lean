-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.ldu_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:00:55.070059+00:00
-- url     : https://prove2.me/submissions/f5ea5b56-2cd9-4880-879f-cc2fc71668b3

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_det_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_submatrix_mul_lower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.Ux5
theorem _root_.solution {p : ℕ} (L U : Matrix (Fin p) (Fin p) ℂ) (d : Fin p → ℂ)
    (hL : ∀ a b, a < b → L a b = 0) (hL1 : ∀ a, L a a = 1) (hU : ∀ a b, b < a → U a b = 0)
    (hU1 : ∀ a, U a a = 1) {m : ℝ} (hM : EB (L * diagonal d * U) m) (i j' : Fin p) :
    ‖(∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)) * U i j'‖ ≤ (i.val + 1).factorial * m ^ (i.val + 1) := by
  set r : Fin (i.val + 1) → Fin p := Fin.castLE i.isLt with hr
  set f : Fin (i.val + 1) → Fin p := fun t => if t.val < i.val then r t else j' with hf
  have h1 : (L * diagonal d * U).submatrix r f = L.submatrix r r * (diagonal d * U).submatrix r f := by
    rw [mul_assoc]
    exact submatrix_mul_lower i.isLt L _ hL f
  have h2 : (L.submatrix r r).det = 1 := by
    have hb : (L.submatrix r r).BlockTriangular OrderDual.toDual := by
      intro a b hab
      have hab' : a < b := hab
      simp only [submatrix_apply]
      apply hL
      rw [hr, Fin.lt_iff_val_lt_val, Fin.coe_castLE, Fin.coe_castLE]
      exact hab'
    rw [Matrix.det_of_isLowerTriangular _ hb]
    simp [hL1]
  have hrl : r (Fin.last i.val) = i := by
    apply Fin.ext
    simp [hr]
  have hfl : f (Fin.last i.val) = j' := by
    simp [hf]
  have hfc : ∀ t : Fin i.val, f t.castSucc = r t.castSucc := by
    intro t
    simp [hf, t.isLt]
  have h3 : ((diagonal d * U).submatrix r f).det = (∏ t, d (r t)) * U i j' := by
    have hb : ((diagonal d * U).submatrix r f).BlockTriangular id := by
      intro a b hab
      have hab' : b < a := hab
      simp only [submatrix_apply, diagonal_mul]
      have hb' : b.val < i.val := lt_of_lt_of_le hab' (Nat.lt_succ_iff.mp a.isLt)
      have : f b = r b := by simp [hf, hb']
      rw [this, hU _ _ (by rw [hr, Fin.lt_iff_val_lt_val, Fin.coe_castLE, Fin.coe_castLE]; exact hab'), mul_zero]
    rw [Matrix.det_of_isUpperTriangular hb, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    simp only [submatrix_apply, diagonal_mul, hfc, hrl, hfl, hU1, mul_one]
    ring
  have h4 := det_norm_le ((L * diagonal d * U).submatrix r f) (m := m) (fun a b => hM _ _)
  rw [h1, Matrix.det_mul, h2, h3, one_mul] at h4
  simpa using h4
end Formalism.FourierDecayAlt.P.Ux5
