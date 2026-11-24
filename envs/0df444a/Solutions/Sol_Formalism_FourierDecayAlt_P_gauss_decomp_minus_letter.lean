-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gauss_decomp_minus_letter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:07:54.962376+00:00
-- url     : https://prove2.me/submissions/1d59e998-03c4-4afb-a9b5-586fa170db5d

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_l_shift_from_determinant
import Theorems.Thm_Formalism_FourierDecayAlt_P_quasi_determinant_from_entries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : GaussMinus := by
  intro 𝕜 A _ _ _ t τinv q S h Y hY hY1
  have h' := h
  obtain ⟨-, -, -, h4, -, -⟩ := h'
  have hY' : Y - 1 + 1 ∈ S := by rw [sub_add_cancel]; exact hY
  have hl := l_shift_from_determinant 𝕜 A t τinv q S h (Y - 1) hY1 hY'
  rw [sub_add_cancel] at hl
  have hB : lf t τinv (Y - 1) * t Y 1 1 = t Y 1 0 := by
    rw [hl, mul_assoc, (h4 Y hY).2, mul_one]
  have hC : t Y 1 1 * mf t τinv Y = t Y 0 1 := by
    unfold mf
    rw [← mul_assoc, (h4 Y hY).1, one_mul]
  have hA : q (Y - 1) • τinv (Y - 1) + lf t τinv (Y - 1) * t Y 1 1 * mf t τinv Y = t Y 0 0 := by
    rw [hB, ← quasi_determinant_from_entries 𝕜 A t τinv q S h Y hY hY1]
    unfold mf
    noncomm_ring
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.eta_fin_two (t Y)ᵀ]
  simp only [Matrix.transpose_apply, one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add]
  rw [hA, hB, hC]
end Formalism.FourierDecayAlt.P
