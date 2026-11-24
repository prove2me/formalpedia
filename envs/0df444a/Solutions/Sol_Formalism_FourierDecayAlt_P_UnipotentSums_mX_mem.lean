-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentSums.mX_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:55:01.076212+00:00
-- url     : https://prove2.me/submissions/325a2506-859c-472e-963e-0018b6f658d9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_mX_col_X
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_unipotent_apply_middle_column
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_mX_uh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentSums
open C2x5 C2x6 FlagSpanVanishing HermitianXiVector
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.UnipotentSums
theorem _root_.solution (vX : Matrix (Fin r) (Fin r) ℂ) (hv : vX ∈ C2.UTset r) : C2.mX k r vX ∈ Nset k r := by
  obtain ⟨hv1, hv2⟩ := hv
  have hdet : vX.det = 1 := by
    rw [Matrix.det_of_upperTriangular (by intro i j hij; exact hv1 i j hij)]
    simp [hv2]
  refine ⟨mX_uh vX (by rw [hdet]; exact isUnit_one), ?_, ?_⟩
  · intro a i hai
    rw [mX_col_X]
    by_cases hi : i.val < r
    · rw [dif_pos hi]
      by_cases he : i = eI k r a
      · rw [if_pos he]
        subst he
        exact hv2 a
      · rw [if_neg he]
        apply hv1
        show a.val < i.val
        have : i.val ≠ a.val := fun h => he (Fin.ext h)
        omega
    · rw [dif_neg hi, if_neg]
      intro h
      apply hi
      rw [h]
      exact a.isLt
  · intro i j hj1 hj2 _
    exact unipotent_apply_middle_column vX i j hj1 hj2
end Formalism.FourierDecayAlt.P.UnipotentSums
