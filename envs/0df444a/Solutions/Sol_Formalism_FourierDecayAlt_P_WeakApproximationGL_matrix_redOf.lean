-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakApproximationGL.matrix_redOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:46.016798+00:00
-- url     : https://prove2.me/submissions/8757e3f9-5e7b-45ac-affa-3f25a9a446cd

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_tri_gt
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_rhs_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_rhs_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_wMat_mulVec_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_wMat_mul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakApproximationGL
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G5
namespace Formalism.FourierDecayAlt.P.WeakApproximationGL
theorem _root_.solution (m : ℕ) (t ρ₁ : ℂ) (p : XY m) :
    wMat (m + 2) * Mcoord t (strictUpper (redOf m p).2.2.1) (redOf m p).2.2.2
        (Fin.cons ρ₁ (redOf m p).2.1) (redOf m p).1 =
      t • subShift (m + 2) + Matrix.diagonal (Fin.cons ρ₁ p.1 : Fin (m + 2) → ℂ) + strictUpper p.2 := by
  ext i j
  rw [wMat_mul_apply]
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨r, rfl⟩
  ·
    rw [Fin.rev_zero]
    rcases Fin.eq_castSucc_or_eq_last j with ⟨c, rfl⟩ | rfl
    · rw [Mcoord, blk_lc]
      rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨k, rfl⟩
      · simp [subShift, strictUpper]
      · rw [Fin.cons_succ, rhs_zero _ _ _ _ (by simp [Fin.lt_def])]
        rfl
    · rw [Mcoord, blk_ll, rhs_zero _ _ _ _ Fin.last_pos]
      rfl
  ·
    rw [Fin.rev_succ, rhs_succ]
    rcases Fin.eq_castSucc_or_eq_last j with ⟨c, rfl⟩ | rfl
    · rw [Mcoord, blk_cc, wMat_mul_apply, Fin.rev_rev]
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, strictUpper,
        Matrix.of_apply, Fin.val_castSucc, smul_eq_mul]
      by_cases hrc : r < c
      · have h1 : r ≠ c := ne_of_lt hrc
        have h2 : (c : ℕ) ≠ r := fun h => h1 (Fin.ext h.symm)
        rw [dif_pos hrc, if_neg h1, if_neg h2]
        simp only [mul_zero, zero_add]
        rfl
      · have hcr : c.castSucc < r.succ := by
          rw [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
          rw [not_lt, Fin.le_iff_val_le_val] at hrc
          omega
        rw [dif_neg hrc, tri_gt _ _ hcr]
        by_cases hrc' : r = c
        · subst hrc'
          simp
        · have h2 : (c : ℕ) ≠ r := fun h => hrc' (Fin.ext h.symm)
          simp [hrc', h2]
    · rw [Mcoord, blk_cl, wMat_mulVec_apply, Fin.rev_rev]
      have hne : ((Fin.last (m + 1) : Fin (m + 2)) : ℕ) ≠ r := by
        simp only [Fin.val_last]
        have := r.isLt
        omega
      rw [if_neg hne, zero_add]
      rfl
end Formalism.FourierDecayAlt.P.WeakApproximationGL
