-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.ShapeCovering.signed_minors_cofactor_adjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:09:38.660976+00:00
-- url     : https://prove2.me/submissions/1bec0871-b7f6-40ce-98e4-31742e527a9e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_HermitianTensor_ShapeCovering_StatementY
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_HermitianTensor_ShapeCovering_CovDet
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
noncomputable section
namespace Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
open MvPolynomial Formalism.GradedWeylDivisibility
private theorem cvd_adj {B : Type*} [CommRing B] {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) B)
    (i : Fin (m + 1)) :
    M.adjugate 0 i = (-1) ^ (i : ℕ) * Matrix.det (fun a b : Fin m => M (i.succAbove a) b.succ) := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_zero, add_zero, Fin.succAbove_zero]
  rfl
private theorem cvd_covY (K : Type) [Field K] (m : ℕ) (i : Fin (m + 1)) :
    covY K m i = (cvdM K m).adjugate 0 i := by
  rw [cvd_adj]
  simp only [covY]
  congr 2
end Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
open MvPolynomial Formalism.GradedWeylDivisibility
namespace Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
theorem _root_.solution : CovL5adj := by
  intro K _ m g i
  have hM : (rowAct K (n := m + 1) g : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K →+* _).mapMatrix (cvdM K m)
      = g.map C * cvdM K m := by
    ext a b
    refine Fin.cases ?_ (fun b' => ?_) b
    · simp [cvdM, Matrix.mul_apply]
    · simp [cvdM, Matrix.mul_apply, rowAct]
  rw [cvd_covY]
  calc rowAct K g ((cvdM K m).adjugate 0 i)
      = ((rowAct K (n := m + 1) g : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K →+* _).mapMatrix
          (cvdM K m).adjugate) 0 i := rfl
    _ = (g.map C * cvdM K m).adjugate 0 i := by rw [RingHom.map_adjugate, hM]
    _ = (((cvdM K m).adjugate * (g.map C).adjugate :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)) 0 i) := by
        rw [Matrix.adjugate_mul_distrib]
    _ = ∑ j, C (g.adjugate j i) * covY K m j := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← cvd_covY, mul_comm]
      congr 1
      rw [show g.map C = (C : K →+* MvPolynomial (Fin (m + 1) × Fin (m + 1)) K).mapMatrix g from rfl,
        ← RingHom.map_adjugate]
      rfl
end Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
