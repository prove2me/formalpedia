-- Prove2me | solution 1 for Formalism.ResultantValuation.laplaceExpansionRows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:18:16.263004+00:00
-- url     : https://prove2.me/submissions/274bcb0d-bdc3-4f41-b822-33deab636174

import Definitions.Def_Formalism_ResultantValuation_ResultantConjugate
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_natAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_det_rows
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_natAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_sign_glue
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_bijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_natAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_natAdd

set_option autoImplicit false
open Finset Equiv
noncomputable section
open Formalism Formalism.ResultantValuation
open LaplaceProof
namespace Formalism.ResultantValuation
theorem _root_.solution : LaplaceRows := by
  intro R _ a b M
  rw [det_rows M, ← (glue_bijective (a := a) (b := b)).sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [det_rows, det_rows, mul_assoc, Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [sign_glue, Fin.prod_univ_add]
  simp only [glue_castAdd, glue_natAdd, Matrix.submatrix_apply]
  push_cast
  ring
end Formalism.ResultantValuation
