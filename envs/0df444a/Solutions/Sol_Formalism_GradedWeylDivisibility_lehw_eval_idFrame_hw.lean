-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lehw_eval_idFrame_hw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:30.25547+00:00
-- url     : https://prove2.me/submissions/7bd9b369-07e4-4d78-90ce-058fee39e6bf

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    eval (idFrame ℚ r n) (hw ℚ hn ν) = 1 := by
  unfold hw
  rw [map_prod]
  apply Finset.prod_eq_one
  intro s _
  rw [map_pow]
  convert one_pow (M := ℚ) _
  unfold lpMinor
  rw [RingHom.map_det]
  refine (congrArg Matrix.det ?_).trans Matrix.det_one
  ext p q
  simp [idFrame, Matrix.one_apply, Fin.ext_iff]
end Formalism.GradedWeylDivisibility
