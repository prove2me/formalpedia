-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldtensor_blockAct_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:10.40185+00:00
-- url     : https://prove2.me/submissions/cd0a9fde-c22b-4e8a-9385-bf43c7292c2d

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BlockActTensor
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
theorem _root_.solution (K : Type*) [CommRing K] {S : Type*} {k n : ℕ}
    (g : S → Matrix (Fin k) (Fin k) K) (s : S) :
    (blockAct K (n := n) g).comp (blockEmb K (k := k) (n := n) s) =
      (blockEmb K s).comp (rowAct K (g s)) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [blockEmb, blockAct, rowAct, map_sum, rename_C]
end Formalism.GradedWeylDivisibility
