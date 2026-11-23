-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldlat_rowAct_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:07.031887+00:00
-- url     : https://prove2.me/submissions/a472a348-aba0-42d5-828e-e4c72b7a07d3

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
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
theorem _root_.solution {R : Type*} [CommRing R] {k n : ℕ} :
    rowAct R (n := n) (1 : Matrix (Fin k) (Fin k) R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [rowAct, aeval_X, AlgHom.id_apply]
  rw [Finset.sum_eq_single v.1 (fun b _ hb => by simp [Matrix.one_apply_ne (Ne.symm hb)]) (by simp)]
  simp
end Formalism.GradedWeylDivisibility
