-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.rowdiv_mem_dualWeyl_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:04.774791+00:00
-- url     : https://prove2.me/submissions/a75a4531-6ff5-4572-b19d-d422b34937a1

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
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
theorem _root_.solution (R : Type*) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) :
    f ∈ dualWeyl R r n ν ↔ IsWeightedHomogeneous (colW r n) f ν ∧
      ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  simp [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]
end Formalism.GradedWeylDivisibility
