-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.lattice_z_zero_columns
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:16:12.589842+00:00
-- url     : https://prove2.me/submissions/cc8d83e6-6d6d-4f2a-9def-eefcad043edb

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_hw_mem
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_incl_of_le
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution : LatticeInclusionTrivialWeight := by
  unfold LatticeInclusionTrivialWeight
  intro r hn ν l hl
  apply la_incl_of_le hn ν _ _ hl
  intro x _
  have h1 : hw ℤ hn ν = 1 := by simp [hw]
  have hmem := la_hw_mem ℤ hn ν
  rw [h1] at hmem
  have hx : x = (coeff 0 x) • (1 : MvPolynomial (Fin r × Fin 0) ℤ) := by
    rw [MvPolynomial.smul_eq_C_mul, mul_one]
    exact MvPolynomial.eq_C_of_isEmpty x
  rw [hx]
  exact Submodule.smul_mem _ _ hmem
end Formalism.CohomologicalDescent.LA
