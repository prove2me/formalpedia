-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_range_binForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:15:01.626496+00:00
-- url     : https://prove2.me/submissions/6c35f502-88e4-412d-a84a-fa059a5aff6f

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_binForm_apply
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_binForm_single
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
theorem _root_.solution (R : Type) [CommRing R] (d : ℕ) :
    LinearMap.range (binForm R d) = la_monLat R (0 : Fin 1) d := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    rw [la_binForm_apply, la_monLat]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨d - i.val, i.val, by have := i.isLt; omega, rfl⟩))
  · rw [la_monLat, Submodule.span_le]
    rintro f ⟨p, q, hpq, rfl⟩
    refine ⟨Pi.single ⟨q, by omega⟩ 1, ?_⟩
    rw [la_binForm_single, one_smul]
    simp only [Fin.val_mk, show d - q = p by omega]
end Formalism.CohomologicalDescent.LA
