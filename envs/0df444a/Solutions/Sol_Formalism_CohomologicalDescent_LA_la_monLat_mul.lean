-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_monLat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:53:09.459106+00:00
-- url     : https://prove2.me/submissions/2d3cd05b-69c5-4687-a425-f975f2cedd49

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
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
theorem _root_.solution (R : Type) [CommRing R] {n : ℕ} (s : Fin n) {d d' : ℕ}
    {u u' : MvPolynomial (Fin 2 × Fin n) R} (hu : u ∈ la_monLat R s d)
    (hu' : u' ∈ la_monLat R s d') : u * u' ∈ la_monLat R s (d + d') := by
  have h := Submodule.mul_mem_mul hu hu'
  rw [la_monLat, la_monLat, Submodule.span_mul_span] at h
  rw [la_monLat]
  refine Submodule.span_mono ?_ h
  rintro f ⟨a, ⟨p, q, hpq, rfl⟩, b, ⟨p', q', hpq', rfl⟩, rfl⟩
  exact ⟨p + p', q + q', by omega, by simp only [la_xy]; ring⟩
end Formalism.CohomologicalDescent.LA
