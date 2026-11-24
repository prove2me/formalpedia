-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.initial_minor_mem_det_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:16:46.780846+00:00
-- url     : https://prove2.me/submissions/b2347a2f-50e7-46e3-ad72-17a0c257e039

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_fin_two_eq_zero_or_one
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_T_xy
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
theorem _root_.solution (s : ℕ) (I : Fin s → Fin 2) (hs : s ≤ 2) :
    initMinor ℤ I hs ∈ detPowMulMonomialSpan (if s = 2 then 1 else 0) (if s = 1 then 1 else 0) := by
  obtain rfl | rfl | rfl : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  · have h : initMinor ℤ I hs = 1 := Matrix.det_isEmpty
    rw [h]
    simpa [la_xy] using la_T_xy 0 0 0
  · have h : initMinor ℤ I hs = X (I 0, 0) := Matrix.det_fin_one _
    rw [h]
    rcases fin_two_eq_zero_or_one (I 0) with h0 | h0 <;> rw [h0]
    · simpa [la_xy] using la_T_xy 0 1 0
    · simpa [la_xy] using la_T_xy 0 0 1
  · have h : initMinor ℤ I hs = X (I 0, 0) * X (I 1, 1) - X (I 0, 1) * X (I 1, 0) :=
      Matrix.det_fin_two _
    have h2 := la_T_xy 1 0 0
    simp only [la_xy, pow_zero, pow_one, mul_one, add_zero] at h2
    show initMinor ℤ I hs ∈ detPowMulMonomialSpan 1 0
    rw [h]
    rcases fin_two_eq_zero_or_one (I 0) with h0 | h0 <;> rcases fin_two_eq_zero_or_one (I 1) with h1 | h1 <;> rw [h0, h1]
    · have e : X ((0 : Fin 2), (0 : Fin 2)) * X ((0 : Fin 2), (1 : Fin 2)) -
          X ((0 : Fin 2), (1 : Fin 2)) * X ((0 : Fin 2), (0 : Fin 2)) =
          (0 : MvPolynomial (Fin 2 × Fin 2) ℤ) := by ring
      rw [e]
      exact Submodule.zero_mem _
    · exact h2
    · have e : X ((1 : Fin 2), (0 : Fin 2)) * X ((0 : Fin 2), (1 : Fin 2)) -
          X ((1 : Fin 2), (1 : Fin 2)) * X ((0 : Fin 2), (0 : Fin 2)) = -la_det ℤ := by
        simp only [la_det]
        ring
      rw [e]
      exact Submodule.neg_mem _ h2
    · have e : X ((1 : Fin 2), (0 : Fin 2)) * X ((1 : Fin 2), (1 : Fin 2)) -
          X ((1 : Fin 2), (1 : Fin 2)) * X ((1 : Fin 2), (0 : Fin 2)) =
          (0 : MvPolynomial (Fin 2 × Fin 2) ℤ) := by ring
      rw [e]
      exact Submodule.zero_mem _
end Formalism.CohomologicalDescent.LA
