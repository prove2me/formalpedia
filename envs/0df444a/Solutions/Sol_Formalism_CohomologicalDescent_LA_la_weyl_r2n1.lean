-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_weyl_r2n1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:33:47.57743+00:00
-- url     : https://prove2.me/submissions/2d83395c-f516-46fd-8b72-2e8a4a22fcba

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_word_mem
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_rowDiv_xy_zero
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_binLat_stable
import Theorems.Thm_Formalism_CohomologicalDescent_LA_highest_weight_one_column
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_weyl_le_of_stable
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
theorem _root_.solution (R : Type) [CommRing R] (hn : 1 ≤ 2) (ν : Fin 1 → ℕ) :
    weyl R 2 1 hn ν = la_binLat R (0 : Fin 1) (ν 0) := by
  have hhw : hw R hn ν = la_xy R (0 : Fin 1) (ν 0) 0 := by
    rw [highest_weight_one_column, la_xy, pow_zero, mul_one]
    try rfl
  apply le_antisymm
  · refine la_weyl_le_of_stable R hn ν _ ?_ (fun a b k f hf => la_binLat_stable R 0 (ν 0) a b k f hf)
    rw [hhw, la_binLat]
    exact Submodule.subset_span ⟨ν 0, 0, by simp, by simp⟩
  · rw [la_binLat, Submodule.span_le]
    rintro f ⟨p, q, hpq, rfl⟩
    have h := la_word_mem R hn ν [((1 : Fin 2), (0 : Fin 2), q)]
    have e : applyWord R [((1 : Fin 2), (0 : Fin 2), q)] (hw R hn ν) =
        ((p + q).choose q : MvPolynomial (Fin 2 × Fin 1) R) * la_xy R 0 p q := by
      show rowDiv R 1 0 q (hw R hn ν) = _
      rw [hhw, ← hpq, la_rowDiv_xy_zero]
      simp [la_xy]
    rw [e] at h
    exact h
end Formalism.CohomologicalDescent.LA
