-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_weyl_r2n2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:33:50.174878+00:00
-- url     : https://prove2.me/submissions/435b38d8-6b9f-4741-9df3-de8c6e2d3942

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_word_mem
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_rowDiv_xy_zero
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_binLat_stable
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_weyl_le_of_stable
import Theorems.Thm_Formalism_CohomologicalDescent_LA_highest_weight_rank_two
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_rowDiv_tw_ne
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_tw_stable
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
theorem _root_.solution (R : Type) [CommRing R] (hn : 2 ≤ 2) (ν : Fin 2 → ℕ) :
    weyl R 2 2 hn ν =
      (la_binLat R (0 : Fin 2) (ν 0 - ν 1)).map (LinearMap.mulLeft R (la_det R ^ ν 1)) := by
  have hhw : hw R hn ν = la_det R ^ ν 1 * la_xy R (0 : Fin 2) (ν 0 - ν 1) 0 := highest_weight_rank_two R hn ν
  apply le_antisymm
  · refine la_weyl_le_of_stable R hn ν _ ?_ (fun a b k f hf => la_tw_stable R _
      (fun a b k f hf => la_binLat_stable R 0 (ν 0 - ν 1) a b k f hf) (ν 1) a b k f hf)
    rw [hhw]
    refine Submodule.mem_map.mpr ⟨la_xy R 0 (ν 0 - ν 1) 0, ?_, rfl⟩
    rw [la_binLat]
    exact Submodule.subset_span ⟨ν 0 - ν 1, 0, by simp, by simp⟩
  · rw [la_binLat, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨f, ⟨p, q, hpq, rfl⟩, rfl⟩
    have h := la_word_mem R hn ν [((1 : Fin 2), (0 : Fin 2), q)]
    have e : applyWord R [((1 : Fin 2), (0 : Fin 2), q)] (hw R hn ν) =
        LinearMap.mulLeft R (la_det R ^ ν 1)
          (((p + q).choose q : MvPolynomial (Fin 2 × Fin 2) R) * la_xy R 0 p q) := by
      show rowDiv R 1 0 q (hw R hn ν) = _
      rw [hhw, la_rowDiv_tw_ne R 1 0 (by decide), ← hpq, la_rowDiv_xy_zero,
        LinearMap.mulLeft_apply]
      simp [la_xy]
    rw [e] at h
    exact h
end Formalism.CohomologicalDescent.LA
