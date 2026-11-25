-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.lemma_a_rank_two_one_column
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:53:05.017371+00:00
-- url     : https://prove2.me/submissions/bb504ea8-8bbf-482b-95d2-c99cdc3bfe54

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_mem_of_dvd
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_arith
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_weyl_r2n1
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_nabla_r2n1
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_eExp_r2n1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution : LemmaAR_r2n1 := by
  unfold LemmaAR_r2n1
  intro R _ hn ν l hl hu x hx
  rw [la_nabla_r2n1] at hx
  rw [la_weyl_r2n1, la_eExp_r2n1]
  obtain ⟨m, hm, hdiv⟩ := la_arith l (ν 0) hl
  obtain ⟨u, hu'⟩ := hu m hm
  have key : ∀ y ∈ la_monLat R (0 : Fin 1) (ν 0),
      ((m : R) * (l : R) ^ Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0)) • y ∈ la_binLat R 0 (ν 0) := by
    intro y hy
    rw [la_monLat] at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨p, q, hpq, rfl⟩ := hz
      have h := la_mem_of_dvd R (0 : Fin 1) hpq (N := m * l ^ Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0))
        (by rw [hpq]; exact hdiv q (by omega))
      rw [MvPolynomial.smul_eq_C_mul, ← Nat.cast_pow, ← Nat.cast_mul, map_natCast]
      exact h
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      rw [smul_add]
      exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      rw [smul_comm]
      exact Submodule.smul_mem _ c ha
  have h2 := Submodule.smul_mem _ (↑u⁻¹ : R) (key x hx)
  rwa [smul_smul, ← mul_assoc, ← hu', Units.inv_mul, one_mul] at h2
end Formalism.CohomologicalDescent.LA
