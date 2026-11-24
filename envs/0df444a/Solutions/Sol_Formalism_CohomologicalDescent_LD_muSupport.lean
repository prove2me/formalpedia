-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.muSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:56:40.223787+00:00
-- url     : https://prove2.me/submissions/d1c2fca2-ea2c-43ad-ac35-11ee279fee5e

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : MuSupport := by
  intro p w i q lam2 c hw hmu
  unfold mu at hmu
  obtain ⟨tau, htau, hne⟩ : ∃ tau ∈ shapes p w i lam2, boxesOfContent lam2 tau c ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hmu (Nat.eq_zero_of_le_zero (Finset.sup_le fun t ht => (hcon t ht).le))
  unfold boxesOfContent at hne
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  simp only [shapes, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at htau
  have h1 := (htau.1 a).2
  have h2 := hw a
  have h3 := a.isLt
  constructor <;> omega
end Formalism.CohomologicalDescent.LD
