-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.muRange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:59:38.347829+00:00
-- url     : https://prove2.me/submissions/170e9ea7-7c25-4995-991b-9ebbf1c4f1df

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
theorem _root_.solution : MuRange := by
  intro p w i q m lam2 c hlam hmu
  unfold mu at hmu
  obtain ⟨tau, htau, hne⟩ : ∃ tau ∈ shapes p w i lam2, boxesOfContent lam2 tau c ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hmu (Nat.eq_zero_of_le_zero (Finset.sup_le fun t ht => (hcon t ht).le))
  unfold boxesOfContent at hne
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  simp only [shapes, Finset.mem_filter] at htau
  have hz := htau.2.2.2.2
  unfold boxesOfContent at hz
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hz
  have hna := hz (Finset.mem_univ a)
  have h1 := hlam a
  have h3 := a.isLt
  constructor
  · omega
  · by_contra hc
    push_neg at hc
    exact hna ⟨by omega, by omega⟩
end Formalism.CohomologicalDescent.LD
