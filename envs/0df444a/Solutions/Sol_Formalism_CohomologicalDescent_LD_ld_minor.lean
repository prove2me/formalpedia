-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:43:35.771101+00:00
-- url     : https://prove2.me/submissions/7e2b8f80-8477-48cc-a5ba-76ad5e83a873

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (s : ℕ) (I : Fin s → Fin 2) (hs : s ≤ 2) :
    (s = 0 ∧ initMinor ℤ I hs = 1) ∨ (s = 1 ∧ ∃ a : Fin 2, initMinor ℤ I hs = X (a, 0)) ∨
      (s = 2 ∧ ∃ ε : ℤ, initMinor ℤ I hs = C ε * ldDet) := by
  obtain rfl | rfl | rfl : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  · left
    exact ⟨rfl, by unfold initMinor; exact Matrix.det_isEmpty⟩
  · right; left
    refine ⟨rfl, I 0, ?_⟩
    unfold initMinor
    rw [Matrix.det_fin_one]
    rfl
  · right; right
    refine ⟨rfl, ?_⟩
    have h : initMinor ℤ I hs = X (I 0, 0) * X (I 1, 1) - X (I 0, 1) * X (I 1, 0) := by
      unfold initMinor
      rw [Matrix.det_fin_two]
      rfl
    rw [h]
    generalize I 0 = a
    generalize I 1 = b
    have ha : a = 0 ∨ a = 1 := by omega
    have hb : b = 0 ∨ b = 1 := by omega
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact ⟨0, by rw [C_0]; ring⟩
    · exact ⟨1, by rw [C_1]; unfold ldDet; ring⟩
    · exact ⟨-1, by rw [C_neg, C_1]; unfold ldDet; ring⟩
    · exact ⟨0, by rw [C_0]; ring⟩
end Formalism.CohomologicalDescent.LD
