-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_shapes_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:43:36.768291+00:00
-- url     : https://prove2.me/submissions/1e96d9fd-d774-43c8-b907-3c2254672288

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
theorem _root_.solution (p w y i : ℕ) (hp : 1 ≤ p) (h : y + i ≤ w) :
    shapes p w i (fun _ : Fin 1 => y) = {fun _ => y + i} := by
  ext tau
  simp only [shapes, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro ⟨-, -, hsum, -, -⟩
    funext a
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    simpa using hsum
  · rintro rfl
    refine ⟨fun _ => ⟨Nat.le_add_right y i, le_rfl⟩, fun _ _ _ => le_rfl, by simp, ?_, ?_⟩
    · intro b j hj
      unfold colLen
      exact (Finset.card_le_univ _).trans (by simpa using hp)
    · unfold boxesOfContent
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro a - ⟨h1, h2⟩
      push_cast at h2
      omega
end Formalism.CohomologicalDescent.LD
