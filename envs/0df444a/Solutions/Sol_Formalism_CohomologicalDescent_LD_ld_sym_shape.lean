-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_sym_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:42:34.492797+00:00
-- url     : https://prove2.me/submissions/66396a98-86e5-47e3-840b-66643e1a9164

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
theorem _root_.solution (q w i : ℕ) (hi : i ≤ w) :
    (fun a : Fin q => if a.val = 0 then i else 0) ∈ shapes 1 w i (fun _ : Fin q => 0) ∨ q = 0 := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · exact Or.inr hq
  left
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  simp only [shapes, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨fun a => ⟨Nat.zero_le _, by split_ifs <;> omega⟩, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have hab' : a.val ≤ b.val := hab
    split_ifs <;> omega
  · simp [Fin.sum_univ_succ]
  · intro b j hj
    unfold colLen
    rw [Finset.card_le_one]
    intro a ha c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hc
    apply Fin.ext
    split_ifs at ha hc <;> omega
  · unfold boxesOfContent
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro a - ⟨-, h2⟩
    beta_reduce at h2
    split_ifs at h2 <;> omega
end Formalism.CohomologicalDescent.LD
