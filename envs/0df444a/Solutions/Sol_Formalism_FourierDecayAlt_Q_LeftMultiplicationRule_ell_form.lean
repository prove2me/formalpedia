-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.ell_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:52:10.316809+00:00
-- url     : https://prove2.me/submissions/0bf5aaf8-d46f-443e-b4a5-e106225db9a3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_HasDerivAtPhase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_LeftMultiplicationRule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {l : Fin r} {M : Mx k r}
    (hM : InS k r l M) : ell k r z M = ∑ q, M (eI k r l) q * fvec k r z l.succ q := by
  have hl := l.isLt
  unfold ell
  rw [Finset.sum_eq_single l]
  · split_ifs with h
    · unfold fvec
      rw [dif_pos (show l.succ.val < r by simp only [Fin.val_succ]; exact h)]
      simp only [bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
    · unfold fvec
      rw [dif_neg (show ¬ l.succ.val < r by simp only [Fin.val_succ]; exact h)]
      rfl
  · intro a _ hal
    have hal' : a.val ≠ l.val := Fin.val_ne_of_ne hal
    have hal2 := a.isLt
    split_ifs with h
    · apply hM
      intro hs
      unfold SP at hs
      simp only [eI] at hs
      omega
    · simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro q _
      have hq2 := q.isLt
      by_cases hq : r + k < q.val
      · rw [hz q (Or.inr hq), mul_zero]
      · rw [hM _ _ ?_, zero_mul]
        intro hs
        unfold SP at hs
        simp only [eI] at hs
        omega
  · intro h
    exact absurd (Finset.mem_univ l) h
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
