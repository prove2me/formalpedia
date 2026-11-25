-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.ell_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:10:25.751093+00:00
-- url     : https://prove2.me/submissions/be8a962a-23dc-413d-8f09-6851ea51cff4

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_eI_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}
private lemma mulVec_bvec_lemma_2 (M : Mx k r) (q : Fin (2 * r + k + 1)) :
    M *ᵥ bvec q = fun p => M p q := by
  funext p
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
end
end

set_option autoImplicit false
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
theorem _root_.solution {l : Fin r} {M : Mx k r} (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (hM : InS k r l M) : ell k r z M = (M *ᵥ fvec k r z l.succ) (eI k r l) := by
  have hl := l.isLt
  unfold ell
  rw [Finset.sum_eq_single l]
  · by_cases h : l.val + 1 < r
    · have h' : (Fin.succ l).val < r := by simpa using h
      rw [dif_pos h]
      simp only [fvec, dif_pos h', mulVec_bvec_lemma_2]
      rfl
    · have h' : ¬ (Fin.succ l).val < r := by simpa using h
      rw [dif_neg h]
      simp only [fvec, dif_neg h']
  · intro a _ hal
    have hal' : a.val ≠ l.val := fun e => hal (Fin.ext e)
    have ha := a.isLt
    split_ifs with h
    · apply hM
      unfold SP
      simp only [eI_val]
      omega
    · simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro q _
      by_cases hq : SP k r l (eI k r a) q
      · have hq' : q.val = 2 * r + k - l.val := by
          unfold SP at hq
          simp only [eI_val] at hq
          omega
        rw [hz q (Or.inr (by omega)), mul_zero]
      · rw [hM _ _ hq, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
