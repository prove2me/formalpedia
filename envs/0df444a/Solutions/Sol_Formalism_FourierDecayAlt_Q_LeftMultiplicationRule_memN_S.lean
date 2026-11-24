-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.memN_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:52:12.623797+00:00
-- url     : https://prove2.me/submissions/d1d08107-0d75-4aef-983c-3162af021418

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_eI_val
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_esI_val
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_mul_apply_S
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
private lemma gent_lemma {l : Fin r} {Y : Mx k r} (hY : InS k r l Y) (i j : Fin (2 * r + k + 1))
    (h1 : ¬ SP k r l i j) (h2 : ¬ (i.val = l.val ∧ j.val = 2 * r + k - l.val)) :
    (1 + Y + (1 / 2 : ℂ) • (Y * Y)) i j = (1 : Mx k r) i j := by
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, hY i j h1, mul_apply_S hY hY i j h2,
    smul_zero, add_zero, add_zero]
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
theorem _root_.solution {l : Fin r} {Y : Mx k r} (hY : InS k r l Y)
    (hU : 1 + Y + (1 / 2 : ℂ) • (Y * Y) ∈ UH (Hpk k r)) :
    1 + Y + (1 / 2 : ℂ) • (Y * Y) ∈ Nlev k r l.castSucc := by
  have hl := l.isLt
  refine ⟨⟨hU, fun a i hai => ?_, fun i j hj1 hj2 hi => ?_⟩, hU, fun a ha => ⟨?_, ?_⟩⟩
  · have ha := a.isLt
    rw [gent_lemma hY _ _ (by unfold SP; simp only [eI_val]; omega) (by simp only [eI_val]; omega)]
    exact Matrix.one_apply
  · rw [gent_lemma hY _ _ (by unfold SP; omega) (by omega)]
    exact Matrix.one_apply
  · have ha' : a.val < l.val := ha
    have ha2 := a.isLt
    rw [mulVec_bvec_lemma_2]
    funext p
    rw [gent_lemma hY _ _ (by unfold SP; simp only [eI_val]; omega) (by simp only [eI_val]; omega)]
    simp [bvec, Pi.single_apply, Matrix.one_apply]
  · have ha' : a.val < l.val := ha
    have ha2 := a.isLt
    rw [mulVec_bvec_lemma_2]
    funext p
    rw [gent_lemma hY _ _ (by unfold SP; simp only [esI_val]; omega) (by simp only [esI_val]; omega)]
    simp [bvec, Pi.single_apply, Matrix.one_apply]
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
