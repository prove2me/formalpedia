-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.fvec_es
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:49:32.719257+00:00
-- url     : https://prove2.me/submissions/76638903-9d87-4bf8-bad4-48019c250da3

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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (l : Fin r) :
    fvec k r z l.succ (esI k r l) = 0 := by
  have hl := l.isLt
  unfold fvec
  split_ifs with h
  · simp only [bvec, Pi.single_apply]
    rw [if_neg]
    intro h'
    have h'' := congrArg Fin.val h'
    simp only [eI, esI, Fin.val_succ] at h'' h
    omega
  · apply hz
    right
    show r + k < 2 * r + k - l.val
    omega
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
