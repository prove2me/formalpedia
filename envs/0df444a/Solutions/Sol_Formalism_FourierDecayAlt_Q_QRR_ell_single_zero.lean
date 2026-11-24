-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.ell_single_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:03:22.359915+00:00
-- url     : https://prove2.me/submissions/59db26b8-9386-43fa-8b12-da79091aeaf5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_EllSingleZero
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_QRR_mulVec_single__2f731049bd4a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.QRR
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (a b : Fin (2 * r + k + 1)) (c : ℂ)
    (hb : r ≤ b.val) (hzb : z b = 0) : ell k r z (Matrix.single a b c) = 0 := by
  unfold ell
  apply Finset.sum_eq_zero
  intro a' _
  split_ifs with h
  · rw [Matrix.single_apply, if_neg]
    rintro ⟨-, hb'⟩
    have h' := congrArg Fin.val hb'
    simp only [eI] at h'
    omega
  · rw [mulVec_single', hzb]
    simp
end Formalism.FourierDecayAlt.Q.QRR
