-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.pat_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:11:21.794172+00:00
-- url     : https://prove2.me/submissions/e9b853c5-35b1-454a-aad3-42273452c5ad

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_EllSingleZero

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
theorem _root_.solution (l : Fin r) (a b : Fin (2 * r + k + 1)) (c : ℂ)
    (h : (a.val = l.val ∧ l.val < b.val ∧ b.val ≤ 2 * r + k - l.val) ∨
      (b.val = 2 * r + k - l.val ∧ l.val ≤ a.val ∧ a.val < 2 * r + k - l.val)) :
    Pat k r l (Matrix.single a b c) := by
  intro i j hij
  rw [Matrix.single_apply] at hij
  split_ifs at hij with h'
  · obtain ⟨rfl, rfl⟩ := h'
    exact h
  · exact absurd rfl hij
end Formalism.FourierDecayAlt.Q.QRR
