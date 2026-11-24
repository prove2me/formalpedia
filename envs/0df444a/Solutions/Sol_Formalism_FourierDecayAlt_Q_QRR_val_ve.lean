-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.val_ve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:15:53.857959+00:00
-- url     : https://prove2.me/submissions/8a1aec69-57ed-4c49-b65d-6663ecfc053e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_EllSingleZero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_ell_single_zero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_ell_single_row
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_dag_single
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_tau_esI
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_sgn_eI
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_star_sgn
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_esI_zero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_esI_ge
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_herm_bvec_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}
private lemma tau_val_lemma (i : Fin (2 * r + k + 1)) :
    (WeylGroupFacts.tau k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := rfl
private lemma sgn_tau_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.sgn k r (WeylGroupFacts.tau k r i) = WeylGroupFacts.sgn k r i := by
  have hi := i.isLt
  unfold WeylGroupFacts.sgn
  simp only [tau_val_lemma]
  split_ifs <;> first | rfl | omega
end Formalism.FourierDecayAlt.Q.QRR
end
end

set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.QRR
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (l : Fin r) (j : Fin (mdim k r l.succ)) :
    ell k r z (Matrix.single (posL k r l.succ j) (esI k r l) 1) +
      star (ell k r z (dag k r (Matrix.single (posL k r l.succ j) (esI k r l) 1))) = xbv k r z l.succ j := by
  have hc : WeylGroupFacts.sgn k r (eI k r l) * star (1 : ℂ) * WeylGroupFacts.sgn k r (WeylGroupFacts.tau k r (posL k r l.succ j)) =
      WeylGroupFacts.sgn k r (posL k r l.succ j) := by
    rw [sgn_eI, star_one, one_mul, one_mul, sgn_tau_lemma]
  rw [ell_single_zero z _ _ _ (esI_ge l) (esI_zero z hz l), zero_add, dag_single, tau_esI, hc,
    ell_single_row]
  unfold xbv
  rw [herm_bvec_left]
  unfold fvec
  by_cases h : l.val + 1 < r
  · rw [dif_pos h, dif_pos (show l.succ.val < r from h)]
    simp only [bvec, Pi.single_apply]
    split_ifs with h1 h2 h3
    all_goals first
      | exact absurd h1 h2
      | exact absurd h3 h1
      | (rw [star_one, one_mul, star_sgn])
      | simp
  · rw [dif_neg h, dif_neg (show ¬ l.succ.val < r from h), star_mul', star_sgn, mul_comm]
end Formalism.FourierDecayAlt.Q.QRR
