-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.hpk_W_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:23:37.93502+00:00
-- url     : https://prove2.me/submissions/586e7751-7d25-4488-bd17-9e2f42f09c8e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DpsiIsDerivation
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val



set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (w p : Fin (2 * r + k + 1)) (hw : r ≤ w.val ∧ w.val ≤ r + k) :
    Hpk k r p w = if p = w then Hpk k r w w else 0 := by
  by_cases hpw : p = w
  · subst hpw
    simp
  · rw [if_neg hpw]
    have hp := p.isLt
    unfold Hpk
    rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => hpw h.2.2)]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
