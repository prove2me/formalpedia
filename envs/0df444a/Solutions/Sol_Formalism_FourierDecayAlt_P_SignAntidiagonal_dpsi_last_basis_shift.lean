-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.dpsi_last_basis_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:22:20.679373+00:00
-- url     : https://prove2.me/submissions/bec966bc-074b-4149-b92c-70960e2230cc

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstPeelingMinorMemIdeal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPeelingMinorMemIdeal
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
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (a b : ℕ) (ha : a < r) (hb : b < r) :
    dpsiP k r z' (ps k r a) (ps k r b) = if b + 1 = a then 1 else 0 := by
  have c1 : ¬(2 * r + k - a < r ∧ 2 * r + k - b < r) := by omega
  have c2 : ¬(2 * r + k - a < r ∧ r ≤ 2 * r + k - b ∧ 2 * r + k - b ≤ r + k) := by omega
  have c3 : ¬(r ≤ 2 * r + k - a ∧ 2 * r + k - a ≤ r + k ∧ r + k < 2 * r + k - b) := by omega
  have c4 : r + k < 2 * r + k - a ∧ r + k < 2 * r + k - b := by omega
  have c5 : (2 * r + k - b = 2 * r + k - a + 1) ↔ (b + 1 = a) := by omega
  have c6 : ¬(2 * r + k - a ≤ r + k) := by omega
  simp only [dpsiP, ps_val, c1, c2, c3, c4, c5, c6, if_false, if_true, and_self, and_false, false_and, and_true]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
