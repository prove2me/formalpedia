-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.dpsi_e_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:22:19.476687+00:00
-- url     : https://prove2.me/submissions/f18eec27-554c-43f6-9821-2bba7da4c3e4

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
theorem _root_.solution (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (p : ℕ) (hp : p < r) (w : Fin (k + 1)) :
    dpsiP k r z' (pe k r p) (wI k r w) = if p + 1 = r then z' (wI k r w) else 0 := by
  have h1 : min p (2 * r + k) = p := by omega
  have hw : (wI k r w).val = r + w.val := rfl
  have hwk := w.isLt
  simp only [dpsiP, pe_val, h1, hw]
  rw [if_neg (by omega), if_pos (by omega)]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
