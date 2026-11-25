-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.Tm_Emir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:28:58.897845+00:00
-- url     : https://prove2.me/submissions/89adbb21-8ce4-4818-aed5-85b0c1b91767

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHeadV
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_ep_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_rv_rv
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal
variable {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (v : ℂ) (p q : Fin (2 * r + k + 1)) :
    Tm (Emir E) v p q = (ep p * ep q) • Tm (Formalism.FourierDecayAlt.P.Qx5.Eop E) v (rv p) (rv q) := by
  by_cases h : p = q
  · subst q
    simp only [Tm, Emir, Formalism.FourierDecayAlt.P.Qx5.Eop, if_true, ep_sq, one_smul]
  · have h' : ¬ rv p = rv q := fun e => h (by rw [← rv_rv p, e, rv_rv])
    simp only [Tm, Emir, Formalism.FourierDecayAlt.P.Qx5.Eop, h, h', if_false, zero_add, smul_neg]
end Formalism.FourierDecayAlt.P.PBG
