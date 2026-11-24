-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.dpsi_middle_last_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:01:27.529837+00:00
-- url     : https://prove2.me/submissions/2b6f63ef-db3d-46db-91ba-1fae5c461470

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
theorem _root_.solution (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (l : ℕ) (hl : l < r) (w : Fin (k + 1)) :
    dpsiP k r z' (wI k r w) (ps k r l) = if l + 1 = r then herm (Hpk k r) (bvec (wI k r w)) z' else 0 := by
  have hw : (wI k r w).val = r + w.val := rfl
  have hwk := w.isLt
  simp only [dpsiP, ps_val, hw]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  simp only [show (2 * r + k - l = r + k + 1) ↔ (l + 1 = r) by omega]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
