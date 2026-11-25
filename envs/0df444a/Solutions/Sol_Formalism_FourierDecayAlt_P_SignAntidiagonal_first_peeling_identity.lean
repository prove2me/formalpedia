-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.first_peeling_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:28.851621+00:00
-- url     : https://prove2.me/submissions/4abf3ee2-e34f-4b56-a32c-bcece5aa3293

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPolynomialExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstPeelingMinorMemIdeal
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_first_peeling_minor_mem_ideal
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_succAbove_val

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
theorem _root_.solution : PeelingOmittedColumn := by
  intro A _ _ k r z' E m hm i u
  have e1 : ∀ (j : ℕ) (hj : j ≤ r), xR k r j hj = fun l : Fin j => pe k r l.val := by
    intro j hj
    funext l
    apply Fin.ext
    simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE, pe_val]
    have := l.isLt
    omega
  have e2 : (fun l : Fin m => xR k r (m + 1) hm (i.succAbove l)) =
      fun l : Fin m => pe k r (if l.val < i.val then l.val else l.val + 1) := by
    funext l
    apply Fin.ext
    simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE, pe_val, succAbove_val]
    have := l.isLt
    split_ifs <;> omega
  rw [e2, e1, e1]
  exact first_peeling_minor_mem_ideal k r z' E u m i.val (by have := i.isLt; omega) hm
end Formalism.FourierDecayAlt.P.SignAntidiagonal
