-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.mul_hpk_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:37:00.308045+00:00
-- url     : https://prove2.me/submissions/9f59bf48-9e48-4706-b175-4635bebfcd8b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DpsiIsDerivation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangularFactorMiddleRow
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_hpk_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_row
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
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p q : Fin (2 * r + k + 1)) :
    (M * Hpk k r) p q = M p (tau k r q) * WeylGroupFacts.sgn k r q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r q)]
  · rw [hpk_symm, hpk_row, if_pos rfl]
  · intro m _ hm; rw [hpk_symm, hpk_row, if_neg hm, mul_zero]
  · simp
end Formalism.FourierDecayAlt.P.SignAntidiagonal
