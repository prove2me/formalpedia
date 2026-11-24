-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:58:39.895788+00:00
-- url     : https://prove2.me/submissions/cebcffe8-952e-40e3-bb1b-ee0e73ebb86c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainFirstIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightDerivativeRulePsi
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_hpk_row_eI
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
theorem _root_.solution {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) v (bvec (eI k r b)) = v (esI k r b) := by
  have h1 : herm (Hpk k r) v (bvec (eI k r b)) = ∑ p, Hpk k r (eI k r b) p * v p := by
    have hs : star (bvec (eI k r b)) = bvec (eI k r b) := by
      ext i
      by_cases h : i = eI k r b <;> simp [bvec, Pi.single_apply, h]
    unfold herm
    rw [hs]
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [h1]
  simp_rw [hpk_row_eI]
  rw [Finset.sum_eq_single (esI k r b)]
  · simp [esI]
  · intro p _ hp
    rw [if_neg, zero_mul]
    intro h
    exact hp (Fin.ext (by simp [esI, h]))
  · simp
end Formalism.FourierDecayAlt.P.SignAntidiagonal
