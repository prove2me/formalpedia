-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScalarCastIdentities.J_signed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:33:49.170879+00:00
-- url     : https://prove2.me/submissions/92f248ec-5cef-4c84-8790-d80cda172e59

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant
import Theorems.Thm_Formalism_FourierDecayAlt_P_ScalarCastIdentities_cast_mul_eq_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ScalarCastIdentities
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {A : Type} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A)
namespace Formalism.FourierDecayAlt.P.ScalarCastIdentities
theorem _root_.solution (hJ : QJacobi) (hE : GlRel E) (u : ℂ) (i q l p : Fin t) :
    mS E i l (u + 1) * mS E q p u - mS E q l (u + 1) * mS E i p u = qdet E (u + 1) * nS E i q l p u := by
  have h := hJ A t E hE u i q l p
  have a1 : mS E i l (u + 1) * mS E q p u = ((-1 : ℂ) ^ ((i : ℕ) + (q : ℕ) + (l : ℕ) + (p : ℕ))) •
      (qminor E (skip1 i) (skip1 l) (u + 1) * qminor E (skip1 q) (skip1 p) u) := by
    unfold mS
    rw [smul_mul_smul_comm]
    congr 1
    ring
  have a2 : mS E q l (u + 1) * mS E i p u = ((-1 : ℂ) ^ ((i : ℕ) + (q : ℕ) + (l : ℕ) + (p : ℕ))) •
      (qminor E (skip1 q) (skip1 l) (u + 1) * qminor E (skip1 i) (skip1 p) u) := by
    unfold mS
    rw [smul_mul_smul_comm]
    congr 1
    ring
  rw [a1, a2, ← smul_sub, h, nS]
  by_cases hc : i = q ∨ l = p
  · rw [if_pos hc, if_pos hc, smul_zero, mul_zero]
  · rw [if_neg hc, if_neg hc, cast_mul_eq_smul, mul_smul_comm, smul_smul]
    congr 1
    push_cast
    ring
end Formalism.FourierDecayAlt.P.ScalarCastIdentities
