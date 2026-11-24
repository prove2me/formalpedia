-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScalarCastIdentities.MC_signed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:52:08.315157+00:00
-- url     : https://prove2.me/submissions/a23e69a2-f6a0-49be-8595-05cd5b37022d

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
theorem _root_.solution (hM : MinorCov) (hE : GlRel E) (η : Fin t → A) (hη : IsCov E η) (u : ℂ) (q p i : Fin t) :
    mS E q p u * η i - η i * mS E q p u = ∑ a, nS E a q i p u * η a := by
  have h := hM A t E η hE hη u q p i
  have a1 : mS E q p u * η i - η i * mS E q p u = ((-1 : ℂ) ^ ((q : ℕ) + (p : ℕ))) •
      (qminor E (skip1 q) (skip1 p) u * η i - η i * qminor E (skip1 q) (skip1 p) u) := by
    unfold mS
    rw [smul_mul_assoc, mul_smul_comm, smul_sub]
  rw [a1, h]
  by_cases hi : i = p
  · rw [if_pos hi, smul_zero]
    symm
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [nS, if_pos (Or.inr hi), zero_mul]
  · rw [if_neg hi, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a = q
    · rw [if_pos ha, nS, if_pos (Or.inl ha), smul_zero, zero_mul]
    · rw [if_neg ha, nS, if_neg (by tauto), cast_mul_eq_smul, smul_smul, smul_mul_assoc]
      congr 1
      push_cast
      ring
end Formalism.FourierDecayAlt.P.ScalarCastIdentities
