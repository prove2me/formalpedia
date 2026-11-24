-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.connection_raising_gamma_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:39:34.190123+00:00
-- url     : https://prove2.me/submissions/6f48b652-7355-4389-b2b8-f353a4126da6

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_mGG
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_raising_constant_eq
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_NFx2_sc_GG_GGi_958e5f9477be

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (Y : ℂ) :
    L0.GG * (sc_LL h hF).m0 Y * L0.GGi = (sc_LL h hF).m0 (Y + 1) := by
  have e1b : L0.GG * (L0.ζ * L0.GGi * L0.GGi) = L0.ζ * L0.GGi := by
    calc L0.GG * (L0.ζ * L0.GGi * L0.GGi) = (L0.GG * L0.ζ) * L0.GGi * L0.GGi := by noncomm_ring
      _ = (L0.ζ * L0.GG) * L0.GGi * L0.GGi := by rw [sc_fc L0 (sc_mGG L0) (sc_mζ L0)]
      _ = L0.ζ * (L0.GG * L0.GGi) * L0.GGi := by noncomm_ring
      _ = L0.ζ * L0.GGi := by rw [L0.GG_GGi, mul_one]
  have e1 : L0.GG * star (nabDef L0 κ b) * L0.GGi = star (nabDef L0 κ b) + L0.ζ * L0.GGi := by
    rw [mul_assoc, sc_NsGGi h hF, mul_add, ← mul_assoc, L0.GG_GGi, one_mul, e1b]
  have e2 : L0.GG * (L0.ζ * L0.GGi) * L0.GGi = L0.ζ * L0.GGi := by rw [sc_GGζGGi]
  rw [connection_raising_constant_eq, connection_raising_constant_eq, mul_sub, sub_mul, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, e1, e2,
    show (Y + 1 - 1 / 2 : ℂ) = (Y - 1 / 2) + 1 by ring, add_smul, one_smul]
  abel
end Formalism.FourierDecayAlt.P.NFx2
