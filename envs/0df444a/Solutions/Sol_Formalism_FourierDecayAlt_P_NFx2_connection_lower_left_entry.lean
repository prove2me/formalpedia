-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.connection_lower_left_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:13:57.68205+00:00
-- url     : https://prove2.me/submissions/60be486c-107f-4f6b-aa45-564ed9f8b754

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq

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
    (Q.NFData.QQ (⟨sc_LL h hF, κ, SS⟩ : Q.NFData P A) Y) 1 0 =
      L0.GG * xA κ Y * (sc_LL h hF).l0 Y + ∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ Y) := rfl
end Formalism.FourierDecayAlt.P.NFx2
