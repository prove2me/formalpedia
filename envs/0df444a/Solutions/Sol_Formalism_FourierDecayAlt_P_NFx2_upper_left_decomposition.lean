-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.upper_left_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:24:29.276767+00:00
-- url     : https://prove2.me/submissions/d871e726-f870-4cc0-9dbc-d8be232fa17f

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (Y : ℂ) : (Q.NFData.QQ (⟨L, κ, SS⟩ : Q.NFData P A) Y) 0 0 =
    L.GGi * κ (fun ρ => M.wC P ρ Y) + upperLeftTail L κ SS Y + L.GGi * Q.NFData.S4 (⟨L, κ, SS⟩ : Q.NFData P A) Y := by
  simp only [Q.NFData.QQ, upperLeftTail, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one, Q.NFData.x, xA]
  noncomm_ring
end Formalism.FourierDecayAlt.P.NFx2
