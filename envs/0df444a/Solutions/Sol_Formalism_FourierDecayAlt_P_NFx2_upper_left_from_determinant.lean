-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.upper_left_from_determinant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:22:49.689638+00:00
-- url     : https://prove2.me/submissions/03103a4b-3eaf-4954-952e-60d114d8655c

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
theorem _root_.solution {t11 t12 t21 t21' τ τ' τi τi' q : A} (hD3 : t11 * τ' - t12 * t21' = q)
    (hD4 : t21 * τ' = τ * t21') (h1 : τ' * τi' = 1) (h2 : τi * τ = 1) : t11 = q * τi' + t12 * τi * t21 := by
  calc t11 = t11 * τ' * τi' := by rw [mul_assoc, h1, mul_one]
    _ = (q + t12 * t21') * τi' := by rw [← hD3]; noncomm_ring
    _ = q * τi' + t12 * (τi * τ) * t21' * τi' := by rw [h2]; noncomm_ring
    _ = q * τi' + t12 * τi * (τ * t21') * τi' := by noncomm_ring
    _ = q * τi' + t12 * τi * t21 * (τ' * τi') := by rw [← hD4]; noncomm_ring
    _ = q * τi' + t12 * τi * t21 := by rw [h1, mul_one]
end Formalism.FourierDecayAlt.P.NFx2
