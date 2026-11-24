-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_e_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:22:57.303987+00:00
-- url     : https://prove2.me/submissions/e7dfea93-ed0d-41ab-8465-cc542b2e9e16

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
theorem _root_.solution (l : ℕ) (τ : M.Ty P) :
    sn_e P τ l ((-(M.rho P τ l) - 1 : ℝ) : ℂ) =
      (((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (M.rho P τ j - M.rho P τ l)) *
        ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (M.rho P τ j - M.rho P τ l - 1) : ℝ) : ℂ) := by
  unfold sn_e
  rw [Finset.sdiff_singleton_eq_erase, mul_comm]
  push_cast
  congr 1 <;> exact Finset.prod_congr rfl fun i _ => by ring
end Formalism.FourierDecayAlt.P.NFx2
