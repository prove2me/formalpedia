-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.coordinate_shift_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:39:21.716192+00:00
-- url     : https://prove2.me/submissions/8210dcb4-446b-4ba3-864b-bab375bf8001

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_coordinate_shift_product

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
theorem _root_.solution {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (τ : M.Ty P) (Y : ℂ) :
    M.xC P τ (Y + 1) = (Y + M.rho P τ j + 1) * ∏ i ∈ Icc 1 (P.k - 1) \ {j}, (Y + (1 + (M.rho P τ i : ℂ))) := by
  rw [coordinate_shift_product, Finset.prod_eq_mul_prod_sdiff_singleton j _ (fun h => absurd hj h)]; ring
end Formalism.FourierDecayAlt.P.NFx2
