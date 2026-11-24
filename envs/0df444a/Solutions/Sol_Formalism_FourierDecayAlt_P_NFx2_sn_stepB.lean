-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_stepB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:44:06.971863+00:00
-- url     : https://prove2.me/submissions/cd4d0d5b-a7aa-495d-90fd-05ba48314a4a

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_kap_mul_pj
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_kxi_ss

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
theorem _root_.solution (hR : Raises κ SS) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (τ : M.Ty P) (Y : ℂ) :
    (L.GGi * xiA κ Y) * (SS j * proj κ τ) =
      ((Y + M.rho P τ j + 1) * M.xEx P {j} τ Y)⁻¹ • (L.GGi * (SS j * proj κ τ)) := by
  rw [mul_assoc, ← mul_assoc (xiA κ Y), sn_kxi_ss hR hj, mul_assoc, kap_mul_pj, mul_smul_comm, mul_smul_comm]
end Formalism.FourierDecayAlt.P.NFx2
