-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.lower_sum_mul_projection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:21:24.596807+00:00
-- url     : https://prove2.me/submissions/d80d60fa-742d-4ee4-9cc3-d3e52848382a

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_kap_mul_pj

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
theorem _root_.solution (τ : M.Ty P) (Y : ℂ) :
    Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y * proj κ τ =
      ∑ j ∈ Icc 1 (P.k - 1), M.xEx P {j} τ Y • (SS j * proj κ τ) := by
  unfold Q.NFData.weightedSumBis
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only
  rw [mul_assoc, kap_mul_pj, mul_smul_comm]
end Formalism.FourierDecayAlt.P.NFx2
