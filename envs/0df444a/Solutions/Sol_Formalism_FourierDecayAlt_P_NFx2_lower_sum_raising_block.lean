-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.lower_sum_raising_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:37:12.761093+00:00
-- url     : https://prove2.me/submissions/06f011c6-9ebb-4335-b533-83373be775e9

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_up_idx
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_pj_ss_pj
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_ss
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_lower_sum_block_entry

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
theorem _root_.solution (hR : Raises κ SS) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P} (hu : M.Up P l ρ ρ') (Y : ℂ) :
    proj κ ρ' * (∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ Y)) * proj κ ρ =
      M.xEx P {l} ρ Y • (SS l * proj κ ρ) := by
  rw [lower_sum_block_entry hR, Finset.sum_eq_single l, pj_ss_pj κ hR hu]
  · intro j hj hjl; rw [blk_ss κ hR j ρ' ρ (fun hu' => hjl (up_idx P hj hl hu' hu)), smul_zero]
  · intro hn; exact absurd hl hn
end Formalism.FourierDecayAlt.P.NFx2
