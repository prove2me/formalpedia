-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.lower_sum_block_structure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:37:01.554625+00:00
-- url     : https://prove2.me/submissions/f1cdc171-d0b7-413f-ad85-3426d4019467

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_ss
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_kap

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
theorem _root_.solution (hR : Raises κ SS) (Y : ℂ) :
    GlobalTheory κ (fun τ σ => ∃ j ∈ Icc 1 (P.k - 1), M.Up P j τ σ)
      (∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ Y)) := by
  refine blk_sum κ _ fun j hj => ?_
  refine blk_mono κ (blk_mul κ (blk_ss κ hR j) (blk_kap κ _)) ?_
  rintro τ σ ⟨μ, rfl, hμ⟩; exact ⟨j, hj, hμ⟩
end Formalism.FourierDecayAlt.P.NFx2
