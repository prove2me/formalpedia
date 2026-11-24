-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.upper_sum_block_structure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:40:12.307012+00:00
-- url     : https://prove2.me/submissions/2bc6a5e4-1bf0-43e4-8212-2c23608949b7

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_H_pj_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_star
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
theorem _root_.solution (h : SHyp P L0 QQ κ) (hR : Raises κ SS) (Y : ℂ) :
    GlobalTheory κ (fun τ σ => ∃ j ∈ Icc 1 (P.k - 1), M.Up P j σ τ)
      (∑ l ∈ Icc 1 (P.k - 1), (κ fun ρ => M.xEx P {l} ρ Y) * star (SS l)) := by
  refine blk_sum κ _ fun j hj => ?_
  refine blk_mono κ (blk_mul κ (blk_kap κ _) (blk_star κ (H_pj_star h) (blk_ss κ hR j))) ?_
  rintro τ σ ⟨μ, hμ, rfl⟩; exact ⟨j, hj, hμ⟩
end Formalism.FourierDecayAlt.P.NFx2
