-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.lower_sum_square_raising_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:57:28.994353+00:00
-- url     : https://prove2.me/submissions/6c139545-93bf-4d26-be94-5bc0d00c40d6

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_not_up_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_lower_sum_block_structure

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
theorem _root_.solution (hR : Raises κ SS) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P} (hu : M.Up P l ρ ρ')
    (u v : ℂ) :
    proj κ ρ' * ((∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ u)) *
      (∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ v))) * proj κ ρ = 0 := by
  refine blk_mul κ (lower_sum_block_structure hR u) (lower_sum_block_structure hR v) ρ' ρ ?_
  rintro ⟨μ, ⟨i, hi, h1⟩, ⟨j, hj, h2⟩⟩
  exact not_up_up P hi hj hl h1 h2 hu
end Formalism.FourierDecayAlt.P.NFx2
