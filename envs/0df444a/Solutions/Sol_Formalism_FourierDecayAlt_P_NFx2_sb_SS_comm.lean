-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sb_SS_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:59:53.019806+00:00
-- url     : https://prove2.me/submissions/55819ac1-eda6-4ff4-a4be-76094d5a983e

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_T_comm

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L0 : PreLevel A P.r}
  {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (h : SHyp P L0 QQ κ) (l : ℕ) : ∀ g ∈ L0.ops, Commute (sb_SS κ QQ l) g := by
  intro g hg
  unfold sb_SS
  refine Commute.sum_left _ _ _ fun ρ _ => Commute.sum_left _ _ _ fun σ _ => ?_
  split_ifs with hc
  · have hne : σ ≠ ρ := fun e => up_ne P hc.1 hc.2 e.symm
    exact (sb_T_comm h hne regular_base_point g hg).smul_left _
  · exact Commute.zero_left g
end Formalism.FourierDecayAlt.P.NFx2
