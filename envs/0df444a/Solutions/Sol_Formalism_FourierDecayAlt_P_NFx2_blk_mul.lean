-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.blk_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:59:26.182039+00:00
-- url     : https://prove2.me/submissions/a4789001-c0d0-4d73-951e-655609bb5b48

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_expand

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (κ : (M.Ty P → ℂ) →ₐ[ℂ] A)
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution {R S : M.Ty P → M.Ty P → Prop} {X Y : A} (hX : GlobalTheory κ R X) (hY : GlobalTheory κ S Y) :
    GlobalTheory κ (fun τ σ => ∃ μ, S τ μ ∧ R μ σ) (X * Y) := by
  intro σ τ h
  rw [blk_expand]
  refine Finset.sum_eq_zero fun μ _ => ?_
  by_cases h1 : S τ μ
  · have h2 : ¬ R μ σ := fun h2 => h ⟨μ, h1, h2⟩
    rw [hX σ μ h2, zero_mul]
  · rw [hY μ τ h1, mul_zero]
end Formalism.FourierDecayAlt.P.NFx2
