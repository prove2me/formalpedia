-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sc_isPF_kap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:54:03.489808+00:00
-- url     : https://prove2.me/submissions/8bcd7b49-68d1-4faf-a856-8cef42fc5dfa

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_kap_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_cpoly
import Theorems.Thm_UpperTheory_Reformulated_B_IsPFSum_isPF_sum


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
theorem _root_.solution (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (g : M.Ty P → ℕ → ℂ) (s : M.Ty P → Finset ℕ) :
    IsPF fun Y => κ (fun ρ => ∏ i ∈ s ρ, (Y + g ρ i)) := by
  have e : ∀ Y, κ (fun ρ => ∏ i ∈ s ρ, (Y + g ρ i)) =
      ∑ ρ, (∏ i ∈ s ρ, (Polynomial.X + Polynomial.C (g ρ i))).eval Y • proj κ ρ := by
    intro Y; rw [kap_eq]; refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Polynomial.eval_prod]; simp
  simp_rw [e]
  exact isPF_sum _ fun ρ _ => isPF_cpoly _ _
end Formalism.FourierDecayAlt.P.NFx2
