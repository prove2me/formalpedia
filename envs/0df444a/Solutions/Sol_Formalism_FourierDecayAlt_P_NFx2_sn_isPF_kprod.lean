-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_isPF_kprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:06:36.04209+00:00
-- url     : https://prove2.me/submissions/7024a12f-68dd-40a3-93ef-60feb1a5728d

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_kap_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_isPF_prod_smul
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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (s : Finset ℕ) (c : M.Ty P → ℕ → ℂ) :
    IsPF fun Y => κ (fun ρ => ∏ i ∈ s, (Y + c ρ i)) := by
  have e : (fun Y => κ (fun ρ => ∏ i ∈ s, (Y + c ρ i))) = fun Y => ∑ ρ, (∏ i ∈ s, (Y + c ρ i)) • proj κ ρ :=
    funext fun Y => kap_eq κ _
  rw [e]
  exact isPF_sum _ fun ρ _ => sn_isPF_prod_smul s (c ρ) (isPF_const _)
end Formalism.FourierDecayAlt.P.NFx2
