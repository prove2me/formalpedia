-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.type_eq_of_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:22:39.088585+00:00
-- url     : https://prove2.me/submissions/6eb1b0f3-1489-4946-8fc1-fd910638cf84

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_idx_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_ty_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_xC_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_xC_root

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
theorem _root_.solution (hP : P.OK) {σ ρ : M.Ty P} (hx : ∀ u, M.xC P σ u = M.xC P ρ u) : σ = ρ := by
  apply ty_ext P
  intro i hi
  have h0 : M.xC P σ (-((M.rho P ρ i : ℝ) : ℂ)) = 0 := by rw [hx]; exact sb_xC_root ρ hi
  obtain ⟨j, hj, e⟩ := sb_xC_zero h0
  have e' : M.rho P ρ i = M.rho P σ j := by exact_mod_cast neg_injective e
  have := idx_eq P hP ρ σ hi hj e'
  subst this; exact e'.symm
end Formalism.FourierDecayAlt.P.NFx2
