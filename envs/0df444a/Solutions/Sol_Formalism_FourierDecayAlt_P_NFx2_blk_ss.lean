-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.blk_ss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:17:42.187953+00:00
-- url     : https://prove2.me/submissions/c0049ad5-713a-4124-906e-1690a34c30ac

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_pj_orth
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_ss_pj_none
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_ss_pj_up

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
theorem _root_.solution {SS : ℕ → A} (hR : Raises κ SS) (l : ℕ) : GlobalTheory κ (M.Up P l) (SS l) := by
  intro σ τ h
  by_cases hτ : ∃ τ', M.Up P l τ τ'
  · obtain ⟨τ', hτ'⟩ := hτ
    have hne : σ ≠ τ' := fun e => h (e ▸ hτ')
    rw [mul_assoc, ← ss_pj_up κ hR hτ', ← mul_assoc, pj_orth κ hne, zero_mul]
  · rw [mul_assoc, ss_pj_none κ hR hτ, mul_zero]
end Formalism.FourierDecayAlt.P.NFx2
