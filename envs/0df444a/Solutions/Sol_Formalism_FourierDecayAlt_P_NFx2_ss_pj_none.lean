-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.ss_pj_none
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:31:23.034742+00:00
-- url     : https://prove2.me/submissions/b3a8a892-40c9-4872-8719-2a200a2e9294

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq

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
theorem _root_.solution {SS : ℕ → A} (hR : Raises κ SS) {l : ℕ} {ρ : M.Ty P} (h : ¬ ∃ ρ', M.Up P l ρ ρ') :
    SS l * proj κ ρ = 0 := by
  have := hR l (fun x => if x = ρ then 1 else 0) 0 (by
    intro a b hab
    simp only [Pi.zero_apply]
    split_ifs with hh
    · subst hh; exact absurd ⟨b, hab⟩ h
    · rfl)
  rw [map_zero, zero_mul] at this
  exact this.symm
end Formalism.FourierDecayAlt.P.NFx2
