-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sc_star_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:24:26.078526+00:00
-- url     : https://prove2.me/submissions/d43488a5-f250-47f3-8c89-b2b380b51540

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution {Y : ℂ} (hY : star Y = Y) (s : Finset ℕ) (g : ℕ → ℝ) :
    star (∏ i ∈ s, (Y + (g i : ℂ))) = ∏ i ∈ s, (Y + (g i : ℂ)) := by
  rw [show star (∏ i ∈ s, (Y + (g i : ℂ))) = starRingEnd ℂ (∏ i ∈ s, (Y + (g i : ℂ))) from rfl, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_add, Complex.conj_ofReal]
  congr 1
end Formalism.FourierDecayAlt.P.NFx2
