-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FreeActionExpansion.pair_eq_sum_split_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:22:13.465805+00:00
-- url     : https://prove2.me/submissions/001b58b8-21d9-4fb5-833f-0ebc8667c0d3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionUpdateSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeActionExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_CoordinateFlipUpdateSums_sum_position


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FreeActionExpansion
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
open scoped Matrix
variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S]
  [DecidableEq S] [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
namespace Formalism.FourierDecayAlt.P.FreeActionExpansion
theorem _root_.solution (a : S) (ρ : Rep A V) (Ψ Ψ' : Ix S → V) :
    pair ρ Ψ Ψ' = ∑ u, if u a = 0 then ρ.β (Ψ u) (Ψ' u) +
      ρ.β (Ψ (Function.update u a 1)) (Ψ' (Function.update u a 1)) else 0 :=
  sum_position a (fun u => ρ.β (Ψ u) (Ψ' u))
end Formalism.FourierDecayAlt.P.FreeActionExpansion
