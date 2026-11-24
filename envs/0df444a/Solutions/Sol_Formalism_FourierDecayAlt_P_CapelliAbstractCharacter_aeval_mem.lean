-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.aeval_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:36:34.444441+00:00
-- url     : https://prove2.me/submissions/cf4fa09e-9617-4caf-87cb-19c1dc8b993e

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_pow_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
theorem _root_.solution {W : Type} [AddCommGroup W] [Module ℂ W] (G : Submodule ℂ W) (K : Module.End ℂ W)
    (hK : ∀ X ∈ G, K X ∈ G) (p : ℂ[X]) : ∀ X ∈ G, Polynomial.aeval K p X ∈ G := by
  intro X hX
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  refine G.sum_mem (fun i _ => ?_)
  rw [LinearMap.smul_apply]
  exact G.smul_mem _ (Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.pow_mem G K hK i X hX)
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
