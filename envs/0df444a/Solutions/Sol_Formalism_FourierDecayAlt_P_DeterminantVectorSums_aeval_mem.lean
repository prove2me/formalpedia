-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DeterminantVectorSums.aeval_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:12:36.905128+00:00
-- url     : https://prove2.me/submissions/656f1b69-295e-41f5-aec3-6507ca43a40f

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StarSumLemmas
import Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantVectorSums_pow_mem

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DeterminantVectorSums
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {W : Type} [AddCommGroup W] [Module ℂ W]
namespace Formalism.FourierDecayAlt.P.DeterminantVectorSums
theorem _root_.solution (G : Submodule ℂ W) (K : Module.End ℂ W) (hK : ∀ x ∈ G, K x ∈ G) (q : ℂ[X]) :
    ∀ x ∈ G, aeval K q x ∈ G := by
  intro x hx
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  refine Submodule.sum_mem _ (fun s _ => ?_)
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (pow_mem G K hK s x hx)
end Formalism.FourierDecayAlt.P.DeterminantVectorSums
