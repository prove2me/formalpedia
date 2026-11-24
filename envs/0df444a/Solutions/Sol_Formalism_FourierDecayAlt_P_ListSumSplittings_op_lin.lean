-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumSplittings.op_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:14:25.270568+00:00
-- url     : https://prove2.me/submissions/28d8f314-8c7b-412c-83a0-b635fca3e2ce

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_hasDerivAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumSplittings
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic Formalism.FourierDecayAlt.P.ListSumInequalities
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumSplittings
theorem _root_.solution (ℓ : Mat k r →ₗ[ℝ] ℂ) (b : Bool) (X : Mat k r) :
    op b X (fun g => ℓ g) = fun g => (ℓ.comp (vf b X).toLinearMap) g := by
  funext g
  have hd : HasDerivAt (fun t : ℝ => ℓ (cv b X t g)) (ℓ (vf b X g)) 0 := by
    have h := (LinearMap.toContinuousLinearMap ℓ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (cv_hasDerivAt b X g)
    exact h
  show deriv (fun t : ℝ => ℓ (cv b X t g)) 0 = _
  rw [hd.deriv]; rfl
end Formalism.FourierDecayAlt.P.ListSumSplittings
