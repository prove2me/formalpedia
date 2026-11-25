-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QrD.dRep_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:21:03.648611+00:00
-- url     : https://prove2.me/submissions/31e81430-5811-4ec8-9606-d81f40caff1e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneParameterDifferentiable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightTypeAction
import Theorems.Thm_Formalism_FourierDecayAlt_P_QrD_dOp_hasDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.QrD
variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
variable [FiniteDimensional ℂ W] {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}
namespace Formalism.FourierDecayAlt.P.QrD
theorem _root_.solution (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {X : Mx k r}
    (hX : InLieW k r z X) (v : W) : dRep π X v = dOp π X v := by
  have h := dOp_hasDeriv hπ hc hX
  have h2 : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) v) (dOp π X v) 0 := by
    have := ((ContinuousLinearMap.apply ℂ W v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    simpa [Function.comp_def] using this
  unfold dRep
  exact h2.deriv
end Formalism.FourierDecayAlt.P.QrD
