-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.exp_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:03:22.108668+00:00
-- url     : https://prove2.me/submissions/402e07e6-8dff-4d6d-84e4-1d4701641883

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_hasDerivAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx3
theorem _root_.solution {X : Mx k r} {v : Fin (2 * r + k + 1) → ℂ} (h : X *ᵥ v = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) *ᵥ v = v := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => mulVecL v ((1 : Mx k r) * NormedSpace.exp ((s : ℂ) • X))) 0 s := by
    intro s
    have h1 := B5.curve_hasDerivAt (1 : Mx k r) X s
    have h2 := (mulVecL v).hasFDerivAt.comp_hasDerivAt s h1
    refine h2.congr_deriv ?_
    show ((1 : Mx k r) * NormedSpace.exp ((s : ℂ) • X) * X) *ᵥ v = 0
    rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa [mulVecL, NormedSpace.exp_zero] using hc
end Formalism.FourierDecayAlt.P.Qx3
