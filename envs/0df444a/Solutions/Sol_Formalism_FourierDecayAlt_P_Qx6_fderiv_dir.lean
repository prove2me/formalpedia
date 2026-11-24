-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.fderiv_dir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:56:31.119478+00:00
-- url     : https://prove2.me/submissions/fa965af1-547d-41c5-b6aa-2b01ce8468d6

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_add_smul_single

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (a : Fin r) {f₁ f₂ : (Fin r → ℂ) → E} {c : Fin r → ℂ} (κ : ℂ)
    (h1 : DifferentiableAt ℝ f₁ c) (h2 : DifferentiableAt ℝ f₂ c)
    (hev : ∀ᶠ s in 𝓝 (c a), f₁ (Function.update c a s) = κ • f₂ (Function.update c a s)) (v : ℂ) :
    fderiv ℝ f₁ c (Pi.single a v) = κ • fderiv ℝ f₂ c (Pi.single a v) := by
  have l1 : HasDerivAt (fun t : ℝ => f₁ (c + t • (Pi.single a v : Fin r → ℂ))) (fderiv ℝ f₁ c (Pi.single a v)) 0 :=
    h1.hasFDerivAt.hasLineDerivAt _
  have l2 : HasDerivAt (fun t : ℝ => f₂ (c + t • (Pi.single a v : Fin r → ℂ))) (fderiv ℝ f₂ c (Pi.single a v)) 0 :=
    h2.hasFDerivAt.hasLineDerivAt _
  have ht : Tendsto (fun t : ℝ => c a + t • v) (𝓝 0) (𝓝 (c a)) := by
    have : Continuous (fun t : ℝ => c a + t • v) := by fun_prop
    simpa using this.tendsto 0
  have ev : (fun t : ℝ => f₁ (c + t • (Pi.single a v : Fin r → ℂ))) =ᶠ[𝓝 0]
      fun t : ℝ => κ • f₂ (c + t • (Pi.single a v : Fin r → ℂ)) := by
    filter_upwards [ht.eventually hev] with t h
    rw [add_smul_single]
    exact h
  exact l1.unique ((l2.const_smul κ).congr_of_eventuallyEq ev)
end Formalism.FourierDecayAlt.P.Qx6
