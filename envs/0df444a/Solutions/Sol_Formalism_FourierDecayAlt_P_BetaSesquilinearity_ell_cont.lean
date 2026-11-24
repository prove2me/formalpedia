-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.ell_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:37:13.675029+00:00
-- url     : https://prove2.me/submissions/d489e4f1-76fd-4c50-936a-9c8e2b363c43

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) : Continuous fun n : Mt k r => ell k r z (Matrix.of n) := by
  unfold ell
  refine continuous_finsetSum _ fun a _ => ?_
  by_cases h : a.val + 1 < r
  · simp only [h, dite_true]
    exact (continuous_apply _).comp (continuous_apply _)
  · simp only [h, dite_false]
    unfold Matrix.mulVec dotProduct
    refine continuous_finsetSum _ fun j _ => ?_
    have : Continuous fun n : Mt k r => n (eI k r a) j := (continuous_apply j).comp (continuous_apply (eI k r a))
    exact this.mul continuous_const
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
