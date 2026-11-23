-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PoissonSummationDecay.gP_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:30.509147+00:00
-- url     : https://prove2.me/submissions/b310f9cb-a38f-4351-9e15-fea4454da393

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PoissonSummationDecay
open Formalism.FourierDecayAlt.F7
open Finset Polynomial
open MeasureTheory Formalism.H
open scoped FourierTransform RealInnerProductSpace ENNReal
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type} [Fintype ι]
namespace Formalism.FourierDecayAlt.P.PoissonSummationDecay
theorem _root_.solution (π : ι → V →L[ℝ] ℂ) (c : V) : 0 < gP π c :=
  Finset.prod_pos fun v _ => by positivity
end Formalism.FourierDecayAlt.P.PoissonSummationDecay
