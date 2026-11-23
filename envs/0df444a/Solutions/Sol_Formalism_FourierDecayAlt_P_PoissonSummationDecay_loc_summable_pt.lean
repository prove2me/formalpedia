-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PoissonSummationDecay.loc_summable_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:04.673805+00:00
-- url     : https://prove2.me/submissions/f19ea078-2697-4aa8-9dcc-1ab7efc57f86

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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]
omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] [InnerProductSpace ℝ V]
namespace Formalism.FourierDecayAlt.P.PoissonSummationDecay
theorem _root_.solution (Λ : Submodule ℤ V) (φ : V → ℂ) (h : LocSummable Λ φ) (x : V) :
    Summable (fun l : Λ => φ ((l:V) + x)) := by
  obtain ⟨b, hb, hbd⟩ := h {x} isCompact_singleton
  exact Summable.of_norm_bounded hb (fun l => hbd l x rfl)
end Formalism.FourierDecayAlt.P.PoissonSummationDecay
