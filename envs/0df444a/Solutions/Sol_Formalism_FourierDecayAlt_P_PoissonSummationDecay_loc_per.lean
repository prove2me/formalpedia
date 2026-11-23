-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PoissonSummationDecay.loc_per
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:44.450137+00:00
-- url     : https://prove2.me/submissions/9b46e3be-0247-4dbc-aa6b-fca21b39acc6

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



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
theorem _root_.solution (Λ : Submodule ℤ V) (φ : V → ℂ) (l₀ : Λ) (x : V) :
    ∑' l : Λ, φ ((l:V) + ((l₀:V) + x)) = ∑' l : Λ, φ ((l:V) + x) := by
  have := (Equiv.addRight l₀).tsum_eq (fun l : Λ => φ ((l : V) + x))
  rw [← this]
  refine tsum_congr fun l => ?_
  simp only [Equiv.coe_addRight, Submodule.coe_add, add_assoc]
end Formalism.FourierDecayAlt.P.PoissonSummationDecay
