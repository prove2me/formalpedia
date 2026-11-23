-- Prove2me | solution 1 for Formalism.DimensionVariation.fjW_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:59.976263+00:00
-- url     : https://prove2.me/submissions/15586847-b907-4ead-99a6-587590dcd68b

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
open scoped ComplexConjugate Real Nat
noncomputable section
open Formalism Formalism.DimensionVariation
namespace Formalism.DimensionVariation
theorem _root_.solution (a b : ℕ) : Continuous (fjW a b) := by
  show Continuous fun z : ℂ => z ^ a * conj z ^ b * (Real.exp (-‖z‖ ^ 2) : ℂ)
  exact ((continuous_id.pow a).mul (Complex.continuous_conj.pow b)).mul
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_norm.pow 2).neg))
end Formalism.DimensionVariation
