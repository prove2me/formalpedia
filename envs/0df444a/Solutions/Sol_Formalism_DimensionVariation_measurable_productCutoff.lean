-- Prove2me | solution 1 for Formalism.DimensionVariation.measurable_productCutoff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:57.667696+00:00
-- url     : https://prove2.me/submissions/8f9b7ffc-5a61-4d6c-9fd7-77588cb8108b

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet
import Theorems.Thm_Formalism_DimensionVariation_fjChi_measurable

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
theorem _root_.solution {κ : Type} [Fintype κ] (N : ℕ) : Measurable (fjChiP (κ := κ) N) := by
  show Measurable fun u : κ → ℂ => ∏ x, fjChi N (u x)
  exact Finset.measurable_prod _ fun x _ =>
    (fjChi_measurable N).comp (measurable_pi_apply x)
end Formalism.DimensionVariation
