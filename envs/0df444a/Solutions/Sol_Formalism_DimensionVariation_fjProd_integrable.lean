-- Prove2me | solution 1 for Formalism.DimensionVariation.fjProd_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:14.945891+00:00
-- url     : https://prove2.me/submissions/041587bf-93e4-4c0e-8510-584c7d8ee5df

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet
import Theorems.Thm_Formalism_DimensionVariation_fjW_integrable
import Theorems.Thm_Formalism_DimensionVariation_fjProd

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
theorem _root_.solution {κ : Type} [Fintype κ] (a b : κ → ℕ) :
    Integrable (fun u : κ → ℂ => mono u a * mono (cj u) b * (Real.exp (-(nsq u)) : ℂ)) := by
  simp_rw [fjProd]
  exact Integrable.fintype_prod (f := fun x (z : ℂ) => fjW (a x) (b x) z)
    fun x => fjW_integrable _ _
end Formalism.DimensionVariation
