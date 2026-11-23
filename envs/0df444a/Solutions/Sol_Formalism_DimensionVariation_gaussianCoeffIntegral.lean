-- Prove2me | solution 1 for Formalism.DimensionVariation.gaussianCoeffIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:37.291967+00:00
-- url     : https://prove2.me/submissions/48d54b7f-a087-443d-aea0-dff3d50f0422

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet
import Theorems.Thm_Formalism_DimensionVariation_fjCut
import Theorems.Thm_Formalism_DimensionVariation_fjProd_integrable
import Theorems.Thm_Formalism_DimensionVariation_fjProd_diag
import Theorems.Thm_Formalism_DimensionVariation_fjIntegrable
import Theorems.Thm_Formalism_DimensionVariation_fjPolydisc

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
theorem _root_.solution : FockJet := by
  unfold FockJet
  intro κ _ F c S hF hs hg e
  have hint_r := fjIntegrable F S hF hg e
  refine ⟨hint_r, ?_⟩
  have h1 := fjCut _ hint_r
  have h2 := ((fjCut _
    (fjProd_integrable e e)).const_mul (c e)).congr
    fun N => (fjPolydisc F c hs e N).symm
  rw [tendsto_nhds_unique h1 h2, fjProd_diag]
  ring
end Formalism.DimensionVariation
