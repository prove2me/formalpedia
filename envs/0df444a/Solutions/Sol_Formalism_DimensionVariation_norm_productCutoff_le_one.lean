-- Prove2me | solution 1 for Formalism.DimensionVariation.norm_productCutoff_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:19.108469+00:00
-- url     : https://prove2.me/submissions/238b6f44-610f-42e2-9f54-2312fce256e0

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet
import Theorems.Thm_Formalism_DimensionVariation_fjChi_norm_le

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
theorem _root_.solution {κ : Type} [Fintype κ] (N : ℕ) (u : κ → ℂ) : ‖fjChiP N u‖ ≤ 1 := by
  rw [fjChiP, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun x _ => fjChi_norm_le N (u x)
end Formalism.DimensionVariation
