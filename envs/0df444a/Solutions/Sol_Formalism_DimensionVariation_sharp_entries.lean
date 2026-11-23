-- Prove2me | solution 1 for Formalism.DimensionVariation.sharp_entries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:46.947459+00:00
-- url     : https://prove2.me/submissions/1ba8ec07-ca55-4b32-8594-38b059dd62a7

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementCB
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_PerEmbeddingCoupledBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues (fnorm chainFun chainMat)
open CB
namespace Formalism.DimensionVariation
theorem _root_.solution : SharpEntries := by
  intro AA AA' _ Cl Cl' _ A B _ _ _ _ γ ε T G
  refine ⟨fun b L' => ?_, Fintype.sum_sigma (fun p => γ p * ‖G p‖ ^ 2)⟩
  show (∑ p, ((γ p : ℂ) * ε p ⟨b, L'⟩) • T p ⟨b, L'⟩ (G p)) =
    (∑ a, entryHom γ ε T a b (fun L => G ⟨a, L⟩)) L'
  rw [Finset.sum_apply, Fintype.sum_sigma]
  rfl
end Formalism.DimensionVariation
