-- Prove2me | solution 1 for Formalism.DimensionVariation.coupled_bound_lemma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:26:38.016313+00:00
-- url     : https://prove2.me/submissions/cfce8984-2963-4290-98d5-e2cd36dcd9d1

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementCB
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_PerEmbeddingCoupledBound
import Theorems.Thm_Formalism_DimensionVariation_sharp_norm
import Theorems.Thm_Formalism_DimensionVariation_sharp_entries
import Theorems.Thm_Formalism_DimensionVariation_coupled_product
import Theorems.Thm_Formalism_DimensionVariation_coupled_norm
import Theorems.Thm_Formalism_DimensionVariation_sharp_cost
import Theorems.Thm_Formalism_DimensionVariation_path_sum_alt
import Theorems.Thm_Formalism_DimensionVariation_column_paths

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
theorem _root_.solution : LemmaCB :=
  ⟨sharp_entries, coupled_product, path_sum_alt, column_paths, sharp_norm,
    coupled_norm, sharp_cost⟩
end Formalism.DimensionVariation
