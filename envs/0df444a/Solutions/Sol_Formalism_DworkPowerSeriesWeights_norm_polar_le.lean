-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.norm_polar_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:04:26.931854+00:00
-- url     : https://prove2.me/submissions/e034ab9b-91b6-41c0-9121-73167d36c2e2

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementQ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneRow
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_IntegralOperatorsOnJets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type} [Fintype ι]
    (c : ι → ι → K) (hc : ∀ x y, ‖c x y‖ ≤ 1) (L L' : ι → K) (hL : ∀ x, ‖L x‖ ≤ 1)
    (hL' : ∀ x, ‖L' x‖ ≤ 1) : ‖polar c L L'‖ ≤ 1 := by
  unfold polar
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun y _ => ?_
  rw [norm_mul]
  refine mul_le_one₀ (hc x y) (norm_nonneg _) ?_
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact mul_le_one₀ (hL x) (norm_nonneg _) (hL' y)
  · rw [norm_mul]
    exact mul_le_one₀ (hL y) (norm_nonneg _) (hL' x)
end Formalism.DworkPowerSeriesWeights
