-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.norm_prod_pow_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:06.147801+00:00
-- url     : https://prove2.me/submissions/f1c9cec9-759c-4d26-b604-0a2fb152a6e0

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_eq_sum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_right


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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.InvariantFactorPaths.G7.ETerm
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact jetPair_eq_sum jetPair_C_mul_right jetPair_sum_right)
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.InvariantFactorPaths.G7.ETerm
theorem _root_.solution {α : Type} (s : Finset α) (a : α → K) (m : α → ℕ)
    (ha : ∀ i, ‖a i‖ ≤ 1) : ‖∏ i ∈ s, a i ^ m i‖ ≤ 1 := by
  rw [norm_prod]
  refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => ?_
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (ha i)
end Formalism.InvariantFactorPaths.G7.ETerm
