-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.closure_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:44.933083+00:00
-- url     : https://prove2.me/submissions/af3ef524-af29-4f48-8839-40b6bccca32f

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_eq_sum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_right
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs


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
theorem _root_.solution {Wt J : Type} (valid : Wt → Prop) (B : Wt → ℝ) (s : Finset J) (f : J → K)
    (h : ∀ j ∈ s, f j = 0 ∨ ∃ w, valid w ∧ ‖f j‖ ≤ B w) :
    ∑ j ∈ s, f j = 0 ∨ ∃ w, valid w ∧ ‖∑ j ∈ s, f j‖ ≤ B w := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · left; simp
  · obtain ⟨j, hj, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs f
    rcases h j hj with h0 | ⟨w, hw, hb⟩
    · left
      rw [h0, norm_zero] at hle
      exact norm_le_zero_iff.1 hle
    · exact Or.inr ⟨w, hw, hle.trans hb⟩
end Formalism.InvariantFactorPaths.G7.ETerm
