-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.cg_frob2_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:45:52.046212+00:00
-- url     : https://prove2.me/submissions/b7798fc5-e376-4d77-9fff-33e1d0058f1c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_trans
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_frob_sum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low norm_finsum_le_of)
open Formalism.FG.SolveVAux (Low low_pow low_one_iff)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one integralSubstV)
open Formalism.InvariantFactorPaths.G7.TwoS
variable {K ι : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.InvariantFactorPaths.G7.TwoS
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) {α : Type} (s : Finset α)
    (F : α → MvPowerSeries ι K) (h : ∀ a ∈ s, Integral (F a)) :
    Cg p ((∑ a ∈ s, F a) ^ (p ^ 2)) (∑ a ∈ s, F a ^ (p ^ 2)) := by
  have h1 := cg_frob_sum hp hn s F h
  have h2 := cg_frob_sum hp hn s (fun a => F a ^ p) fun a ha => integral_pow (h a ha) p
  have h3 := cg_pow (integral_pow (integral_sum _ _ h) p)
    (integral_sum _ _ fun a ha => integral_pow (h a ha) p) h1 p
  simp only [← pow_mul, ← sq] at h2 h3
  exact cg_trans h3 h2
end Formalism.InvariantFactorPaths.G7.TwoS
