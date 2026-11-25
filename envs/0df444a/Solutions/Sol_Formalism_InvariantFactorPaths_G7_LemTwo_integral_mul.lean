-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemTwo.integral_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:04:59.222637+00:00
-- url     : https://prove2.me/submissions/b44e1a78-b95a-48fb-8b62-a18a123bc774

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LemmaTwoOf

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LemTwo
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.InvariantFactorPaths.G7.LemTwo
theorem _root_.solution {ι : Type} {f g : MvPowerSeries ι K} (hf : Integral f) (hg : Integral g) :
    Integral (f * g) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    (fun q _ => by rw [norm_mul]; exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _))
end Formalism.InvariantFactorPaths.G7.LemTwo
