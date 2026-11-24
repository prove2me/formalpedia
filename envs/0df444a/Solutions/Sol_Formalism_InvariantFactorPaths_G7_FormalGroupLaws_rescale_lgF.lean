-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FormalGroupLaws.rescale_lgF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:49.687179+00:00
-- url     : https://prove2.me/submissions/6cae7db8-1d48-4ca3-a0f3-53147124a379

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
import Definitions.Def_Formalism_TorsionNormIteration_LubinTateExample
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_zeta_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
namespace FormalGroupLaws
section Alg
variable {K : Type} [Field K]
private theorem coeff_lgF_eq_zero_of_ne_pow_sq_pow (p n : ℕ) (h : ∀ j, n ≠ (p ^ 2) ^ j) :
    PowerSeries.coeff n (lgF K p) = 0 := by
  rw [lgF, PowerSeries.coeff_mk]
  exact Finset.sum_eq_zero (fun i _ => if_neg (h i))
end Alg
end FormalGroupLaws
open FormalGroupLaws
end Formalism.InvariantFactorPaths.G7
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.FormalGroupLaws
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.FormalGroupLaws
theorem _root_.solution {ζ : K} {p : ℕ} (hζ : ζ ^ (p ^ 2 - 1) = 1) (hp : 2 ≤ p) :
    PowerSeries.rescale ζ (lgF K p) = PowerSeries.C ζ * lgF K p := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul]
  by_cases hn : ∃ j, n = (p ^ 2) ^ j
  · obtain ⟨j, rfl⟩ := hn
    rw [zeta_pow hζ hp j]
  · push_neg at hn
    rw [coeff_lgF_eq_zero_of_ne_pow_sq_pow p n hn]
    simp
end Formalism.InvariantFactorPaths.G7.FormalGroupLaws
