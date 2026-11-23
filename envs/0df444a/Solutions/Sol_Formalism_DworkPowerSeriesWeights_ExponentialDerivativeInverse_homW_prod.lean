-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse.homW_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:05.736875+00:00
-- url     : https://prove2.me/submissions/648477f3-b7b0-4143-84ee-4d31c8fbed7e

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero

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
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
variable {K : Type u} [NormedField K] {ι : Type v}
variable {w : ι → ℤ}
namespace Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
theorem _root_.solution {α : Type w} (s : Finset α) (c : α → ℤ) (F : α → MvPowerSeries ι K)
    (h : ∀ i ∈ s, HomW w (c i) (F i)) : HomW w (∑ i ∈ s, c i) (∏ i ∈ s, F i) := by
  first | exact UpperTheory.Reformulated.B.Qi22.homW_prod .. | (apply UpperTheory.Reformulated.B.Qi22.homW_prod <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qi22.homW_prod <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi22.homW_prod <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qi22.homW_prod <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi22.homW_prod <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι w α s c F h | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι w α s c F | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι w α s c | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι w α s | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι w α | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι w | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› ι | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K ‹_› | exact @UpperTheory.Reformulated.B.Qi22.homW_prod K
end Formalism.DworkPowerSeriesWeights.ExponentialDerivativeInverse
