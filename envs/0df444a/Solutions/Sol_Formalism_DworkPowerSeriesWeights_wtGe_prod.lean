-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.wtGe_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:29.03473+00:00
-- url     : https://prove2.me/submissions/4625b1a2-4443-4d4c-9e97-52a3d88f5afd

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46
import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WtGeProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound

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
variable {K : Type u} [NormedField K] {ι : Type v}
variable [IsUltrametricDist K]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {pi : ℝ} (h0 : 0 < pi) {r : ι → ℝ} {α : Type w} (s : Finset α) (wt : α → ℝ)
    (F : α → MvPowerSeries ι K) (h : ∀ i ∈ s, WtGe pi r (wt i) (F i)) :
    WtGe pi r (∑ i ∈ s, wt i) (∏ i ∈ s, F i) := by
  first | exact UpperTheory.Reformulated.B.Qk29.wtGe_prod .. | (apply UpperTheory.Reformulated.B.Qk29.wtGe_prod <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk29.wtGe_prod <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk29.wtGe_prod <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk29.wtGe_prod <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk29.wtGe_prod <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι ‹_› pi h0 r α s wt F h | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι ‹_› pi h0 r α s wt F | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι ‹_› pi h0 r α s wt | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι ‹_› pi h0 r α s | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι ‹_› pi h0 r α | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι ‹_› pi h0 r | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι ‹_› pi h0 | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι ‹_› pi | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι ‹_› | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› ι | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K ‹_› | exact @UpperTheory.Reformulated.B.Qk29.wtGe_prod K
end Formalism.DworkPowerSeriesWeights
