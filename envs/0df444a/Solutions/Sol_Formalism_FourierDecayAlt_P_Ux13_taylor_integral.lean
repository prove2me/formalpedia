-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux13.taylor_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:31:00.511785+00:00
-- url     : https://prove2.me/submissions/f065ef32-9e88-4428-ad84-070d321853a6

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux13
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
namespace Formalism.FourierDecayAlt.P.Ux13
theorem _root_.solution {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] {q : ℕ} (H : α → X → W) (ph : α → X → FormalMultilinearSeries ℝ X W)
    (hT : ∀ a, HasFTaylorSeriesUpTo q (H a) (ph a))
    (hmeas : ∀ m ≤ q, ∀ x, AEStronglyMeasurable (fun a => ph a x m) μ)
    (bound : α → ℝ) (hb : Integrable bound μ) (hle : ∀ m ≤ q, ∀ a x, ‖ph a x m‖ ≤ bound a) :
    HasFTaylorSeriesUpTo q (fun x => ∫ a, H a x ∂μ) (fun x m => ∫ a, ph a x m ∂μ) := by
  have hint : ∀ m ≤ q, ∀ x, Integrable (fun a => ph a x m) μ := fun m hm x =>
    hb.mono' (hmeas m hm x) (Filter.Eventually.of_forall fun a => hle m hm a x)
  refine ⟨fun x => ?_, fun m hm x => ?_, fun m hm => ?_⟩
  · have h0 := hint 0 (Nat.zero_le _) x
    show (∫ a, ph a x 0 ∂μ) 0 = ∫ a, H a x ∂μ
    rw [ContinuousMultilinearMap.integral_apply h0]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => (hT a).zero_eq x)
  · have hmq' : m < q := by exact_mod_cast hm
    have hm' : m + 1 ≤ q := hmq'
    have hmq : m ≤ q := hmq'.le
    have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (s := Set.univ) (x₀ := x)
      (F := fun y a => ph a y m) (F' := fun y a => (ph a y (m + 1)).curryLeft) (bound := bound)
      Filter.univ_mem (Filter.Eventually.of_forall fun y => hmeas m hmq y) (hint m hmq x)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => X) W).continuous.comp_aestronglyMeasurable
        (hmeas (m + 1) hm' x))
      (Filter.Eventually.of_forall fun a y _ => by
        have hn := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => X) W).norm_map (ph a y (m + 1))
        exact (le_of_eq hn).trans (hle (m + 1) hm' a y))
      hb (Filter.Eventually.of_forall fun a y _ => (hT a).fderiv m hm y)
    have hc := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => X) W).toContinuousLinearEquiv.integral_comp_comm
      (μ := μ) (fun a => ph a x (m + 1))
    exact key.congr_fderiv hc
  · have hmq : m ≤ q := by exact_mod_cast hm
    exact continuous_of_dominated (fun x => hmeas m hmq x)
      (fun x => Filter.Eventually.of_forall fun a => hle m hmq a x) hb
      (Filter.Eventually.of_forall fun a => (hT a).cont m hm)
end Formalism.FourierDecayAlt.P.Ux13
