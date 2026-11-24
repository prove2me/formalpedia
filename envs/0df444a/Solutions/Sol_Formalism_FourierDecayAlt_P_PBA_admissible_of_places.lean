-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.admissible_of_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:37:13.709967+00:00
-- url     : https://prove2.me/submissions/80e461a9-568c-4710-a7cc-7d0ce01d4735

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution {g : C.Word S.f} (h : ∀ v, ∃ w0 : S.W, w0.1 v = g v) : S.admitted g := by
  unfold C.HidaSetting.admitted
  refine ⟨fun v => ?_, fun v => ?_⟩
  · obtain ⟨w0, hw⟩ := h v
    have hA : S.admitted w0.1 := And.left w0.2
    have hA1 := (And.left hA) v
    rw [hw] at hA1
    exact hA1
  · obtain ⟨w0, hw⟩ := h v
    have hA : S.admitted w0.1 := And.left w0.2
    have hA2 := (And.right hA) v
    rw [hw] at hA2
    exact hA2
end Formalism.FourierDecayAlt.P.PBA
