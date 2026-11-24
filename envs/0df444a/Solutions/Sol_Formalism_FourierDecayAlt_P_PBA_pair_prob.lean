-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.pair_prob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:57:32.100014+00:00
-- url     : https://prove2.me/submissions/bf942a1c-28bd-41bd-be55-5c274ccab965

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SizeAtNonneg

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
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution {W : Type} {s t : Finset W} {a b : W → ℝ} (ha : TB.IsProb s a) (hb : TB.IsProb t b) :
    TB.IsProb (s ×ˢ t) (fun x => a x.1 * b x.2) := by
  refine ⟨fun x => mul_nonneg (ha.1 _) (hb.1 _), fun x hx => ?_, ?_⟩
  · rw [Finset.mem_product, not_and_or] at hx
    rcases hx with h | h
    · simp [ha.2.1 _ h]
    · simp [hb.2.1 _ h]
  · rw [Finset.sum_product]
    simp_rw [← Finset.mul_sum, hb.2.2, mul_one]
    exact ha.2.2
end Formalism.FourierDecayAlt.P.PBA
