-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.letters_at_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:46:01.091428+00:00
-- url     : https://prove2.me/submissions/9c704ef3-0435-4ede-b1ba-cedbb742fb8c

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThresholdBelowOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Jx11
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : LettersAtPlaces := by
  intro L f K pl A φ h
  rw [← Finset.prod_fiberwise (s := univ) (g := pl) (f := fun a => φ (pl a))]
  have h1 : ∀ v : Fin f, ∏ a ∈ univ.filter (fun a => pl a = v), φ (pl a) = φ v ^ (if v ∈ A then K else 0) := by
    intro v
    rw [← h v, ← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro a ha
    rw [(Finset.mem_filter.1 ha).2]
  simp only [h1]
  rw [← Finset.prod_subset (Finset.subset_univ A)]
  · apply Finset.prod_congr rfl
    intro v hv; rw [if_pos hv]
  · intro v _ hv; rw [if_neg hv, pow_zero]
end Formalism.FourierDecayAlt.P
