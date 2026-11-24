-- Prove2me | solution 1 for Formalism.SL.P.eichler_inverse_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:46:30.082272+00:00
-- url     : https://prove2.me/submissions/d6204743-b896-4e6f-a489-26a57338bc90

import Mathlib
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementEI
import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_EichlerEquivalenceHolds
import Theorems.Thm_Formalism_SL_P_eichler_composition_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.SL Formalism.SL.P
open Formalism.SL.IwahoriBlocks
namespace Formalism.SL.P
theorem _root_.solution : Formalism.SL.IwahoriBlocks.EichInv := by
  have hc := eichler_composition_holds
  intro E _ _ V _ _ h x u s hH hxx hux hs v
  have hnx : h (-u) x = 0 := by simp [hux]
  refine ⟨?_, ?_⟩
  · rw [hc E V h x (-u) u (star s) s hH hxx hnx hux]
    have : star s + s + h u (-u) = 0 := by
      rw [map_neg, ← hs]; ring
    have h2 : star s + s + -(h u) u = 0 := by rw [← hs]; ring
    simp [eich, h2]
  · rw [hc E V h x u (-u) s (star s) hH hxx hux hnx]
    have : s + star s + h (-u) u = 0 := by
      rw [LinearMap.map_neg, LinearMap.neg_apply, ← hs]; ring
    have h2 : s + star s + -(h u) u = 0 := by rw [← hs]; ring
    simp [eich, h2]
end Formalism.SL.P
