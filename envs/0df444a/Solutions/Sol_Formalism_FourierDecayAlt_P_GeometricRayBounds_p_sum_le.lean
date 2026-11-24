-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GeometricRayBounds.p_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:19:43.824966+00:00
-- url     : https://prove2.me/submissions/c40cf24c-d75d-4fcf-9e91-bbeb30b3fb34

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragingVanishes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GeometricRayBounds
namespace Formalism.FourierDecayAlt.P.GeometricRayBounds
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] (p : Seminorm ℂ V) {ι : Type*} (S : Finset ι)
    (f : ι → V) : p (∑ i ∈ S, f i) ≤ ∑ i ∈ S, p (f i) := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact (map_add_le_add p _ _).trans (add_le_add_right ih _)
end Formalism.FourierDecayAlt.P.GeometricRayBounds
