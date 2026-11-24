-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumSplittings.W_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:14:23.633532+00:00
-- url     : https://prove2.me/submissions/830d1575-74cc-4eb5-a7b6-a27abea3fd9a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_cons


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumSplittings
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic Formalism.FourierDecayAlt.P.ListSumInequalities
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumSplittings
theorem _root_.solution (c : ℂ) : ∀ a : List (Bool × Mat k r), ∃ c' : ℂ, ‖c'‖ ≤ ‖c‖ ∧ W a (fun _ => c) = fun _ => c' := by
  intro a
  induction a with
  | nil => exact ⟨c, le_rfl, rfl⟩
  | cons x a ih =>
    obtain ⟨c', -, he⟩ := ih
    refine ⟨0, by simp, ?_⟩
    rw [W_cons, he]
    funext g; simp [op]
end Formalism.FourierDecayAlt.P.ListSumSplittings
