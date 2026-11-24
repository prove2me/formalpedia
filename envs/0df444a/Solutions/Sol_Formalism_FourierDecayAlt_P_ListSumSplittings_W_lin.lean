-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumSplittings.W_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:33:50.776914+00:00
-- url     : https://prove2.me/submissions/7d19c224-4a5e-4da7-976f-d45f3958c584

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_op_lin
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
theorem _root_.solution (ℓ : Mat k r →ₗ[ℝ] ℂ) :
    ∀ a : List (Bool × Mat k r), ∃ ℓ' : Mat k r →ₗ[ℝ] ℂ, W a (fun g => ℓ g) = fun g => ℓ' g := by
  intro a
  induction a with
  | nil => exact ⟨ℓ, rfl⟩
  | cons x a ih =>
    obtain ⟨ℓ', he⟩ := ih
    exact ⟨ℓ'.comp (vf x.1 x.2).toLinearMap, by rw [W_cons, he, op_lin]⟩
end Formalism.FourierDecayAlt.P.ListSumSplittings
