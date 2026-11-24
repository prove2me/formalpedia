-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumInequalities.bw_tags
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:52:01.651988+00:00
-- url     : https://prove2.me/submissions/ddf93145-0be5-448d-aa59-1f48eb66bf30

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumInequalities
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumInequalities
theorem _root_.solution : ∀ (τ : List Bool), ∀ w' ∈ bw (k := k) (r := r) τ, w'.map Prod.fst = τ := by
  intro τ
  induction τ with
  | nil =>
    intro w' hw
    simp only [bw, List.mem_singleton] at hw
    subst hw
    rfl
  | cons b τ ih =>
    intro w' hw
    simp only [bw, List.mem_flatMap, List.mem_map] at hw
    obtain ⟨w, hw, i, -, rfl⟩ := hw
    simp [ih w hw]
end Formalism.FourierDecayAlt.P.ListSumInequalities
