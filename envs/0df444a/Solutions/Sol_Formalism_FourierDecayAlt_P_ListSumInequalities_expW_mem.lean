-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumInequalities.expW_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:15:49.859325+00:00
-- url     : https://prove2.me/submissions/818f8372-3226-4c09-86b9-d3748d8674ef

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_Lt_unit


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
theorem _root_.solution (w : List (Bool × Mat k r)) :
    ∀ p ∈ expW w, p.2.length = w.length ∧ ∀ y ∈ p.2, unitLie k r y.2 := by
  induction w with
  | nil =>
    intro p hp
    simp only [expW, List.mem_singleton] at hp
    subst hp
    simp
  | cons x w ih =>
    intro p hp
    simp only [expW, List.mem_flatMap, List.mem_map] at hp
    obtain ⟨q, hq, i, -, rfl⟩ := hp
    obtain ⟨h1, h2⟩ := ih q hq
    refine ⟨by simp [h1], ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Lt_unit i
    · exact h2 y hy
end Formalism.FourierDecayAlt.P.ListSumInequalities
