-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumSplittings.splits_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:12:45.242582+00:00
-- url     : https://prove2.me/submissions/4c8abbe8-79c7-4e8a-92ab-b616fb96fed5

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings

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
theorem _root_.solution {α : Type*} : ∀ (w : List α), ∀ p ∈ splits w, p.1.Sublist w ∧ p.2.Sublist w := by
  intro w
  induction w with
  | nil => intro p hp; simp only [splits, List.mem_singleton] at hp; subst hp; simp
  | cons x w ih =>
    intro p hp
    rw [splits, List.mem_flatMap] at hp
    obtain ⟨q, hq, hp⟩ := hp
    rcases List.mem_cons.1 hp with h | h
    · subst h; exact ⟨(ih q hq).1.cons_cons x, (ih q hq).2.cons x⟩
    · rw [List.mem_singleton.1 h]; exact ⟨(ih q hq).1.cons x, (ih q hq).2.cons_cons x⟩
end Formalism.FourierDecayAlt.P.ListSumSplittings
