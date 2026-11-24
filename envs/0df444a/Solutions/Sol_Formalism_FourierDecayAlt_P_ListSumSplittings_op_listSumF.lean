-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumSplittings.op_listSumF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:55:09.649802+00:00
-- url     : https://prove2.me/submissions/ff53cd9d-0e3a-416f-b68d-8e7e629b0f75

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_ckOn_listSumF
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_add


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
theorem _root_.solution {α : Type*} {b : Bool} {X : Mat k r} (hX : inLie k r X) (φ : α → Mat k r → E) :
    ∀ (L : List α), (∀ a ∈ L, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (φ a)) →
      ∀ g ∈ GV k r, op b X (fun g' => (L.map fun a => φ a g').sum) g = (L.map fun a => op b X (φ a) g).sum := by
  intro L
  induction L with
  | nil => intro _ g _; simp [op]
  | cons a L ih =>
    intro hL g hg
    have hL' : ∀ c ∈ L, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (φ c) := fun c hc => hL c (List.mem_cons_of_mem _ hc)
    have e : (fun g' => ((a :: L).map fun a => φ a g').sum) = φ a + (fun g' => (L.map fun a => φ a g').sum) := by
      funext g'; simp
    rw [e, op_add b hX (hL a List.mem_cons_self) (ckOn_listSumF φ L hL') hg, ih hL' g hg]
    simp
end Formalism.FourierDecayAlt.P.ListSumSplittings
