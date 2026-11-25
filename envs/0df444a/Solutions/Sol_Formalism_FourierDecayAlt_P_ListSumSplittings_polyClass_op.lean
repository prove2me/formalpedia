-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumSplittings.polyClass_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:21:47.051422+00:00
-- url     : https://prove2.me/submissions/f23f22e5-dad0-4f7c-8054-1e570143dd29

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_append
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_ckOn_op_top


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
theorem _root_.solution {D : ℕ} {P : Mat k r → ℂ} (hP : PolyClass D P) (b : Bool) {X : Mat k r}
    (hX : inLie k r X) : PolyClass D (op b X P) := by
  refine ⟨ckOn_op_top b hP.1 hX, fun a ha => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hP.2 (a ++ [(b, X)]) (by
    intro y hy; rcases List.mem_append.1 hy with h | h
    · exact ha y h
    · rw [List.mem_singleton.1 h]; exact hX)
  exact ⟨C, hC0, fun g hg => by have := hC g hg; rwa [W_append] at this⟩
end Formalism.FourierDecayAlt.P.ListSumSplittings
