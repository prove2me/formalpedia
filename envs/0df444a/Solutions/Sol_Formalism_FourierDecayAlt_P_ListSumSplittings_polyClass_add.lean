-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumSplittings.polyClass_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:21:50.645171+00:00
-- url     : https://prove2.me/submissions/da881ef1-7617-4dfc-a850-7cd9a310338f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_ckOn_top_nat


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
theorem _root_.solution {D : ℕ} {P Q : Mat k r → ℂ} (hP : PolyClass D P) (hQ : PolyClass D Q) :
    PolyClass D (fun g => P g + Q g) := by
  refine ⟨ckOn_add hP.1 hQ.1, fun a ha => ?_⟩
  obtain ⟨C1, h10, h1⟩ := hP.2 a ha
  obtain ⟨C2, h20, h2⟩ := hQ.2 a ha
  refine ⟨C1 + C2, add_nonneg h10 h20, fun g hg => ?_⟩
  have e := W_add a ha (ckOn_top_nat hP.1 _) (ckOn_top_nat hQ.1 _) g hg
  rw [show (fun g => P g + Q g) = P + Q from rfl, e]
  calc ‖W a P g + W a Q g‖ ≤ ‖W a P g‖ + ‖W a Q g‖ := norm_add_le _ _
    _ ≤ C1 * gN g ^ D + C2 * gN g ^ D := add_le_add (h1 g hg) (h2 g hg)
    _ = (C1 + C2) * gN g ^ D := by ring
end Formalism.FourierDecayAlt.P.ListSumSplittings
