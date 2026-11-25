-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ruleB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:47:19.044398+00:00
-- url     : https://prove2.me/submissions/ab051538-22b2-4d15-9ea5-efb2199b9088

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_ckOn_op_top
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_dLR_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_dLR_L

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
theorem _root_.solution : C2.RuleB := by
  intro k r E _ _ A F hF X hX
  refine ⟨⟨ckOn_op_top false hF.1 hX.1, ?_⟩, ⟨ckOn_op_top true hF.1 hX.1, ?_⟩⟩
  · intro u v hu hv
    obtain ⟨C, hC⟩ := hF.2 u (v ++ [X]) hu (by
      intro Y hY; rcases List.mem_append.1 hY with h | h
      · exact hv Y h
      · rw [List.mem_singleton.1 h]; exact hX)
    refine ⟨C, fun g hg => ?_⟩
    have e : A - C2.B0 r - C2.B0 r * ((u.length : ℝ) + v.length) =
        A - C2.B0 r * ((u.length : ℝ) + (v ++ [X]).length) := by
      rw [List.length_append, List.length_singleton]; push_cast; ring
    have := hC g hg
    rw [← e, ← dLR_R] at this
    exact this
  · intro u v hu hv
    obtain ⟨C, hC⟩ := hF.2 (u ++ [X]) v (by
      intro Y hY; rcases List.mem_append.1 hY with h | h
      · exact hu Y h
      · rw [List.mem_singleton.1 h]; exact hX) hv
    refine ⟨C, fun g hg => ?_⟩
    have e : A - C2.B0 r - C2.B0 r * ((u.length : ℝ) + v.length) =
        A - C2.B0 r * (((u ++ [X]).length : ℝ) + v.length) := by
      rw [List.length_append, List.length_singleton]; push_cast; ring
    have := hC g hg
    rw [← e, ← dLR_L (fun Y hY => (hu Y hY).1) (fun Y hY => (hv Y hY).1) hX.1 hF.1 g hg] at this
    exact this
end Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
