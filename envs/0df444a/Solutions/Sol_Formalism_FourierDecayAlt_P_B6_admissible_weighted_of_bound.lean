-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.admissible_weighted_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:24:03.004896+00:00
-- url     : https://prove2.me/submissions/b599c3ea-befd-4643-9aa0-2e5b32f51dd9

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_lie_element_unitary
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuousOn_of_contDiffOn_group
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_right_derivative_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_differentiable_left_of_contDiffOn_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_smooth_iterated_left_right_derivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_replicated_word_derivative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {α c : ℝ} {F : Mat k r → E} (h : CCle α 4 F c) : AdmW α c 2 2 F := by
  obtain ⟨hck, hb⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro j hj i hi
    refine ⟨continuousOn_of_contDiffOn_group (smooth_iterated_left_right_derivatives (n := 0) hck (by omega)), ?_⟩
    intro g hg
    rw [← replicated_word_derivative]
    refine hb _ _ ?_ ?_ ?_ g hg
    · intro X hX; rw [List.eq_of_mem_replicate hX]; exact lie_element_unitary k r
    · intro X hX; rw [List.eq_of_mem_replicate hX]; exact lie_element_unitary k r
    · simp only [List.length_replicate]; omega
  · intro j hj
    exact right_derivative_exists (n := 0) (smooth_iterated_left_right_derivatives (n := 1) (i := 0) hck (by omega))
  · intro j hj i hi
    exact differentiable_left_of_contDiffOn_succ (n := 0) (smooth_iterated_left_right_derivatives (n := 1) hck (by omega))
end Formalism.FourierDecayAlt.P.B6
