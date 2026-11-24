-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.exists_phase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:31:12.277847+00:00
-- url     : https://prove2.me/submissions/9cb15ebd-3080-4396-b7ae-86cf3f0902ad

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution (s : ℂ) (q : ℝ) : ∃ θ : ℂ, θ * star θ = 1 ∧ ∃ t : ℝ, star θ * s = t ∧ q * t ≤ 0 := by
  by_cases hs : s = 0
  · exact ⟨1, by simp, 0, by simp [hs], by simp⟩
  have hn : (‖s‖ : ℂ) ≠ 0 := by
    simpa using hs
  have hss : star s * s = (‖s‖ : ℂ) ^ 2 := by
    rw [Complex.star_def]; exact Complex.conj_mul' s
  have hss' : s * star s = (‖s‖ : ℂ) ^ 2 := by rw [mul_comm]; exact hss
  have hst : star ((‖s‖ : ℂ)) = (‖s‖ : ℂ) := by simp
  rcases le_total 0 q with hq | hq
  · refine ⟨-(s / ‖s‖), ?_, -‖s‖, ?_, ?_⟩
    · rw [star_neg, star_div₀, hst]
      field_simp
      linear_combination hss'
    · rw [star_neg, star_div₀, hst]
      push_cast
      field_simp
      linear_combination -hss
    · have := norm_nonneg s
      nlinarith
  · refine ⟨s / ‖s‖, ?_, ‖s‖, ?_, ?_⟩
    · rw [star_div₀, hst]
      field_simp
      linear_combination hss'
    · rw [star_div₀, hst]
      field_simp
      linear_combination hss
    · have := norm_nonneg s
      nlinarith
end Formalism.FourierDecayAlt.P.TwoByOneBlock
