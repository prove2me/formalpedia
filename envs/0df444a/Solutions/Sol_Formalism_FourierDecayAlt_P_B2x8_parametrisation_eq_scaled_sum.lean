-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.parametrisation_eq_scaled_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:24:56.164361+00:00
-- url     : https://prove2.me/submissions/4c3888e2-f202-4f39-a413-0fe14e6588af

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_e0_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_dual_base_vector_eq_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_lift_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heisenberg_quadratic_dilation

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (p : ℂ × HPar k r') :
    p.1 • (es0 k r' + liftVec k 1 r' p.2.1 + hb k r' p.2.1 p.2.2 • e0 k r') = Ψt k r' (cm1Θ k r' p) := by
  obtain ⟨c, y, s⟩ := p
  simp only [Ψt, cm1Θ]
  rw [heisenberg_quadratic_dilation, dual_base_vector_eq_single, lift_eq, e0_eq, three_block_smul, three_block_add, three_block_add, three_block_smul]
  by_cases hc : c = 0
  · subst hc; simp
  · have hc' : conj c ≠ 0 := (map_ne_zero _).mpr hc
    have h1 : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * conj c := by
      rw [Complex.mul_conj']; push_cast; rfl
    rw [h1]
    congr 1
    · field_simp
      ring
    · simp
    · simp
end Formalism.FourierDecayAlt.P.B2x8
