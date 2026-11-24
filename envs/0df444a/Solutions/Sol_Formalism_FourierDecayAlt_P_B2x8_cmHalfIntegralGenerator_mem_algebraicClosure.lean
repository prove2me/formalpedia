-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.cmHalfIntegralGenerator_mem_algebraicClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:49:33.00427+00:00
-- url     : https://prove2.me/submissions/a0247916-ad2d-4d41-900f-ff3a5b098666

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_mem_UH_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_eta
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hermitian_three_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_long_weyl_three_block

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
theorem _root_.solution (c : ℂ) (hc : c ≠ 0) : w0 k r' c ∈ GV k (1 + r') := by
  apply mem_UH_of
  intro u v
  rw [← three_block_eta u, ← three_block_eta v, long_weyl_three_block, long_weyl_three_block, hermitian_three_block, hermitian_three_block]
  have hc' : (starRingEnd ℂ) c ≠ 0 := by simpa using hc
  have h1 : ((starRingEnd ℂ) c)⁻¹ * (starRingEnd ℂ) c = 1 := inv_mul_cancel₀ hc'
  have h2 : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  simp only [map_mul, map_inv₀, Complex.conj_conj]
  linear_combination (cL u * (starRingEnd ℂ) (cF v)) * h1 + (cF u * (starRingEnd ℂ) (cL v)) * h2
end Formalism.FourierDecayAlt.P.B2x8
