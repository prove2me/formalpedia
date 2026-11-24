-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.heisenberg_three_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:49:41.613805+00:00
-- url     : https://prove2.me/submissions/2ac34240-8fe1-4af8-9a4e-8cbd0e1e0e30

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_e0_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_lift_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hermitian_three_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_tk_heisAct

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
theorem _root_.solution (x : HPar k r') (a b : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) :
    heis0 k r' x *ᵥ mk3 k r' a y b =
      mk3 k r' (a - herm (Hpk k r') y x.1 + b * hb k r' x.1 x.2) (y + b • x.1) b := by
  have h0 : herm (Hpk k r') y 0 = 0 := by simp [herm]
  unfold heis0
  rw [tk_heisAct, lift_eq, e0_eq, hermitian_three_block, hermitian_three_block]
  simp only [map_zero, map_one, mul_zero, mul_one, zero_add, add_zero, h0, three_block_smul, three_block_add, three_block_sub]
  congr 1 <;> first | ring1 | simp
end Formalism.FourierDecayAlt.P.B2x8
