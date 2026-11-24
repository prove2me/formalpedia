-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.heis_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:07:16.254051+00:00
-- url     : https://prove2.me/submissions/62602c8d-341d-498c-b23b-cca994779244

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_mem_UH_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_eta
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hermitian_three_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_Hpk_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hb_add_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heisenberg_three_block
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm


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
theorem _root_.solution (x : HPar k r') : heis0 k r' x ∈ GV k (1 + r') := by
  apply mem_UH_of
  intro u v
  rw [← three_block_eta u, ← three_block_eta v, heisenberg_three_block, heisenberg_three_block, hermitian_three_block, hermitian_three_block]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right]
  have h1 := herm_conj (Hpk k r') (Hpk_herm k r') (mid v) x.1
  have h2 := hb_add_conj (k := k) x.1 x.2
  simp only [map_add, map_sub, map_mul]
  linear_combination (-(cL u)) * h1 + (cL u * (starRingEnd ℂ) (cL v)) * h2
end Formalism.FourierDecayAlt.P.B2x8
