-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.qrefl_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:50:52.89572+00:00
-- url     : https://prove2.me/submissions/9ff48c71-5bec-4d8c-adaf-578f729fc4d1

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mem_UH_of_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_qrefl_mulVec

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
theorem _root_.solution {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (hH : Hᴴ = H) (d : Fin m → ℂ) (c : ℂ)
    (hc : c + star c + c * star c * herm H d d = 0) : qrefl H d c ∈ UH H := by
  apply mem_UH_of_herm
  intro x y
  rw [qrefl_mulVec, qrefl_mulVec]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, star_mul]
  rw [herm_symm H hH y d]
  linear_combination (herm H x d * star (herm H y d)) * hc
end Formalism.FourierDecayAlt.P.TwoByOneBlock
