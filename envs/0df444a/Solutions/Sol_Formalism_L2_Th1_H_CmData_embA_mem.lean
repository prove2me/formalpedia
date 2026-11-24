-- Prove2me | solution 1 for Formalism.L2.Th1.H.CmData.embA_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:26:20.171563+00:00
-- url     : https://prove2.me/submissions/ecab371e-6b98-4880-ba93-605201151f26

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_StdDataCmProof
import Theorems.Thm_Formalism_L2_Th1_H_CmData_slice_embA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H Formalism.L2.Th1.H.CmData
open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmPair cmTheta)
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.L2.Th1.H.CmData
theorem _root_.solution (Λ : AddSubgroup (n → ℂ)) (a : Fin 4) {x : n → ℂ} (hx : x ∈ Λ) : embA a x ∈ pow4 Λ := by
  intro a'
  rw [slice_embA]
  split_ifs
  · exact hx
  · exact Λ.zero_mem
end Formalism.L2.Th1.H.CmData
