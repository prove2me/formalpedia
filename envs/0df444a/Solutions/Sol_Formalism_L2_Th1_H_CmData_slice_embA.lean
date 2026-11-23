-- Prove2me | solution 1 for Formalism.L2.Th1.H.CmData.slice_embA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:13.388118+00:00
-- url     : https://prove2.me/submissions/d994ec12-6cb3-437a-92f9-1f37ef6f4da7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_StdDataCmProof

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
theorem _root_.solution (a a' : Fin 4) (x : n → ℂ) : slice a' (embA a x) = if a' = a then x else 0 := by
  ext i
  by_cases h : a' = a <;> simp [slice, embA, h]
end Formalism.L2.Th1.H.CmData
