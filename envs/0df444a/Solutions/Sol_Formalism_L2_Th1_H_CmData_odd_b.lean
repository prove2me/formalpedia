-- Prove2me | solution 1 for Formalism.L2.Th1.H.CmData.odd_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:25:35.719799+00:00
-- url     : https://prove2.me/submissions/4a033fdf-69d7-498f-83d4-51293d66d4c3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_StdDataCmProof
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb


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
theorem _root_.solution (a : ℕ) (b c : ℤ) (d : ℕ) (h4 : 4 * (a : ℤ) * c = b ^ 2 + d) (h8 : d % 8 = 7) : Odd b := by
  rcases Int.even_or_odd b with ⟨k, hk⟩ | hb
  · exfalso
    subst hk
    have h5 : 4 * ((a : ℤ) * c) = 4 * (k * k) + d := by rw [← mul_assoc, h4]; ring
    generalize (a : ℤ) * c = s at h5
    generalize k * k = t at h5
    omega
  · exact hb
end Formalism.L2.Th1.H.CmData
