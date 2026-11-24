-- Prove2me | solution 1 for Formalism.L2.Th1.H.fourfoldTensor_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:26:16.518803+00:00
-- url     : https://prove2.me/submissions/ff77b978-f95c-45cb-8cc4-6422946b4fc3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {n : Type*} [Fintype n]
namespace Formalism.L2.Th1.H
theorem _root_.solution (c : ℂ) (θ : (n → ℂ) → ℂ) : tens4 (c • θ) = c ^ 4 • tens4 θ := by
  funext z
  simp only [tens4, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
end Formalism.L2.Th1.H
