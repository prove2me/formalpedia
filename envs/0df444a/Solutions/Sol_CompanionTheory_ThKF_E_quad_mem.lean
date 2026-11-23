-- Prove2me | solution 1 for CompanionTheory.ThKF.E.quad_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:15.28988+00:00
-- url     : https://prove2.me/submissions/697608bf-8c91-499d-ad4f-30b4af96a66e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_CompanionTheory_ThickeningEstimates_InnerProductFactorization_EqOfInner
import Theorems.Thm_GlobalTheory_RealWeil_dRho_mem_weylAlg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKF CompanionTheory.ThKF.E
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKF.E
theorem _root_.solution (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) : quad X ∈ weylAlg l :=
  Subalgebra.smul_mem _ (sum_mem fun _ _ => sum_mem fun _ _ => Subalgebra.smul_mem _
    (add_mem (mul_mem (dRho_mem_weylAlg _) (dRho_mem_weylAlg _)) (mul_mem (dRho_mem_weylAlg _) (dRho_mem_weylAlg _))) _) _
end CompanionTheory.ThKF.E
