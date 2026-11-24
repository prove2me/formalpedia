-- Prove2me | solution 1 for CompanionTheory.ThKF.E.Impl.dRho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:44:46.014391+00:00
-- url     : https://prove2.me/submissions/ffbc48cc-e072-4e18-aaea-838417ae506a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_CompanionTheory_ThickeningEstimates_InnerProductFactorization_EqOfInner
import Theorems.Thm_CompanionTheory_ThKF_E_exists_rho
import Theorems.Thm_CompanionTheory_ThKF_E_toLp_rho
import Theorems.Thm_CompanionTheory_ThKF_E_eq_of_inner
import Theorems.Thm_GlobalTheory_RealWeil_hasDerivAt_inner_rho
import Theorems.Thm_GlobalTheory_WeilM_IsTilde_unique


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
namespace Impl
theorem _root_.solution {s : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)} {S : Sch l →ₗ[ℂ] Sch l} (h : Impl s S)
    (hs : Function.Surjective S) (w : l ⊕ l → ℝ) (f : Sch l) : S (dRho w f) = dRho (s w) (S f) := by
  refine eq_of_inner fun φ => ?_
  obtain ⟨φ', rfl⟩ := hs φ
  have d1 := hasDerivAt_inner_rho w φ' f
  have d2 := hasDerivAt_inner_rho (s w) (S φ') (S f)
  rw [h.inner]
  refine d1.unique (d2.congr_of_eventuallyEq (.of_forall fun t => ?_))
  obtain ⟨g, hg⟩ := exists_rho (t • w) f
  simp only
  rw [← toLp_rho hg, ← map_smul, ← toLp_rho (h.impl _ _ _ hg), h.inner]
end Impl
end CompanionTheory.ThKF.E
