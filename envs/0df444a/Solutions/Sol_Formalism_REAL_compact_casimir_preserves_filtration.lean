-- Prove2me | solution 1 for Formalism.REAL.compact_casimir_preserves_filtration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:37:29.408796+00:00
-- url     : https://prove2.me/submissions/a4df56da-ef80-49c3-9adf-c49a2b8ffd57

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasComm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnGroupSum
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IntegrableComplexContinuousBoundedSupport
import Theorems.Thm_Formalism_REAL_compact_lie_operator_preserves_filtration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ENNReal
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
variable (ε)
variable {ε}
variable {W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)}
namespace Formalism.REAL
theorem _root_.solution (hsm : ∀ w ∈ W, SmoothOnG ε w)
    (hstab : ∀ w ∈ W, ∀ i j : Fin n, ε i = ε j → ∃ w' ∈ W, ∀ g, inUJ ε g → Eab ε i j w g = w' g)
    {k : ℕ} {x : SmoothFunctionsModGroup ε} (hx : x ∈ wordFiltration ε W k) : CasK ε (lieOperatorQuotient ε) x ∈ wordFiltration ε W k := by
  unfold CasK
  simp only [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  split_ifs with h
  · rw [Module.End.mul_apply]
    exact compact_lie_operator_preserves_filtration hsm hstab h (compact_lie_operator_preserves_filtration hsm hstab h.symm hx)
  · rw [LinearMap.zero_apply]; exact zero_mem _
end Formalism.REAL
