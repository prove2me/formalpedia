-- Prove2me | solution 1 for Formalism.REAL.lie_operator_raises_filtration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:48.622821+00:00
-- url     : https://prove2.me/submissions/cf8188fb-5753-4dc4-bac3-df7adf5d5696

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
import Theorems.Thm_Formalism_REAL_word_mem_filtration

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
theorem _root_.solution (i j : Fin n) {k : ℕ} {x : SmoothFunctionsModGroup ε} (hx : x ∈ wordFiltration ε W k) :
    lieOperatorQuotient ε i j x ∈ wordFiltration ε W (k + 1) := by
  have : wordFiltration ε W k ≤ (wordFiltration ε W (k + 1)).comap (lieOperatorQuotient ε i j) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨w, m, hm, hw, rfl⟩
    exact word_mem_filtration (w := (i, j) :: w) hm (by simp; omega)
  exact this hx
end Formalism.REAL
