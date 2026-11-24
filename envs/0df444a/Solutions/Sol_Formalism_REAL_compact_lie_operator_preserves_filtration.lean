-- Prove2me | solution 1 for Formalism.REAL.compact_lie_operator_preserves_filtration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:18:10.690792+00:00
-- url     : https://prove2.me/submissions/a534a66b-6cf5-4579-ba25-8fbce53b1c40

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
import Theorems.Thm_Formalism_REAL_filtration_mono
import Theorems.Thm_Formalism_REAL_lie_operator_word_mem_filtration

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
    {c d : Fin n} (hcd : ε c = ε d) {k : ℕ} {x : SmoothFunctionsModGroup ε} (hx : x ∈ wordFiltration ε W k) :
    lieOperatorQuotient ε c d x ∈ wordFiltration ε W k := by
  have : wordFiltration ε W k ≤ (wordFiltration ε W k).comap (lieOperatorQuotient ε c d) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨w, m, hm, hw, rfl⟩
    exact filtration_mono hw (lie_operator_word_mem_filtration hsm hstab hcd hm w)
  exact this hx
end Formalism.REAL
