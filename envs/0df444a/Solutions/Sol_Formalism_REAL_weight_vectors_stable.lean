-- Prove2me | solution 1 for Formalism.REAL.weight_vectors_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:33:37.84392+00:00
-- url     : https://prove2.me/submissions/4941f24d-267c-49f8-9a05-59572e7f1d01

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
import Theorems.Thm_Formalism_REAL_lie_operator_quotient_mk

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
    {m : SmoothFunctionsModGroup ε} (hm : m ∈ weightVectorsQuotient ε W) {c d : Fin n} (hcd : ε c = ε d) :
    lieOperatorQuotient ε c d m ∈ weightVectorsQuotient ε W := by
  obtain ⟨f, hfW, hf, rfl⟩ := hm
  obtain ⟨f', hf'W, he⟩ := hstab f hfW c d hcd
  refine ⟨f', hf'W, hsm f' hf'W, ?_⟩
  rw [lie_operator_quotient_mk, quotient_mk_eq_iff]
  exact he
end Formalism.REAL
