-- Prove2me | solution 1 for Formalism.REAL.signedCasimir_preserves_filtration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:59:05.989223+00:00
-- url     : https://prove2.me/submissions/82ce0a56-0de1-4d2b-a9a9-ef0ae23afc1d

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
import Theorems.Thm_Formalism_REAL_signed_casimir_identity
import Theorems.Thm_Formalism_REAL_compact_casimir_preserves_filtration
import Theorems.Thm_Formalism_REAL_casimir_scalar_on_filtration

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
    {c : ℂ} (hcas : ∀ w ∈ W, ∀ g, inUJ ε g → CasF ε w g = c * w g)
    {k : ℕ} {x : SmoothFunctionsModGroup ε} (hx : x ∈ wordFiltration ε W k) : signedCasimirQuotient ε x ∈ wordFiltration ε W k := by
  unfold signedCasimirQuotient
  rw [signed_casimir_identity, LinearMap.sub_apply, LinearMap.smul_apply, casimir_scalar_on_filtration hsm hcas hx]
  exact sub_mem (Submodule.smul_mem _ _ (compact_casimir_preserves_filtration hsm hstab hx)) (Submodule.smul_mem _ _ hx)
end Formalism.REAL
