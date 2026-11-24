-- Prove2me | solution 1 for Formalism.REAL.casimir_scalar_on_filtration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:01:33.923178+00:00
-- url     : https://prove2.me/submissions/8d952f00-1c06-4dc7-99e6-7ab2bc6eba40

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
import Theorems.Thm_Formalism_REAL_lie_operators_gl_relations
import Theorems.Thm_Formalism_REAL_casimir_quotient_mk
import Theorems.Thm_Formalism_REAL_word_action_smul
import Theorems.Thm_Formalism_REAL_word_action_commute
import Theorems.Thm_Formalism_REAL_casimir_central_holds


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
theorem _root_.solution (hsm : ∀ w ∈ W, SmoothOnG ε w) {c : ℂ}
    (hcas : ∀ w ∈ W, ∀ g, inUJ ε g → CasF ε w g = c * w g)
    {k : ℕ} {x : SmoothFunctionsModGroup ε} (hx : x ∈ wordFiltration ε W k) : Cas (lieOperatorQuotient ε) x = c • x := by
  have hcomm := (casimir_central_holds (Module.End ℂ (SmoothFunctionsModGroup ε)) n ε (lieOperatorQuotient ε) lie_operators_gl_relations).1
  have : wordFiltration ε W k ≤ LinearMap.ker (Cas (lieOperatorQuotient ε) - c • (1 : Module.End ℂ (SmoothFunctionsModGroup ε))) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨w, m, ⟨f, hfW, hf, rfl⟩, _, rfl⟩
    show (Cas (lieOperatorQuotient ε) - c • (1 : Module.End ℂ (SmoothFunctionsModGroup ε))) _ = 0
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero,
      word_action_commute _ hcomm, ← word_action_smul]
    congr 1
    rw [casimir_quotient_mk, ← quotient_mk_smul, quotient_mk_eq_iff]
    intro g hg
    show CasF ε f g = c * f g
    exact hcas f hfW g hg
  have h := this hx
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_eq_zero] at h
  exact h
end Formalism.REAL
