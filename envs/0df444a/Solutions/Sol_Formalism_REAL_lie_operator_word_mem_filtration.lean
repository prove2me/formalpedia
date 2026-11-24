-- Prove2me | solution 1 for Formalism.REAL.lie_operator_word_mem_filtration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:01:09.416595+00:00
-- url     : https://prove2.me/submissions/b5782601-196e-413e-8113-dacd90b498bb

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
import Theorems.Thm_Formalism_REAL_word_mem_filtration
import Theorems.Thm_Formalism_REAL_lie_operator_raises_filtration
import Theorems.Thm_Formalism_REAL_weight_vectors_stable

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
    {c d : Fin n} (hcd : ε c = ε d) {m : SmoothFunctionsModGroup ε} (hm : m ∈ weightVectorsQuotient ε W) :
    ∀ w : List (Fin n × Fin n), lieOperatorQuotient ε c d (wordActionQuotient ε w m) ∈ wordFiltration ε W w.length
  | [] => word_mem_filtration (w := []) (weight_vectors_stable hsm hstab hm hcd) le_rfl
  | p :: w => by
    have ih := solution hsm hstab hcd hm w
    have hgl := lie_operators_gl_relations (ε := ε) c d p.1 p.2
    have key : lieOperatorQuotient ε c d (lieOperatorQuotient ε p.1 p.2 (wordActionQuotient ε w m)) =
        lieOperatorQuotient ε p.1 p.2 (lieOperatorQuotient ε c d (wordActionQuotient ε w m)) +
          ((if d = p.1 then lieOperatorQuotient ε c p.2 else 0) (wordActionQuotient ε w m) -
            (if p.2 = c then lieOperatorQuotient ε p.1 d else 0) (wordActionQuotient ε w m)) := by
      have := congrArg (fun T => T (wordActionQuotient ε w m)) hgl
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
      rw [← this]; abel
    show lieOperatorQuotient ε c d (lieOperatorQuotient ε p.1 p.2 (wordActionQuotient ε w m)) ∈ wordFiltration ε W (w.length + 1)
    rw [key]
    refine add_mem (lie_operator_raises_filtration _ _ ih) (sub_mem ?_ ?_)
    · split_ifs
      · exact word_mem_filtration (w := (c, p.2) :: w) hm (by simp)
      · rw [LinearMap.zero_apply]; exact zero_mem _
    · split_ifs
      · exact word_mem_filtration (w := (p.1, d) :: w) hm (by simp)
      · rw [LinearMap.zero_apply]; exact zero_mem _
end Formalism.REAL
