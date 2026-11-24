-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.comp_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:17.260254+00:00
-- url     : https://prove2.me/submissions/9bc8222c-7b3b-41c3-ad7c-da6ceaa29782

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_enumC_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_enumC_surj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (Cs : Finset (Fin r)) (la la' : Fin r → ℤ) :
    la ∘ enumC Cs = la' ∘ enumC Cs ↔ ∀ c ∈ Cs, la c = la' c := by
  constructor
  · intro h c hc
    obtain ⟨a, rfl⟩ := enumC_surj Cs hc
    exact congrFun h a
  · intro h
    funext a
    exact h _ (enumC_mem Cs a)
end Formalism.InvariantFactorPaths.PW
