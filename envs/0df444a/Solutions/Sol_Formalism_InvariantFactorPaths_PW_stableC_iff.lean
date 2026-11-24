-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.stableC_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:36.623461+00:00
-- url     : https://prove2.me/submissions/5d74a237-5f4b-49f3-87ab-51a2304f899d

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
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) :
    GlStableC p LL j Cs S ↔ (GAe p LL j (enumC Cs)).Stable S := by
  constructor
  · intro h a b x hx
    exact h _ (enumC_mem Cs a) _ (enumC_mem Cs b) x hx
  · intro h c hc d hd x hx
    obtain ⟨a, rfl⟩ := enumC_surj Cs hc
    obtain ⟨b, rfl⟩ := enumC_surj Cs hd
    exact h a b x hx
end Formalism.InvariantFactorPaths.PW
