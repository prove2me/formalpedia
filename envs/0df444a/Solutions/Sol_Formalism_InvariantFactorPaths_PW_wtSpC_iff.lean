-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.wtSpC_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:41:39.773788+00:00
-- url     : https://prove2.me/submissions/150aa81c-eb3d-491a-91ea-03fbbd0af1a0

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_isWt_iff
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
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ WtSpC p LL j Cs la ↔ (GAe p LL j (enumC Cs)).IsWt (la ∘ enumC Cs) x := by
  rw [GAe_isWt_iff, WtSpC]
  have : {m : Fin N × Fin r →₀ ℕ | ∀ c ∈ Cs, wt LL j c m = la c} =
      {m | ∀ a, wt LL j (enumC Cs a) m = (la ∘ enumC Cs) a} := by
    ext m
    constructor
    · intro h a; exact h _ (enumC_mem Cs a)
    · intro h c hc
      obtain ⟨a, rfl⟩ := enumC_surj Cs hc
      exact h a
  rw [this]
end Formalism.InvariantFactorPaths.PW
