-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.HasWtG.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:53:00.891271+00:00
-- url     : https://prove2.me/submissions/39dab146-afd3-4dc9-b6c3-4ff2ed768e83

import Definitions.Def_Formalism_FrobeniusBaseCase_CoeffOfFirstMultiplier
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
variable {k : Type*} [Field k] {S : Type*} {v : AddValuation k (WithTop ℝ)}
namespace Formalism.BaseCaseIdentities
namespace HasWtG
theorem _root_.solution {ω : (S →₀ ℕ) →+ ℝ} {w1 w2 : ℝ} {f g : MvPowerSeries S k}
    (hf : HasWtG v ω w1 f) (hg : HasWtG v ω w2 g) : HasWtG v ω (w1 + w2) (f * g) := by
  intro E
  rw [le_add_coe_iff, coeff_mul]
  refine v.map_le_sum fun p hp => ?_
  rw [v.map_mul]
  have hE : E = p.1 + p.2 := (Finset.HasAntidiagonal.mem_antidiagonal.1 hp).symm
  have : ((w1 + w2 - ω E : ℝ) : WithTop ℝ)
      = ((w1 - ω p.1 : ℝ) : WithTop ℝ) + ((w2 - ω p.2 : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_add, hE, map_add]; congr 1; ring
  rw [this]
  exact add_le_add ((le_add_coe_iff _ _ _).1 (hf p.1)) ((le_add_coe_iff _ _ _).1 (hg p.2))
end HasWtG
end Formalism.BaseCaseIdentities
