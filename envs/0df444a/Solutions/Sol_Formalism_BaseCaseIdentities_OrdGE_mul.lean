-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.OrdGE.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:43.417839+00:00
-- url     : https://prove2.me/submissions/06f653fe-85b4-4ff0-b9b3-f495dc747bb6

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint

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
variable {k : Type*} [Field k] {Z : Type*} {C : Type*}
namespace Formalism.BaseCaseIdentities
namespace OrdGE
theorem _root_.solution {a b : ℕ} {f g : MvPowerSeries Z k} (hf : OrdGE a f) (hg : OrdGE b g) :
    OrdGE (a + b) (f * g) := by
  intro A hA
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' : p.1 + p.2 = A := by simpa using hp
  have hd : p.1.degree + p.2.degree = A.degree := by
    rw [← hp', map_add]
  by_cases h1 : p.1.degree < a
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]
end OrdGE
end Formalism.BaseCaseIdentities
