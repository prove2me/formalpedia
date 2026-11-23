-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.OrdGE.pow_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:40.33775+00:00
-- url     : https://prove2.me/submissions/75bd47f4-9e37-4eb2-8616-b137535dfea7

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mono
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow

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
theorem _root_.solution {f g : MvPowerSeries Z k} {n : ℕ} (hf : OrdGE 1 f) (hg : OrdGE 1 g)
    (hfg : OrdGE (n + 1) (f - g)) {N : ℕ} (hN : 1 ≤ N) : OrdGE (n + N) (f ^ N - g ^ N) := by
  rw [← geom_sum₂_mul]
  have hs : OrdGE (N - 1) (∑ i ∈ Finset.range N, f ^ i * g ^ (N - 1 - i)) := by
    refine OrdGE.sum _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact OrdGE.mono (show N - 1 ≤ i + (N - 1 - i) by omega) ((hf.pow i).mul (hg.pow (N - 1 - i)))
  exact OrdGE.mono (by omega) (hs.mul hfg)
end OrdGE
end Formalism.BaseCaseIdentities
