-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.eq_of_ordGE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:10.402535+00:00
-- url     : https://prove2.me/submissions/4d1e433b-8939-495b-a420-56fbed6c5285

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
theorem _root_.solution {f g : MvPowerSeries Z k} (h : ∀ n : ℕ, OrdGE (n + 1) (f - g)) : f = g := by
  ext A
  have h0 := h A.degree A (Nat.lt_succ_self _)
  rw [map_sub, sub_eq_zero] at h0
  exact h0
end Formalism.BaseCaseIdentities
