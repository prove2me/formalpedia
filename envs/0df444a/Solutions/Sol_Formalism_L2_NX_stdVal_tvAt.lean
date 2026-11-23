-- Prove2me | solution 1 for Formalism.L2.NX.stdVal_tvAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:58.058506+00:00
-- url     : https://prove2.me/submissions/44a2fccd-c318-42de-b5fb-cf0aef15c609

import Mathlib
import Definitions.Def_Formalism_AlgebraicWeights_IsAlgWeight
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs
import Theorems.Thm_Formalism_L2_NX_supSum_tv
import Theorems.Thm_Formalism_L2_NX_tvAt_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.NX
variable {ι : Type} [Fintype ι] {p : ι → ℕ} {r : ℕ}
namespace Formalism.L2.NX
theorem _root_.solution [DecidableEq ι] {K : Type} [Field K] (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ)
    (hr : 2 ≤ r) (x : ι) : stdVal p r θ (tvAt hr x) = θ x (Multiplicative.ofAdd 1) := by
  simp only [stdVal]
  rw [Finset.prod_eq_single x]
  · rw [tvAt_apply, if_pos rfl, supSum_tv]
  · intro y _ hy
    rw [tvAt_apply, if_neg hy, supSum_one, ofAdd_zero, map_one]
  · intro h
    exact absurd (Finset.mem_univ x) h
end Formalism.L2.NX
