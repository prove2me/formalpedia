-- Prove2me | solution 1 for Formalism.QuantumDeterminants.fvec_apply_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:13.846089+00:00
-- url     : https://prove2.me/submissions/7d7a53ef-a2ad-4b83-ba2f-7c78e5a777a5

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ)
    (c : Fin (r + 1)) (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val) :
    fvec k r z c i = if c.val = r then z i else 0 := by
  unfold fvec
  split_ifs with hc h1 h1
  · omega
  · simp [bvec, eI, Pi.single_apply, Fin.ext_iff] <;> omega
  · rfl
  · have := c.isLt
    omega
end Formalism.QuantumDeterminants
