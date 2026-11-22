-- Prove2me | solution 1 for Formalism.QuantumDeterminants.fvec_apply_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:39.824868+00:00
-- url     : https://prove2.me/submissions/02670cab-7cc9-4197-a034-0e9fc466ee03

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
theorem _root_.solution {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (c : Fin (r + 1)) (i : Fin (2 * r + k + 1)) (hi : i.val < r) :
    fvec k r z c i = if c.val = i.val then 1 else 0 := by
  unfold fvec
  split_ifs with hc h1 h1
  · simp [bvec, eI, Pi.single_apply, Fin.ext_iff, h1]
  · simp [bvec, eI, Pi.single_apply, Fin.ext_iff] <;> omega
  · omega
  · exact hz i (Or.inl hi)
end Formalism.QuantumDeterminants
