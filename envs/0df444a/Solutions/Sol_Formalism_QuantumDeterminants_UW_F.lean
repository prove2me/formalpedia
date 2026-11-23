-- Prove2me | solution 1 for Formalism.QuantumDeterminants.UW_F
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:36.433322+00:00
-- url     : https://prove2.me/submissions/bca94e8b-8cd5-4083-bc75-33692da3b491

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
theorem _root_.solution {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    h * Fm k r z = Fm k r z := by
  ext i a
  change (h *ᵥ fvec k r z a) i = fvec k r z a i
  unfold fvec
  split_ifs with ha
  · rw [(hh.2.1 ⟨a.val, ha⟩).1]
  · rw [hh.2.2]
end Formalism.QuantumDeterminants
