-- Prove2me | solution 1 for Formalism.QuantumDeterminants.S_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:03.920973+00:00
-- url     : https://prove2.me/submissions/27b46ffc-6c1b-4488-8b75-f5cacd0abb6c

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Theorems.Thm_Formalism_QuantumDeterminants_UW_F
import Theorems.Thm_Formalism_QuantumDeterminants_N_F
import Theorems.Thm_Formalism_QuantumDeterminants_Uof_lower_zero
import Theorems.Thm_Formalism_QuantumDeterminants_Uof_diag

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
theorem _root_.solution {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hs : s ∈ Sset k r z) :
    ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, (∀ c a, a < c → U c a = 0) ∧ (∀ c, U c c = 1) ∧
      s * Fm k r z = Fm k r z * U := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  refine ⟨Uof k r z m, fun c a hac => Uof_lower_zero hm c a hac, fun c => Uof_diag hm c, ?_⟩
  rw [Matrix.mul_assoc, N_F hz hm, ← Matrix.mul_assoc, UW_F hh]
end Formalism.QuantumDeterminants
