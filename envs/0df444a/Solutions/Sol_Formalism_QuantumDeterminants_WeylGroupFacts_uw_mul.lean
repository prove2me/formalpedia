-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.uw_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:45:07.419013+00:00
-- url     : https://prove2.me/submissions/575f366b-e673-478f-9a0e-6d01f53f01ff

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul

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
open Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace Formalism.QuantumDeterminants.WeylGroupFacts
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ}
    {h h' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (hh' : h' ∈ UWset k r z) : h * h' ∈ UWset k r z := by
  simp only [UWset, Set.mem_setOf_eq] at hh hh' ⊢
  obtain ⟨hU, hfix, hz⟩ := hh
  obtain ⟨hU', hfix', hz'⟩ := hh'
  have key : ∀ v, h *ᵥ v = v → h' *ᵥ v = v → (h * h') *ᵥ v = v := by
    intro v hv hv'
    rw [← Matrix.mulVec_mulVec, hv', hv]
  exact ⟨uh_mul hU hU', fun a => ⟨key _ (hfix a).1 (hfix' a).1, key _ (hfix a).2 (hfix' a).2⟩,
    key _ hz hz'⟩
end Formalism.QuantumDeterminants.WeylGroupFacts
