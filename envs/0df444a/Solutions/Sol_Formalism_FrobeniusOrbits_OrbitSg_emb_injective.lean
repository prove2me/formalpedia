-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.OrbitSg.emb_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:37:46.189897+00:00
-- url     : https://prove2.me/submissions/feb46f17-af09-427c-af0c-a036947735f5

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitCountSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Theorems.Thm_Formalism_FrobeniusOrbits_OrbitSg_sg_fst_ne_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.FrobeniusOrbits.OrbitSg
namespace Formalism.FrobeniusOrbits.OrbitSg
theorem _root_.solution {e : ℕ} (τ : GG e) : Function.Injective (emb τ) := by
  rintro ⟨s, t⟩ ⟨s', t'⟩ h
  simp only [emb, Prod.mk.injEq, mul_left_inj] at h
  obtain ⟨h1, h2⟩ := h
  refine Prod.ext ?_ h2
  have hne := sg_fst_ne_one e
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or s' with rfl | rfl
  · rfl
  · simp at h1; exact absurd h1.symm hne
  · simp at h1; exact absurd h1 hne
  · rfl
end Formalism.FrobeniusOrbits.OrbitSg
