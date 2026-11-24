-- Prove2me | solution 1 for Formalism.L2.Pj.LieAlg.exists_divisor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:16:55.028953+00:00
-- url     : https://prove2.me/submissions/6b6e9784-dec4-451d-b273-ba6d62c68db3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LieAlg
open Submodule
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]
namespace Formalism.L2.Pj.LieAlg
theorem _root_.solution (s : Finset K) : ∃ t : K, (t = 0 → ∀ x ∈ s, x = 0) ∧ (t = 0 ∨ t ∈ s) ∧
    ∀ x ∈ s, ∃ r : V, x = algebraMap V K r * t := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, Or.inl rfl, by simp⟩
  | insert a s ha ih =>
    obtain ⟨t, h0, hts, hdiv⟩ := ih
    by_cases ht : t = 0
    · have hs := h0 ht
      refine ⟨a, fun hz x hx => ?_, Or.inr (Finset.mem_insert_self a s), fun x hx => ?_⟩
      · rcases Finset.mem_insert.1 hx with hx | hx
        · rw [hx]; exact hz
        · exact hs x hx
      · rcases Finset.mem_insert.1 hx with hx | hx
        · exact ⟨1, by simp [hx]⟩
        · exact ⟨0, by simp [hs x hx]⟩
    · have hts' : t = 0 ∨ t ∈ insert a s := by
        rcases hts with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_insert_of_mem h)
      by_cases haz : a = 0
      · refine ⟨t, fun h => absurd h ht, hts', fun x hx => ?_⟩
        rcases Finset.mem_insert.1 hx with hx | hx
        · exact ⟨0, by simp [hx, haz]⟩
        · exact hdiv x hx
      · rcases (ValuationRing.iff_isInteger_or_isInteger V K).1 inferInstance (a / t) with ⟨r, hr⟩ | ⟨r, hr⟩
        · refine ⟨t, fun h => absurd h ht, hts', fun x hx => ?_⟩
          rcases Finset.mem_insert.1 hx with hx | hx
          · exact ⟨r, by rw [hx, hr]; field_simp⟩
          · exact hdiv x hx
        · refine ⟨a, fun h => absurd h haz, Or.inr (Finset.mem_insert_self a s), fun x hx => ?_⟩
          rcases Finset.mem_insert.1 hx with hx | hx
          · exact ⟨1, by simp [hx]⟩
          · obtain ⟨q, hq⟩ := hdiv x hx
            refine ⟨q * r, ?_⟩
            rw [hq, map_mul, hr]
            field_simp
end Formalism.L2.Pj.LieAlg
