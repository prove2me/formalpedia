-- Prove2me | solution 1 for Formalism.MainNotions.FormalGroupSystem.Pf.pivot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:40:10.152414+00:00
-- url     : https://prove2.me/submissions/13286884-15e8-4d7f-930f-a2baac06fbbb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_DescentCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf
open Finset
namespace Formalism.MainNotions.FormalGroupSystem.Pf
theorem _root_.solution {K κ : Type*} [Field K] (R : Subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) (f : κ → K) (s : Finset κ) :
    (∃ k ∈ s, f k ≠ 0) → ∃ k0 ∈ s, f k0 ≠ 0 ∧ ∀ k ∈ s, f k / f k0 ∈ R := by
  classical
  induction s using Finset.induction_on with
  | empty => intro h; simp at h
  | insert a s ha ih =>
    intro h
    by_cases hs : ∃ k ∈ s, f k ≠ 0
    · obtain ⟨k0, hk0, hfk0, hR0⟩ := ih hs
      by_cases hfa : f a / f k0 ∈ R
      · refine ⟨k0, Finset.mem_insert_of_mem hk0, hfk0, ?_⟩
        intro k hk
        rcases Finset.mem_insert.1 hk with rfl | hk
        · exact hfa
        · exact hR0 k hk
      · have hinv : f k0 / f a ∈ R := by
          have := (hR (f a / f k0)).resolve_left hfa
          rwa [inv_div] at this
        have hfa0 : f a ≠ 0 := by
          intro h0; apply hfa; rw [h0, zero_div]; exact R.zero_mem
        refine ⟨a, Finset.mem_insert_self a s, hfa0, ?_⟩
        intro k hk
        rcases Finset.mem_insert.1 hk with rfl | hk
        · rw [div_self hfa0]; exact R.one_mem
        · have : f k / f a = (f k / f k0) * (f k0 / f a) := by field_simp
          rw [this]; exact R.mul_mem (hR0 k hk) hinv
    · push_neg at hs
      have hfa0 : f a ≠ 0 := by
        obtain ⟨k, hk, hfk⟩ := h
        rcases Finset.mem_insert.1 hk with rfl | hk
        · exact hfk
        · exact absurd (hs k hk) hfk
      refine ⟨a, Finset.mem_insert_self a s, hfa0, ?_⟩
      intro k hk
      rcases Finset.mem_insert.1 hk with rfl | hk
      · rw [div_self hfa0]; exact R.one_mem
      · rw [hs k hk, zero_div]; exact R.zero_mem
end Formalism.MainNotions.FormalGroupSystem.Pf
