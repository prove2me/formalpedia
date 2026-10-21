-- Prove2me | solution 1 for DynFairDiv.Uniform.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T12:00:39.884567+00:00
-- url     : https://prove2.me/submissions/7586c913-c18a-4f2e-accf-9247d7345346

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model

open DynFairDiv.Uniform

theorem solution (ψ ψ' : ℕ → ℕ) (n n' : ℕ∞) (hn' : 1 ≤ n') (hle : n' ≤ n)
    (hpre : ∀ t : ℕ, 1 ≤ t → (t : ℕ∞) ≤ n' → ψ' t = ψ t) :
    fairnessRatio ψ n ≤ fairnessRatio ψ' n' := by
  unfold fairnessRatio
  apply csSup_le_csSup
  · refine ⟨1, ?_⟩
    rintro σ ⟨X, hF, hR⟩
    have h1 := hR 1 le_rfl (by exact_mod_cast hn') 0 one_pos
    have h2 := (hF 1 le_rfl (by exact_mod_cast hn')).2.1
    simp at h1 h2
    linarith
  · refine ⟨0, fun _ => 0, ?_, ?_⟩
    · intro t _ _
      refine ⟨fun _ _ => le_rfl, by simp, fun _ => by simp⟩
    · intro t _ _ k _
      simp
  · rintro σ ⟨X, hF, hR⟩
    refine ⟨X, ?_, ?_⟩
    · intro t ht htn
      obtain ⟨a, b, c⟩ := hF t ht (htn.trans hle)
      exact ⟨a, b, fun h2 => (hpre t ht htn) ▸ c h2⟩
    · intro t ht htn
      exact hR t ht (htn.trans hle)
