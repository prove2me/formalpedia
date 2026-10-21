-- Prove2me | solution 2 for DynFairDiv.Uniform.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:17:04.526721+00:00
-- url     : https://prove2.me/submissions/17713ee7-b121-4ed5-86a8-0d1cf58ed716

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model

set_option autoImplicit false
open DynFairDiv.Uniform

theorem solution (ψ ψ' : ℕ → ℕ) (n n' : ℕ∞) (hn' : 1 ≤ n') (hle : n' ≤ n)
    (hpre : ∀ t : ℕ, 1 ≤ t → (t : ℕ∞) ≤ n' → ψ' t = ψ t) :
    fairnessRatio ψ n ≤ fairnessRatio ψ' n' := by
  unfold fairnessRatio
  have hne : {σ : ℝ | ∃ X, AchievesRatio ψ n σ X}.Nonempty := by
    refine ⟨0, fun _ _ => 0, ?_, ?_⟩
    · intro t _ _
      refine ⟨fun _ _ => le_refl _, by simp, fun _ => by simp⟩
    · intro t _ _ k _
      simp
  have hbdd : BddAbove {σ : ℝ | ∃ X, AchievesRatio ψ' n' σ X} := by
    refine ⟨1, ?_⟩
    rintro σ ⟨X, ⟨hf, hr⟩⟩
    have h1 : ((1 : ℕ) : ℕ∞) ≤ n' := by simpa using hn'
    obtain ⟨h0, hs, -⟩ := hf 1 le_rfl h1
    have := hr 1 le_rfl h1 0 (by norm_num)
    simp at this hs
    linarith
  apply csSup_le_csSup hbdd hne
  rintro σ ⟨X, ⟨hf, hr⟩⟩
  refine ⟨X, ⟨?_, ?_⟩⟩
  · intro t ht1 htn
    obtain ⟨a, b, c⟩ := hf t ht1 (htn.trans hle)
    refine ⟨a, b, fun h2 => ?_⟩
    rw [hpre t ht1 htn]
    exact c h2
  · intro t ht1 htn k hk
    exact hr t ht1 (htn.trans hle) k hk
