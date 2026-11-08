-- Prove2me | solution 1 for FlexMargin.remark_def21_def22
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:44:03.025646+00:00
-- url     : https://prove2.me/submissions/670f3a26-5bcd-4c70-8c24-d10234c4480e

import Mathlib
import Definitions.Def_FlexMargin_IsPartwiseSymm
import Definitions.Def_FlexMargin_IsPartwiseSymmAround

open FlexMargin in
theorem solution {n T : ℕ} (cat : Fin n → Fin T) (U : Set (Fin n → ℝ)) :
    IsPartwiseSymm cat U ↔ ∃ c : ℝ, IsPartwiseSymmAround cat (fun _ => c) U := by
  constructor
  · rintro ⟨hnn, hcore⟩
    refine ⟨0, hnn, ?_⟩
    have h : {e | ∃ d ∈ U, e = d - fun _ => (0 : ℝ)} = U := by
      ext e
      constructor
      · rintro ⟨d, hd, rfl⟩
        have : (d - fun _ => (0 : ℝ)) = d := by funext i; simp
        rw [this]; exact hd
      · intro he
        exact ⟨e, he, by funext i; simp⟩
    rw [h]; exact hcore
  · rintro ⟨c, hnn, ⟨Ut, hU⟩, hperm⟩
    refine ⟨hnn, ⟨fun t => {f | (fun i => f i - c) ∈ Ut t}, ?_⟩, ?_⟩
    · ext d
      have key : d ∈ U ↔ (d - fun _ => c) ∈ {e | ∃ d ∈ U, e = d - fun _ => c} := by
        constructor
        · intro h; exact ⟨d, h, rfl⟩
        · rintro ⟨d', hd', he⟩
          have : d = d' := by
            funext i
            have := congrFun he i
            simp only [Pi.sub_apply] at this
            linarith
          rw [this]; exact hd'
      rw [key, hU]
      exact Iff.rfl
    · intro d hd σ hσ
      obtain ⟨d', hd', he⟩ := hperm (d - fun _ => c) ⟨d, hd, rfl⟩ σ hσ
      have : (fun i => d (σ i)) = d' := by
        funext i
        have := congrFun he i
        simp only [Pi.sub_apply] at this
        linarith
      rw [this]; exact hd'
