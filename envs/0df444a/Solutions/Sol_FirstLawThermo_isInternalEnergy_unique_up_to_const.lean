-- Prove2me | solution 1 for FirstLawThermo.isInternalEnergy_unique_up_to_const
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T13:15:22.348162+00:00
-- url     : https://prove2.me/submissions/d6ee1fea-2108-4561-9dec-ec508174db35

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem solution {σ : Type*}
    (procs : Set (Process σ)) (O : σ) (hlink : AdiabaticallyLinkedTo procs O)
    (U U' : σ → ℝ) (hU : IsInternalEnergy procs U) (hU' : IsInternalEnergy procs U') :
    ∃ c : ℝ, ∀ A : σ, U' A = U A + c := by
  refine ⟨U' O - U O, fun A => ?_⟩
  obtain ⟨p, hp, had, hdir⟩ := hlink A
  have h := hU p hp had
  have h' := hU' p hp had
  rcases hdir with ⟨hs, hf⟩ | ⟨hs, hf⟩
  · rw [hs, hf] at h h'
    linarith
  · rw [hs, hf] at h h'
    linarith
