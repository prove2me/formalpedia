-- Prove2me | solution 1 for BookProof.HermiteCarleman.mem_cube_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-10T18:17:36.583742+00:00
-- url     : https://prove2.me/submissions/c4008e6b-58bf-4dc6-a4e3-96aabc1ea8a2

-- Generated from ChapterHermiteCarlemanEsa.lean — solution of BookProof.HermiteCarleman.mem_cube_inc
import Mathlib
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {d N : ℕ} {a : Fin d →₀ ℕ} : a ∈ cube d N ↔ ∀ i, a i ≤ N := by
  classical
  constructor
  · intro h
    rw [cube, Finset.mem_image] at h
    obtain ⟨f, hf, rfl⟩ := h
    intro i
    have h2 := (Fintype.mem_piFinset.mp hf) i
    have h3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp h2)
    simpa [Finsupp.equivFunOnFinite] using h3
  · intro h
    rw [cube, Finset.mem_image]
    exact ⟨Finsupp.equivFunOnFinite a, Fintype.mem_piFinset.mpr
      (fun i => Finset.mem_range.mpr (Nat.lt_succ_of_le (h i))), by simp⟩
