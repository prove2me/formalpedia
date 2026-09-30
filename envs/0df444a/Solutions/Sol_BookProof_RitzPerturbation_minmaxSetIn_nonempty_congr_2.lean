-- Prove2me | solution 2 for BookProof.RitzPerturbation.minmaxSetIn_nonempty_congr
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T18:44:49.366422+00:00
-- url     : https://prove2.me/submissions/2c84a55e-346d-4161-9dc8-4d0600e56f6b

-- Generated from ChapterSirkRitzPerturbation.lean — solution of BookProof.RitzPerturbation.minmaxSetIn_nonempty_congr
import Mathlib
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation









noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (T T' : F →L[ℂ] F) {W : Submodule ℂ F} {k : ℕ}
    (h : (minmaxSetIn T W k).Nonempty) : (minmaxSetIn T' W k).Nonempty := by

  obtain ⟨t, S, hSW, hrank, -⟩ := h
  exact ⟨rayleighSup T' S, S, hSW, hrank, rfl⟩
