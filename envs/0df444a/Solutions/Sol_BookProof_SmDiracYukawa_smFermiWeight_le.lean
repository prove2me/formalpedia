-- Prove2me | solution 1 for BookProof.SmDiracYukawa.smFermiWeight_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:35:25.422177+00:00
-- url     : https://prove2.me/submissions/3c0e41c8-bdb3-4b54-84bb-e8ab060dcf39

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.smFermiWeight_le
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterFarisLavine
open BookProof.SmDiracYukawa




open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {om : Fin n → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0)
    (S : Finset (Fin n)) :
    |smFermiWeight om c0 S| ≤ (∑ i : Fin n, om i) + c0 := by

  have hle : ∑ i ∈ S, om i ≤ ∑ i : Fin n, om i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun i _ _ => hom i
  have hnn : 0 ≤ ∑ i ∈ S, om i := Finset.sum_nonneg fun i _ => hom i
  rw [abs_of_nonneg (by simp only [smFermiWeight]; linarith)]
  simp only [smFermiWeight]
  linarith
