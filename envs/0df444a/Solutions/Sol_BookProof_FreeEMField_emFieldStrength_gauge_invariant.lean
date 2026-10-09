-- Prove2me | solution 1 for BookProof.FreeEMField.emFieldStrength_gauge_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:16:49.568002+00:00
-- url     : https://prove2.me/submissions/7ab01d03-b7ca-40fd-bd56-a741e206dd1e

-- Generated from ChapterFreeEMField.lean — solution of BookProof.FreeEMField.emFieldStrength_gauge_invariant
import Mathlib
import Definitions.Def_ChapterFreeEMField
open BookProof.FreeEMField




open BookProof.YangMillsFieldStrength


variable {R : Type*} [Ring R]

variable {R : Type*} [Ring R]

set_option maxHeartbeats 1000000 in
theorem solution
    (δ : Fin 3 → R → R) (A : Fin 3 → R) (θ : R)
    (hadd : ∀ j x y, δ j (x + y) = δ j x + δ j y)
    (hcomm : ∀ j k x, δ j (δ k x) = δ k (δ j x))
    (j k : Fin 3) :
    emFieldStrength δ (fun i => A i + δ i θ) j k = emFieldStrength δ A j k := by

  simp only [emFieldStrength, hadd]
  rw [hcomm j k θ]; abel
