-- Prove2me | solution 1 for BookProof.FreeEMField.emFieldStrength_isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:17:15.528482+00:00
-- url     : https://prove2.me/submissions/3414799a-547c-4585-874a-7ba6a4ba4e07

-- Generated from ChapterFreeEMField.lean — solution of BookProof.FreeEMField.emFieldStrength_isSelfAdjoint
import Mathlib
import Definitions.Def_ChapterFreeEMField
open BookProof.FreeEMField




open BookProof.YangMillsFieldStrength


variable {R : Type*} [Ring R]

variable {R : Type*} [Ring R]
variable {R : Type*} [Ring R] [Algebra ℂ R]
variable {R : Type*} [Ring R] [StarRing R]

set_option maxHeartbeats 1000000 in
theorem solution
    (δ : Fin 3 → R → R) (π : Fin 3 → R)
    (hstar : ∀ (j : Fin 3) x, star (δ j x) = δ j (star x))
    (hsa : ∀ i, IsSelfAdjoint (π i)) (j k : Fin 3) :
    IsSelfAdjoint (emFieldStrength δ π j k) := by

  change star (δ j (π k) - δ k (π j)) = δ j (π k) - δ k (π j)
  rw [star_sub, hstar, hstar, (hsa k).star_eq, (hsa j).star_eq]
