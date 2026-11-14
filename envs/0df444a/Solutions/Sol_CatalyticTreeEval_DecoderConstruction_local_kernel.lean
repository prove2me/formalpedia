-- Prove2me | solution 1 for CatalyticTreeEval.DecoderConstruction.local_kernel
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-14T01:36:25.153229+00:00
-- url     : https://prove2.me/submissions/25513294-8833-4151-9278-8e27a527d6e5

import Definitions.Def_CatalyticTreeEval_DecoderConstruction

set_option autoImplicit false

namespace CatalyticTreeEval.DecoderConstruction

theorem localTerm_sum {R : Type} [CommRing R] [DecidableEq R] (z : R) :
    ∑ c : Fin 3, localTerm c z =
      -(if z = -2 then 1 else 0) +
      ((if z = 0 then 1 else 0) + (if z = -1 then 1 else 0)) -
      (if z = 1 then 1 else 0) := by
  classical
  simp [Fin.sum_univ_succ, localTerm]
  ring

theorem local_normalization {R : Type} [CommRing R] [DecidableEq R]
    (h1 : (1 : R) ≠ 0) (h2 : (2 : R) ≠ 0) :
    ∑ c : Fin 3, localTerm c (0 : R) = 1 := by
  classical
  rw [localTerm_sum]
  have hneg1 : (0 : R) ≠ -1 := by
    intro h
    apply h1
    linear_combination h
  have hneg2 : (0 : R) ≠ -2 := by
    intro h
    apply h2
    linear_combination h
  simp [hneg1, hneg2, Ne.symm h1]

theorem local_cancel_one {R : Type} [CommRing R] [DecidableEq R] (z : R) :
    ∑ c : Fin 3, localTerm c (z + (c.val : R)) = 0 := by
  classical
  have h1 : z + 1 = 0 ↔ z = -1 := by
    constructor <;> intro h <;> linear_combination h
  have h2 : z + 1 = -1 ↔ z = -2 := by
    constructor <;> intro h <;> linear_combination h
  have h3 : z + 2 = 1 ↔ z = -1 := by
    constructor <;> intro h <;> linear_combination h
  norm_num [Fin.sum_univ_succ, localTerm]
  simp only [h1, h2, h3]
  ring

theorem local_cancel_two {R : Type} [CommRing R] [DecidableEq R] (z : R) :
    ∑ c : Fin 3, localTerm c (z + 2 * (c.val : R)) = 0 := by
  classical
  have h1 : z + 2 = 0 ↔ z = -2 := by
    constructor <;> intro h <;> linear_combination h
  have h2 : z + 2 = -1 ↔ z = -3 := by
    constructor <;> intro h <;> linear_combination h
  have h3 : z + 4 = 1 ↔ z = -3 := by
    constructor <;> intro h <;> linear_combination h
  norm_num [Fin.sum_univ_succ, localTerm]
  simp only [h1, h2, h3]
  ring

end CatalyticTreeEval.DecoderConstruction

open CatalyticTreeEval.DecoderConstruction

theorem solution {R : Type} [CommRing R] [DecidableEq R]
    (h1 : (1 : R) ≠ 0) (h2 : (2 : R) ≠ 0) :
    (∑ c : Fin 3, localTerm c (0 : R) = 1) ∧
    (∀ z : R, ∑ c : Fin 3, localTerm c (z + (c.val : R)) = 0) ∧
    (∀ z : R, ∑ c : Fin 3, localTerm c (z + 2 * (c.val : R)) = 0) := by
  exact ⟨local_normalization h1 h2, local_cancel_one, local_cancel_two⟩
