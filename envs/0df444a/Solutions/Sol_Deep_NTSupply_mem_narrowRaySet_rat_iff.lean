-- Prove2me | solution 1 for Deep.NTSupply.mem_narrowRaySet_rat_iff
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T23:05:41.41697+00:00
-- url     : https://prove2.me/submissions/ddd16b70-f2b6-47f2-b01b-edc773ea52e9

import Definitions.Def_NarrowRayClassGroup
import Theorems.Thm_Rat_ringOfIntegers_pos_iff_all_real_embeddings
import Theorems.Thm_Rat_mem_span_nat_iff_congruence

open NumberField nonZeroDivisors Deep.NTSupply

theorem solution (n : ℕ)
    (I : (FractionalIdeal ((NumberField.RingOfIntegers ℚ)⁰) ℚ)ˣ) :
    I ∈ narrowRaySet ℚ (Ideal.span {(n : NumberField.RingOfIntegers ℚ)}) ↔
      ∃ a : NumberField.RingOfIntegers ℚ, a ≠ 0 ∧
        0 < Rat.ringOfIntegersEquiv a ∧
        (∃ k : ℤ, Rat.ringOfIntegersEquiv a = 1 + (n : ℤ) * k) ∧
        (I : FractionalIdeal ((NumberField.RingOfIntegers ℚ)⁰) ℚ) =
          ((Ideal.span {a} : Ideal (NumberField.RingOfIntegers ℚ)) :
            FractionalIdeal ((NumberField.RingOfIntegers ℚ)⁰) ℚ) := by
  rw [mem_narrowRaySet_iff]
  constructor
  · rintro ⟨a, ha0, ha1, hpos, hI⟩
    exact ⟨a, ha0, (Rat.ringOfIntegers_pos_iff_all_real_embeddings a).2 hpos,
      (Rat.mem_span_nat_iff_congruence n a).1 ha1, hI⟩
  · rintro ⟨a, ha0, hpos, ha1, hI⟩
    exact ⟨a, ha0, (Rat.mem_span_nat_iff_congruence n a).2 ha1,
      (Rat.ringOfIntegers_pos_iff_all_real_embeddings a).1 hpos, hI⟩
