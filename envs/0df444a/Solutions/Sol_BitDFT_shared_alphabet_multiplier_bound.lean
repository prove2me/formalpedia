-- Prove2me | solution 1 for BitDFT.shared_alphabet_multiplier_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T09:28:12.477368+00:00
-- url     : https://prove2.me/submissions/6dc6cf70-b9fb-461a-a9cd-296fea397867

import Definitions.Def_BitDFT_SharedAlphabetStages
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Mathlib.Tactic

set_option autoImplicit false
open IntMul BitDFT.SharedAlphabetStages BitDFT.AlphabetEmbedding

private theorem tape_count_halts_iff (M : MultitapeTM) (n : ℕ) (h : M.k = n)
    (x y : List Bool) (t : ℕ) (w : List Bool) :
    (BitDFT.TapeCountTransport.machine M n h).HaltsWithOutput x y t w ↔
      M.HaltsWithOutput x y t w := by
  cases h
  rfl

/-- The exact multiplication bound survives embedding the multiplier into the
shared alphabet and padding to the common tape width. -/
theorem solution (A M : MultitapeTM) (q : ℕ) (T : ℝ)
    (hM : MultipliesAt M q T) : MultipliesAt (right A M) q T := by
  intro x y hx hy
  obtain ⟨t, ht, hmul⟩ := hM x y hx hy
  let e := BitDFT.SharedAlphabet.right A M
  let E := BitDFT.AlphabetEmbedding.machine e
  let r := width A M - M.k
  let P := BitDFT.TapeExtension.machine E r
  have hE : E.HaltsWithOutput x y t (bin (2*q) (val x * val y)) :=
    (BitDFT.alphabet_embedding_correct M (BitDFT.SharedAlphabet.carrier A M) e).2
      x y t (bin (2*q) (val x * val y)) hmul
  have hP : P.HaltsWithOutput x y t (bin (2*q) (val x * val y)) :=
    (BitDFT.tape_extension_correct E r).2 x y
      (bin (2*q) (val x * val y)) t |>.mpr hE
  let hw : P.k = width A M := Nat.add_sub_of_le (Nat.le_max_right A.k M.k)
  refine ⟨t, ht, ?_⟩
  exact (tape_count_halts_iff P (width A M) hw x y t
    (bin (2*q) (val x * val y))).mpr hP
