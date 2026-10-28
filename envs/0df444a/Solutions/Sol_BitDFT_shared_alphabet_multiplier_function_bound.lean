-- Prove2me | solution 1 for BitDFT.shared_alphabet_multiplier_function_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T05:49:38.842058+00:00
-- url     : https://prove2.me/submissions/e071fd4b-352e-4512-a672-0a2c67ff4cf0

import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_BitDFT_Encoding
import Definitions.Def_BitDFT_SharedAlphabetStages
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_count_transport_correct
import Mathlib.Tactic

set_option autoImplicit false
open IntMul BitDFT.SharedAlphabetStages BitDFT.AlphabetEmbedding

private theorem tape_count_halts_iff (M : MultitapeTM) (n : ℕ) (h : M.k = n)
    (x y : List Bool) (t : ℕ) (w : List Bool) :
    (BitDFT.TapeCountTransport.machine M n h).HaltsWithOutput x y t w ↔
      M.HaltsWithOutput x y t w := by
  cases h
  rfl

theorem solution (A M : MultitapeTM) (T : ℕ → ℝ)
    (hM : BitDFT.Multiplier M T) : BitDFT.Multiplier (right A M) T := by
  intro q hq
  intro x y hx hy
  obtain ⟨t, ht, hmul⟩ := hM q hq x y hx hy
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

