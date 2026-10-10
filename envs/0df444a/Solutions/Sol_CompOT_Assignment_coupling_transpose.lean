-- Prove2me | solution 1 for CompOT.Assignment.coupling_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-09T16:52:03.88+00:00
-- url     : https://prove2.me/submissions/9f9f5971-e2c8-410a-a8f6-1050229733a0

import Mathlib
import Definitions.Def_CompOT_Assignment_Defs

namespace CompOT.Assignment

open Finset
open scoped Pointwise

theorem coupling_transpose {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) :
    P ∈ couplings a b ↔ P.transpose ∈ couplings b a := by
  simp only [couplings, Set.mem_setOf_eq, Matrix.transpose_apply]
  constructor
  · rintro ⟨h0, hr, hc⟩
    exact ⟨fun i j => h0 j i, hc, hr⟩
  · rintro ⟨h0, hr, hc⟩
    exact ⟨fun i j => h0 j i, hc, hr⟩

end CompOT.Assignment

open CompOT.Assignment

theorem solution {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) :
    P ∈ couplings a b ↔ P.transpose ∈ couplings b a :=
  CompOT.Assignment.coupling_transpose a b P
