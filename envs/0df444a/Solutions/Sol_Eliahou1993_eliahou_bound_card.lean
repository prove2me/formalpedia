-- Prove2me | solution 1 for Eliahou1993.eliahou_bound_card
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T14:43:08.43685+00:00
-- url     : https://prove2.me/submissions/a1667165-2360-4d54-a245-373ffae98282

/-
Adapted from https://github.com/tangentproofs/eliahou-collatz-bounds
(commit 18cc351df2f942ddba4bf03feb9b75a70701497d, file Collatz/LinearForm.lean),
formalizing:
  Shalom Eliahou (1993), "The 3x + 1 problem: new lower bounds on nontrivial
  cycle lengths", Discrete Mathematics 118(1-3), pp. 45–56, Theorem 1.1.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

MIT License

Copyright (c) 2026 Michal Wallace

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
import Definitions.Def_eliahou1993Cycle
import Theorems.Thm_Eliahou1993_eliahou_bound_of_min

open Finset

open Eliahou1993 in
theorem solution {L : ℕ} (cyc : CollatzCycle L)
    (hinj : Function.Injective cyc.seq)
    (hmin : (2 : ℕ) ^ 40 < cyc.minElem) :
    17087915 ≤ (Finset.univ.image cyc.seq).card := by
  rw [cyc.card_eq_of_injective hinj]
  exact eliahou_bound_of_min cyc hmin
