-- Prove2me | solution 1 for Eliahou1993.eliahou_product_formula
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T14:39:04.881185+00:00
-- url     : https://prove2.me/submissions/db819ded-457c-4991-bfc0-a56bd49764b3

/-
Adapted from https://github.com/tangentproofs/eliahou-collatz-bounds
(commit 18cc351df2f942ddba4bf03feb9b75a70701497d, file Collatz/ProductFormula.lean),
formalizing:
  Shalom Eliahou (1993), "The 3x + 1 problem: new lower bounds on nontrivial
  cycle lengths", Discrete Mathematics 118(1-3), pp. 45–56, Lemma 2.2.
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
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

open Finset BigOperators

set_option maxHeartbeats 800000

namespace Eliahou1993

/-- For any n, the "multiplied" Collatz value:
    if n is odd then 3n+1, if n is even then n -/
def collatzMul (n : ℕ) : ℕ :=
  if n % 2 = 1 then 3 * n + 1 else n

/-- collatzMul relates to collatzComp by: collatzMul n = 2 * collatzComp n -/
theorem collatzMul_eq_two_mul_collatzComp {n : ℕ} :
    collatzMul n = 2 * collatzComp n := by
  unfold collatzMul
  rw [two_mul_collatzComp]

/-
collatzMul preserves positivity
-/
theorem collatzMul_pos {n : ℕ} (hn : 0 < n) : 0 < collatzMul n := by
  unfold collatzMul;
  grind

/-
Reindexing: the successor-mod map is a bijection on Fin L
-/
theorem succMod_bijective (L : ℕ) (hL : 0 < L) :
    Function.Bijective (fun i : Fin L => i.succMod hL) := by
  constructor;
  · intro i j; simp +decide [ Fin.succMod ] ;
    exact fun h => Fin.ext <| Nat.mod_eq_of_lt i.2 ▸ Nat.mod_eq_of_lt j.2 ▸ by simpa [ ← ZMod.natCast_eq_natCast_iff' ] using h;
  · intro i;
    use ⟨ ( i + L - 1 ) % L, Nat.mod_lt _ hL ⟩ ; simp +decide [ Fin.ext_iff, Fin.succMod ];
    rw [ Nat.sub_add_cancel ( by linarith [ Fin.is_lt i ] ) ] ; simp +decide [ Nat.mod_eq_of_lt ]

/-
Key step: ∏ T(seq i) = ∏ seq i, by reindexing
-/
theorem prod_collatzComp_eq_prod {L : ℕ} (c : CollatzCycle L) :
    ∏ i : Fin L, collatzComp (c.seq i) = ∏ i : Fin L, c.seq i := by
  obtain ⟨hL, seq, hpos, hstep⟩ := c;
  convert Equiv.prod_comp ( Equiv.ofBijective _ <| succMod_bijective _ _ ) _;
  exacts [ hstep _, hL ]

/-
Key step: ∏ collatzMul(seq i) = 2^L * ∏ seq i
-/
theorem prod_collatzMul_eq {L : ℕ} (c : CollatzCycle L) :
    ∏ i : Fin L, collatzMul (c.seq i) = 2 ^ L * ∏ i : Fin L, c.seq i := by
  rw [ Finset.prod_congr rfl fun i hi => collatzMul_eq_two_mul_collatzComp, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin, prod_collatzComp_eq_prod ]

/-- For even n, collatzMul n = n -/
@[simp]
theorem collatzMul_even {n : ℕ} (hn : n % 2 = 0) : collatzMul n = n := by
  simp [collatzMul, hn]

/-- For odd n, collatzMul n = 3n + 1 -/
@[simp]
theorem collatzMul_odd {n : ℕ} (hn : n % 2 = 1) : collatzMul n = 3 * n + 1 := by
  simp [collatzMul, hn]

/-
The complement of odd indices is even indices
-/
theorem CollatzCycle.oddIndices_compl {L : ℕ} (c : CollatzCycle L) :
    c.oddIndicesᶜ = c.evenIndices := by
  ext i
  simp [CollatzCycle.oddIndices, CollatzCycle.evenIndices]

/-
Product over univ splits into product over odd and even indices
-/
theorem CollatzCycle.prod_split_odd_even {L : ℕ} (c : CollatzCycle L)
    (f : Fin L → ℕ) :
    ∏ i : Fin L, f i =
    (∏ i ∈ c.oddIndices, f i) * (∏ i ∈ c.evenIndices, f i) := by
  rw [ ← Finset.prod_union ];
  · rw [ show c.oddIndices ∪ c.evenIndices = Finset.univ from ?_ ];
    ext i
    simp [CollatzCycle.oddIndices, CollatzCycle.evenIndices];
    exact Nat.mod_two_eq_zero_or_one _ |> Or.symm;
  · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;

end Eliahou1993

open Eliahou1993 in
theorem solution {L : ℕ} (c : CollatzCycle L) :
    ∏ i ∈ c.oddIndices, (3 * c.seq i + 1) =
    2 ^ L * ∏ i ∈ c.oddIndices, c.seq i := by
  have h_even_eq : (∏ i : Fin L, collatzMul (c.seq i)) = (∏ i ∈ c.oddIndices, (3 * c.seq i + 1)) * (∏ i ∈ c.evenIndices, c.seq i) := by
    convert CollatzCycle.prod_split_odd_even c ( fun i => collatzMul ( c.seq i ) ) using 1;
    congr! 2;
    · unfold CollatzCycle.oddIndices at *; aesop;
    · unfold CollatzCycle.evenIndices at *; aesop
  have h_even_eq' : (∏ i : Fin L, c.seq i) = (∏ i ∈ c.oddIndices, c.seq i) * (∏ i ∈ c.evenIndices, c.seq i) := by
    convert CollatzCycle.prod_split_odd_even c _;
  exact mul_right_cancel₀ ( show ∏ i ∈ c.evenIndices, c.seq i ≠ 0 from Finset.prod_ne_zero_iff.mpr fun i hi => Nat.ne_of_gt <| c.pos i ) <| by nlinarith [ pow_pos ( zero_lt_two' ℤ ) L, prod_collatzMul_eq c ] ;
