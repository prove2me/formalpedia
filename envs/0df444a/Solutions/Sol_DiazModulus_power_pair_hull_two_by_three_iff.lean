-- Prove2me | solution 1 for DiazModulus.power_pair_hull_two_by_three_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-08T16:36:17.898501+00:00
-- url     : https://prove2.me/submissions/984c95fb-736d-413d-9e11-284553b273e5

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_laurent_hull_config_iff
import Theorems.Thm_DiazModulus_two_sumset_iff_difference_count
import Theorems.Thm_DiazModulus_power_pair_difference_count_iff

open Complex ComplexConjugate

/-! # `2 × 3` configurations in `Σ_{s ∈ {0, ±1, ±k, ±l}} K uˢ`

Let `u` be transcendental over `K` and `4 ≤ k < l`. By `laurent_hull_config_iff`, a `2 × 3`
configuration in the hull of `S = {0, ±1, ±k, ±l}` exists exactly when `S` contains a sumset
`A + B` with `|A| = 2`, `|B| = 3`. By `two_sumset_iff_difference_count`, this happens exactly when
some difference `d > 0` occurs at least three times in `S` (three `s ∈ S` with `s + d ∈ S`), and
`power_pair_difference_count_iff` lists the `l` for which this happens:
`l ∈ {k + 1, k + 2, 2k − 1, 2k, 2k + 1, 3k}`. The proof is the composition of the three nodes,
after reading the set literal as a finite set.
-/

namespace R6_pairs

open DiazModulus

theorem coe_S (k l : ℤ) :
    (({0, 1, -1, k, -k, l, -l} : Finset ℤ) : Set ℤ) = ({0, 1, -1, k, -k, l, -l} : Set ℤ) := by
  push_cast
  rfl

end R6_pairs

open DiazModulus R6_pairs in
theorem solution (K : Subfield ℂ) (u : ℂ) (hT : Transcendental K u)
    (k l : ℤ) (hk : 4 ≤ k) (hkl : k < l) :
    (∃ (x : Fin 2 → ℂ) (y : Fin 3 → ℂ), LinearIndependent K x ∧ LinearIndependent K y ∧
      ∀ i j, x i * y j ∈ Submodule.span K
        ((fun s : ℤ => u ^ s) '' ({0, 1, -1, k, -k, l, -l} : Set ℤ))) ↔
    (l = k + 1 ∨ l = k + 2 ∨ l = 2 * k - 1 ∨ l = 2 * k ∨ l = 2 * k + 1 ∨ l = 3 * k) := by
  rw [← coe_S, DiazModulus.laurent_hull_config_iff K u hT _ 2 3 (by norm_num) (by norm_num),
    DiazModulus.two_sumset_iff_difference_count]
  exact DiazModulus.power_pair_difference_count_iff k l hk hkl
