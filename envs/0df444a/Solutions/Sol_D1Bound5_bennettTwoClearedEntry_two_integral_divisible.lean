-- Prove2me | solution 1 for D1Bound5.bennettTwoClearedEntry_two_integral_divisible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:22:14.521958+00:00
-- url     : https://prove2.me/submissions/887d28dc-4e9e-41ed-b50e-e282953804e1

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Theorems.Thm_D1Bound5_bennettClearedTaylor_two_poles_scaled_eval
import Theorems.Thm_D1Bound5_bennettTwoNodes_two
import Theorems.Thm_D1Bound5_bennettTwoOtherPoles_two
import Theorems.Thm_D1Bound5_bennett_delta_sum_three
import Theorems.Thm_D1Bound5_bennett_sum_divisible_in_subring
import Theorems.Thm_D1Bound5_bennett_two_integral_summand_two

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]























/-- The entire column-two entry is divisible by b^k in the original subring. -/
theorem _root_.solution (S : Subring F)
    (a b c : F) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (ha0 : a ≠ 0) (hab : a ≠ b) (k : ℕ) (hk : 1 ≤ k) (i : Fin 3) :
    ∃ q ∈ S, bennettTwoClearedEntry a b c k i 2 = b ^ k * q := by
  unfold bennettTwoClearedEntry bennettClearedResidue
  rw [bennettTwoOtherPoles_two, bennettTwoNodes_two,
    bennettClearedTaylor_two_poles_scaled_eval]
  apply bennett_sum_divisible_in_subring
  intro ht hht
  apply bennett_sum_divisible_in_subring
  intro uv huv
  have hts := Finset.mem_antidiagonal.mp hht
  have hus := Finset.mem_antidiagonal.mp huv
  have hd := bennett_delta_sum_three i
  have hh : uv.1 + uv.2 + ht.1 + 1 = k + (if i = 2 then 1 else 0) := by omega
  obtain ⟨q, hq, heq⟩ := bennett_two_integral_summand_two S a b c ha hb hc ha0 hab
    k (if i = 0 then 1 else 0) (if i = 1 then 1 else 0) (if i = 2 then 1 else 0)
      uv.1 uv.2 ht.1 hk hd hh
  refine ⟨q, hq, ?_⟩
  convert heq using 1 <;> simp only [mul_pow] <;> ring





end D1Bound5
end
