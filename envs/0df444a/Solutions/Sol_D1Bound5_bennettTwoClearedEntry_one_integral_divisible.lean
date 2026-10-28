-- Prove2me | solution 1 for D1Bound5.bennettTwoClearedEntry_one_integral_divisible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:56:53.844+00:00
-- url     : https://prove2.me/submissions/fa6ad928-8de1-4443-8e4f-21cb49e780a0

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
import Theorems.Thm_D1Bound5_bennettTwoNodes_one
import Theorems.Thm_D1Bound5_bennettTwoOtherPoles_one
import Theorems.Thm_D1Bound5_bennett_delta_sum_three
import Theorems.Thm_D1Bound5_bennett_sum_divisible_in_subring
import Theorems.Thm_D1Bound5_bennett_two_integral_summand_one

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]





















/-- The entire column-one entry is divisible by a^k in the original subring. -/
theorem _root_.solution (S : Subring F)
    (a b c : F) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hb0 : b ≠ 0) (hab : a ≠ b) (k : ℕ) (hk : 1 ≤ k) (i : Fin 3) :
    ∃ q ∈ S, bennettTwoClearedEntry a b c k i 1 = a ^ k * q := by
  unfold bennettTwoClearedEntry bennettClearedResidue
  rw [bennettTwoOtherPoles_one, bennettTwoNodes_one,
    bennettClearedTaylor_two_poles_scaled_eval]
  apply bennett_sum_divisible_in_subring
  intro ht hht
  apply bennett_sum_divisible_in_subring
  intro uv huv
  have hts := Finset.mem_antidiagonal.mp hht
  have hus := Finset.mem_antidiagonal.mp huv
  have hd := bennett_delta_sum_three i
  have hh : uv.1 + ht.1 + uv.2 + 1 = k + (if i = 1 then 1 else 0) := by omega
  obtain ⟨q, hq, heq⟩ := bennett_two_integral_summand_one S a b c ha hb hc hb0 hab
    k (if i = 0 then 1 else 0) (if i = 1 then 1 else 0) (if i = 2 then 1 else 0)
      uv.1 ht.1 uv.2 hk hd hh
  refine ⟨q, hq, ?_⟩
  convert heq using 1 <;> simp only [mul_pow] <;> ring







end D1Bound5
end
