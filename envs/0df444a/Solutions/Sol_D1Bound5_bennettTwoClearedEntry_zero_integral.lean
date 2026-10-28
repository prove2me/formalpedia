-- Prove2me | solution 1 for D1Bound5.bennettTwoClearedEntry_zero_integral
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:24:06.325163+00:00
-- url     : https://prove2.me/submissions/a4ce0895-a633-4d34-9a4a-505e279c27f9

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
import Theorems.Thm_D1Bound5_bennettTwoNodes_zero
import Theorems.Thm_D1Bound5_bennettTwoOtherPoles_zero
import Theorems.Thm_D1Bound5_bennett_delta_sum_three
import Theorems.Thm_D1Bound5_bennett_sum_divisible_in_subring
import Theorems.Thm_D1Bound5_bennett_two_integral_summand_zero

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



















/-- Integrality of the entire column-zero entry, proved from its actual
finite residue expansion. -/
theorem _root_.solution (S : Subring F)
    (a b c : F) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (k : ℕ) (hk : 1 ≤ k) (i : Fin 3) :
    ∃ q ∈ S, bennettTwoClearedEntry a b c k i 0 = 1 * q := by
  unfold bennettTwoClearedEntry bennettClearedResidue
  rw [bennettTwoOtherPoles_zero, bennettTwoNodes_zero,
    bennettClearedTaylor_two_poles_scaled_eval]
  apply bennett_sum_divisible_in_subring
  intro ht hht
  apply bennett_sum_divisible_in_subring
  intro uv huv
  have hts := Finset.mem_antidiagonal.mp hht
  have hus := Finset.mem_antidiagonal.mp huv
  have hd := bennett_delta_sum_three i
  have hh : ht.1 + uv.1 + uv.2 + 1 = k + (if i = 0 then 1 else 0) := by omega
  obtain ⟨q, hq, heq⟩ := bennett_two_integral_summand_zero S a b c ha hb hc ha0 hb0
    k (if i = 0 then 1 else 0) (if i = 1 then 1 else 0) (if i = 2 then 1 else 0)
      ht.1 uv.1 uv.2 hk hd hh
  refine ⟨q, hq, ?_⟩
  convert heq using 1 <;> simp only [add_zero, mul_pow] <;> ring









end D1Bound5
end
