-- Prove2me | solution 1 for Formalism.GrowthSums.padicValHarmonicPowerSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:20.885987+00:00
-- url     : https://prove2.me/submissions/33442766-dc56-4204-8278-53233724d6e4

import Definitions.Def_Formalism_GrowthSums_StatementA
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_Harmonic
import Theorems.Thm_Formalism_GrowthSums_le_padicValRat_sum_of_pos
import Theorems.Thm_Formalism_GrowthSums_padicValNat_le_of_lt_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.GrowthSums
namespace Formalism.GrowthSums
theorem _root_.solution : HarmonicVal := by
  intro p t s hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hPpos : (0 : ℚ) < ((p ^ (t + 1) : ℕ) : ℚ) := by
    have : 0 < p ^ (t + 1) := pow_pos hp.pos _
    exact_mod_cast this
  have hP0 : ((p ^ (t + 1) : ℕ) : ℚ) ≠ 0 := hPpos.ne'
  rw [Finset.mul_sum]
  refine le_padicValRat_sum_of_pos (p := p) (s : ℤ)
    (F := fun y => ((p ^ (t + 1) : ℕ) : ℚ) ^ s * (1 / (y : ℚ) ^ s))
    (S := Ico 1 (p ^ (t + 1))) ?_ ?_ ?_
  · refine ⟨1, ?_⟩
    rw [Finset.mem_Ico]
    exact ⟨le_rfl, Nat.one_lt_pow (Nat.succ_ne_zero t) hp.one_lt⟩
  · intro y hy
    rw [Finset.mem_Ico] at hy
    have hy0 : (0 : ℚ) < (y : ℚ) := by exact_mod_cast (show 0 < y by omega)
    exact mul_pos (pow_pos hPpos _) (one_div_pos.2 (pow_pos hy0 _))
  · intro y hy
    rw [Finset.mem_Ico] at hy
    have hy0 : (y : ℚ) ≠ 0 := by exact_mod_cast (show y ≠ 0 by omega)
    have hvy : padicValNat p y ≤ t := padicValNat_le_of_lt_pow hy.1 hy.2
    rw [padicValRat.mul (pow_ne_zero _ hP0) (one_div_ne_zero (pow_ne_zero _ hy0)),
      padicValRat.pow _, one_div, padicValRat.inv, padicValRat.pow _,
      padicValRat.of_nat, padicValRat.of_nat, padicValNat.prime_pow]
    have hm : (s : ℤ) * (padicValNat p y : ℤ) ≤ (s : ℤ) * (t : ℤ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hvy) (by positivity)
    push_cast
    nlinarith
end Formalism.GrowthSums
