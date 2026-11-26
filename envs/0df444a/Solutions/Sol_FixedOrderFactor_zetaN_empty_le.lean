-- Prove2me | solution 1 for FixedOrderFactor.zetaN_empty_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:09.591036+00:00
-- url     : https://prove2.me/submissions/9ad6af56-3f14-420e-b451-9eb21723d4fa

module
public import Definitions.Def_FixedOrderFactor_Model
public import Definitions.Def_FixedOrderFactor_Order
public import Theorems.Thm_FixedOrderFactor_summable_zetaN_terms


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (s : ℕ) (hs : 2 ≤ s) :
    zetaN ∅ s ≤ 1 + (1 / 2) ^ (s - 2) * zetaN ∅ 2 := by
  have hsum2 := summable_zetaN_terms ∅ (le_refl 2)
  have hsums := summable_zetaN_terms ∅ hs
  have hite : Summable (fun n : ℕ => if n = 1 then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {1}) (fun n hn => by simp at hn; simp [hn])
  have hle : ∀ n : ℕ, (if 0 < n ∧ PrimeTo ∅ n then 1 / (n : ℝ) ^ s else 0) ≤
      (if n = 1 then 1 else 0) +
        (1 / 2) ^ (s - 2) * (if 0 < n ∧ PrimeTo ∅ n then 1 / (n : ℝ) ^ 2 else 0) := by
    intro n
    have hP : PrimeTo ∅ n := fun q hq => absurd hq (Finset.notMem_empty q)
    rcases Nat.lt_trichotomy n 1 with h | h | h
    · have : n = 0 := by omega
      subst this; simp
    · subst h; simp [hP]
    · have hn : (2 : ℝ) ≤ n := by exact_mod_cast h
      simp only [show 0 < n by omega, hP, and_self, if_true, show n ≠ 1 by omega, if_false,
        zero_add]
      have hpos : (0 : ℝ) < n := by linarith
      rw [show s = (s - 2) + 2 by omega, pow_add]
      simp only [show s - 2 + 2 - 2 = s - 2 by omega]
      rw [← one_div_mul_one_div]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [← one_div_pow]
      exact pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le (by norm_num) hn) _
  have := Summable.tsum_le_tsum hle hsums (hite.add (hsum2.mul_left _))
  rw [Summable.tsum_add hite (hsum2.mul_left _), tsum_mul_left, tsum_ite_eq] at this
  exact this
end FixedOrderFactor
