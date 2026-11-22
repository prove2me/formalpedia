-- Prove2me | solution 1 for Egrs75.P4.tail_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:41:32.856562+00:00
-- url     : https://prove2.me/submissions/9c060470-2f7d-410d-85cf-2134a3adebd6

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Definitions.Def_LeanPool_Egrs75_ConditionThreeWindow
public import Theorems.Thm_Egrs75_P4_geomQ_mul
public import Theorems.Thm_Egrs75_P4_geomQ_succ
public import Theorems.Thm_Egrs75_P4_topBad_lt_leastGoodAbove
public import Theorems.Thm_Egrs75_P4_tailLB_le_mod
public import Theorems.Thm_Egrs75_RepairDV_digit_top_big


set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.P4
open Nat
open Finset
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
namespace Egrs75.P4
theorem _root_.solution {q n : ℕ} (hq : 3 ≤ q) (hbad : 0 < badCountQ q n) :
    (q - 1) / 2 * geomQ q (leastGoodAbove hq hbad) + 1 ≤ n % q ^ (leastGoodAbove hq hbad) := by
  -- Abbreviations as plain `let`-free locals (avoid `set` aliasing of `q^j`).
  obtain ⟨j, hjdef⟩ : ∃ j, j = topBadIndex q n := ⟨_, rfl⟩
  obtain ⟨i, hidef⟩ : ∃ i, i = leastGoodAbove hq hbad := ⟨_, rfl⟩
  rw [← hidef]
  have hji : j < i := by rw [hjdef, hidef]; exact topBad_lt_leastGoodAbove hq hbad
  -- top digit b_j ≥ B+1 (oversized)
  have hbj : (q - 1) / 2 < n / q ^ j % q := by rw [hjdef]; exact digit_top_big (by omega) hbad
  -- tailLB i ≤ n % q^i
  have hlb : tailLB q n j i ≤ n % q ^ i := by
    rw [hjdef]; exact tailLB_le_mod hq hbad (t := i) (by rw [← hjdef]; omega) (by rw [hidef])
  -- value of tailLB: with SumMid = ∑_{j+1 ≤ s < i} q^s,
  --   tailLB q n j i = (n/q^j%q)·q^j + B·SumMid.
  set SumMid := ∑ s ∈ Finset.Ico (j + 1) i, q ^ s with hSM
  have htailval : tailLB q n j i = (n / q ^ j % q) * q ^ j + ((q - 1) / 2) * SumMid := by
    simp only [tailLB, ← hSM]
  -- geom split: geomQ q i = geomQ q j + q^j + SumMid.
  have hGsplit : geomQ q i = geomQ q j + q ^ j + SumMid := by
    have h1 : geomQ q i = geomQ q (j + 1) + SumMid := by
      unfold geomQ; rw [hSM, ← Finset.sum_range_add_sum_Ico _ (by omega : j + 1 ≤ i)]
    rw [h1, geomQ_succ q j]
  -- abbreviate the load-bearing products and bound them.
  set B := (q - 1) / 2 with hB
  set Gj := geomQ q j with hGjdef
  set P := q ^ j with hP
  set bj := n / q ^ j % q with hbjdef
  -- 2·(B·Gj) ≤ P - 1 (golden + 2B ≤ q-1), and P ≥ 1, so B·Gj + 1 ≤ P.
  have h2B : 2 * B ≤ q - 1 := by rw [hB]; omega
  have hgolden : (q - 1) * Gj = P - 1 := by rw [hGjdef, hP]; exact geomQ_mul (by omega) j
  have hPpos : 1 ≤ P := by rw [hP]; exact Nat.one_le_pow _ _ (by omega)
  have h2BGj : 2 * (B * Gj) ≤ P - 1 := by
    calc 2 * (B * Gj) = (2 * B) * Gj := by ring
      _ ≤ (q - 1) * Gj := Nat.mul_le_mul_right _ h2B
      _ = P - 1 := hgolden
  have hBGj : B * Gj + 1 ≤ P := by omega
  -- b_j ≥ B+1 ⟹ b_j·P ≥ (B+1)·P = B·P + P.
  have hbjge : B + 1 ≤ bj := by omega
  have hbjP : B * P + P ≤ bj * P := by
    calc B * P + P = (B + 1) * P := by ring
      _ ≤ bj * P := Nat.mul_le_mul_right _ hbjge
  -- assemble: goal  B·(geomQ q i) + 1 ≤ n % q^i.
  rw [hGsplit]
  -- B·(Gj + P + SumMid) + 1 ≤ n % q^i.  Use htailval, hlb, and the products.
  have hgoalexp : B * (Gj + P + SumMid) + 1 = (B * Gj + 1) + (B * P) + (B * SumMid) := by ring
  rw [hgoalexp]
  -- tailLB = bj·P + B·SumMid ≤ n%q^i.  And (B·Gj+1)+B·P ≤ P + B·P ≤ bj·P.
  have htv : tailLB q n j i = bj * P + B * SumMid := by rw [htailval]
  rw [htv] at hlb
  omega
end Egrs75.P4
