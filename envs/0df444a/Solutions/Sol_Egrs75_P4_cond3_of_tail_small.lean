-- Prove2me | solution 1 for Egrs75.P4.cond3_of_tail_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:30.309582+00:00
-- url     : https://prove2.me/submissions/0cea5988-b98e-4795-b4d2-d18314b09b1e

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Definitions.Def_LeanPool_Egrs75_ConditionThreeWindow
public import Theorems.Thm_Egrs75_P4_geomQ_mul

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
theorem _root_.solution {p q : ℕ} (hq : 3 ≤ q)
    (hpo : Odd p) (hqo : Odd q) (m i T : ℕ)
    (hlo : (q - 1) / 2 * geomQ q i + 1 ≤ T)
    (hTS : T < (p ^ m + 1) / 2) :
    q ^ i < p ^ m := by
  -- `q` odd ⟹ `q - 1` even ⟹ `2·((q-1)/2) = q - 1`.
  have hqhalf : 2 * ((q - 1) / 2) = q - 1 := by
    obtain ⟨a, ha⟩ := hqo; simp_all
  -- `p^m` odd ⟹ `p^m + 1` even ⟹ `2·((p^m+1)/2) = p^m + 1`.
  have hpodd : Odd (p ^ m) := hpo.pow
  have hph : 2 * ((p ^ m + 1) / 2) = p ^ m + 1 := by
    obtain ⟨a, ha⟩ := hpodd; rw [ha]
    have : 2 * a + 1 + 1 = 2 * (a + 1) := by omega
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  -- golden: `(q-1)·G i = q^i - 1`, and `1 ≤ q^i`.
  have hgolden : (q - 1) * geomQ q i = q ^ i - 1 := geomQ_mul (by omega) i
  have hqipos : 1 ≤ q ^ i := Nat.one_le_pow _ _ (by omega)
  -- `2T < p^m + 1` ⟹ `2T ≤ p^m`.
  have h2T : 2 * T < p ^ m + 1 := by
    calc 2 * T < 2 * ((p ^ m + 1) / 2) := by omega
      _ = p ^ m + 1 := hph
  -- `2·((q-1)/2·G i + 1) ≤ 2T`.
  have h2lo : (q - 1) * geomQ q i + 2 ≤ 2 * T := by
    have : 2 * ((q - 1) / 2 * geomQ q i + 1) ≤ 2 * T := by omega
    calc (q - 1) * geomQ q i + 2
        = 2 * ((q - 1) / 2) * geomQ q i + 2 := by rw [hqhalf]
      _ = 2 * ((q - 1) / 2 * geomQ q i + 1) := by ring
      _ ≤ 2 * T := this
  -- chain: `(q^i - 1) + 2 ≤ 2T ≤ p^m` ⟹ `q^i + 1 ≤ p^m`.
  rw [hgolden] at h2lo
  omega
end Egrs75.P4
