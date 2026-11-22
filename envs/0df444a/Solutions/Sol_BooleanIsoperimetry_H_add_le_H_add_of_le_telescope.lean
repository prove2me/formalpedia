-- Prove2me | solution 1 for BooleanIsoperimetry.H_add_le_H_add_of_le_telescope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:51.655392+00:00
-- url     : https://prove2.me/submissions/72eb3671-de7d-4a75-a6c5-a4c36f69edc1

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n a b c d : ℕ) (hab : a + b = c + d) (hac : a ≤ c)
    (hinc : ∀ i < c - a, H (n + 1) (a + i + 1) + H (n + 1) (b - i - 1) ≤
      H (n + 1) (a + i) + H (n + 1) (b - i)) :
    H (n + 1) c + H (n + 1) d ≤ H (n + 1) a + H (n + 1) b := by
  generalize hd : c - a = delta
  have hc : c = a + delta := by omega
  have hd2 : d = b - delta := by omega
  subst hc hd2
  clear hab hac hd
  induction delta with
  | zero =>
    simp
  | succ delta ih =>
    have h1 : H (n + 1) (a + (delta + 1)) + H (n + 1) (b - (delta + 1)) ≤
        H (n + 1) (a + delta) + H (n + 1) (b - delta) := by
      have hinc_d := hinc delta (by omega)
      have hrw1 : a + (delta + 1) = a + delta + 1 := by omega
      have hrw2 : b - (delta + 1) = b - delta - 1 := by omega
      rw [hrw1, hrw2]
      exact hinc_d
    have h2 : H (n + 1) (a + delta) + H (n + 1) (b - delta) ≤ H (n + 1) a + H (n + 1) b :=
      ih (fun i hi => hinc i (by omega))
    omega
end BooleanIsoperimetry
