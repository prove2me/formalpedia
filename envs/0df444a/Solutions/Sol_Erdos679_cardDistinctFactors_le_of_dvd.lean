-- Prove2me | solution 1 for Erdos679.cardDistinctFactors_le_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:30:24.925048+00:00
-- url     : https://prove2.me/submissions/cfeb44b1-7291-43a3-99fa-c19efc86d094

module
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos679_CRT

set_option autoImplicit false
@[expose] public section
public section
open Erdos679
namespace Erdos679
theorem _root_.solution {a b : ℕ} (hab : a ∣ b) (hb : b ≠ 0) :
    ArithmeticFunction.cardDistinctFactors a ≤ ArithmeticFunction.cardDistinctFactors b := by
  simpa only [← Nat.toFinset_factors, List.card_toFinset,
    ArithmeticFunction.cardDistinctFactors_apply] using
      Finset.card_le_card (Nat.primeFactors_mono hab hb)
end Erdos679
