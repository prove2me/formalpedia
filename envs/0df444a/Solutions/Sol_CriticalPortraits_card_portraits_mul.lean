-- Prove2me | solution 1 for CriticalPortraits.card_portraits_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:41:06.845925+00:00
-- url     : https://prove2.me/submissions/dce6af36-1c8a-48d7-b572-434aa77deebe

module
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
public import Definitions.Def_LeanPool_CriticalPortraits_Denominator
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Census
public import Theorems.Thm_CriticalPortraits_T_injOn
public import Theorems.Thm_CriticalPortraits_T_levelCanonical
public import Theorems.Thm_CriticalPortraits_T_surjOn
public import Theorems.Thm_CriticalPortraits_card_levelCanonical_mul


set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    d * Fintype.card {P : Finset (Finset (ZMod (d*m))) // Portrait d m P}
      = (d*m).choose (d-1) := by
  -- `T` is a bijection from portraits onto level-canonical `(d−1)`-subsets.
  have hbij : Set.BijOn (T (N := d*m)) {P | Portrait d m P}
      {U | U.card = d - 1 ∧ LevelCanonical d m U} :=
    ⟨fun P hP => ⟨T_card hP, T_levelCanonical hd hm hP⟩,
     T_injOn hd hm, T_surjOn hd hm⟩
  -- The induced equivalence of subtypes equates their cardinalities.
  have hcard : Fintype.card {P : Finset (Finset (ZMod (d*m))) // Portrait d m P}
      = Fintype.card {U : Finset (ZMod (d*m)) // U.card = d - 1 ∧ LevelCanonical d m U} :=
    Fintype.card_congr hbij.equiv
  rw [hcard]
  exact card_levelCanonical_mul d m hd hm
end CriticalPortraits
