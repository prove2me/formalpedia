-- Prove2me | solution 1 for BooleanIsoperimetry.card_le_choose_of_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:17:08.925988+00:00
-- url     : https://prove2.me/submissions/2786f66e-21f2-46ad-815a-a53f35dce4d2

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.SetFamily.Shadow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Combinatorics.SetFamily.KruskalKatona
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open Finset.Colex
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N r : ℕ} {A : Finset (Cube N)}
    (hA : ∀ x ∈ A, x.card = r) :
    A.card ≤ Nat.choose N r := by
  have hsub : A ⊆ Finset.univ.filter (fun x : Cube N => x.card = r) := by
    intro x hx
    simp [hA x hx]
  refine (Finset.card_mono hsub).trans_eq ?_
  rw [show Finset.univ.filter (fun x : Cube N => x.card = r) =
      Finset.powersetCard r (Finset.univ : Finset (Fin N)) by
    ext x
    simp [Finset.mem_powersetCard]]
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
end BooleanIsoperimetry
