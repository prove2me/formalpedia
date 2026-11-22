-- Prove2me | solution 1 for BooleanIsoperimetry.franklFuredi_pairedCompression_exchange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:48:19.101703+00:00
-- url     : https://prove2.me/submissions/c82d7461-dfef-44ec-8244-4a5aad24d357

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Theorems.Thm_BooleanIsoperimetry_pairedCompression_reaches_canonical
public import Theorems.Thm_BooleanIsoperimetry_cascadeSplit_unique


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (A B : Finset (Cube N))
    (p q : ℕ) (hpq : CascadeSplit N (A.card + B.card) p q) :
    PairShadowCost N (simplicialInitSeg N p) (simplicialInitSeg N q) ≤
      PairShadowCost N A B := by
  obtain ⟨A', B', hcan, htot, hcost⟩ := pairedCompression_reaches_canonical A B
  obtain ⟨p', q', hpq', hA'eq, hB'eq⟩ := hcan
  rw [htot] at hpq'
  obtain ⟨hpp, hqq⟩ := cascadeSplit_unique hpq hpq'
  rw [hA'eq, hB'eq, ← hpp, ← hqq] at hcost
  exact hcost
end BooleanIsoperimetry
