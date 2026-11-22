-- Prove2me | solution 1 for BooleanIsoperimetry.H_exchange_max_form_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:48:52.93313+00:00
-- url     : https://prove2.me/submissions/782d2189-cc08-4f96-a19e-6b6b3ceeb477

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Theorems.Thm_BooleanIsoperimetry_PairShadowCost_initSeg_eq_max_H
public import Theorems.Thm_BooleanIsoperimetry_card_simplicialInitSeg
public import Theorems.Thm_BooleanIsoperimetry_cascade_p_le
public import Theorems.Thm_BooleanIsoperimetry_cascade_q_le
public import Theorems.Thm_BooleanIsoperimetry_franklFuredi_pairedCompression_exchange


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N p q a b : ℕ}
    (hpq : CascadeSplit N (a + b) p q) (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N)
    (_hq_pos : 1 ≤ q) :
    max (H N p) q + max (H N q) p ≤ max (H N a) b + max (H N b) a := by
  have ha_card : (simplicialInitSeg N a).card = a := by rw [card_simplicialInitSeg, min_eq_left ha]
  have hb_card : (simplicialInitSeg N b).card = b := by rw [card_simplicialInitSeg, min_eq_left hb]
  have hpq_structural :
      CascadeSplit N ((simplicialInitSeg N a).card + (simplicialInitSeg N b).card) p q := by
    rwa [ha_card, hb_card]
  have h_FF := franklFuredi_pairedCompression_exchange (simplicialInitSeg N a)
    (simplicialInitSeg N b) p q hpq_structural
  have hp : p ≤ 2 ^ N := cascade_p_le hpq
  have hq : q ≤ 2 ^ N := cascade_q_le hpq
  rw [PairShadowCost_initSeg_eq_max_H hp hq,
      PairShadowCost_initSeg_eq_max_H ha hb] at h_FF
  exact h_FF
end BooleanIsoperimetry
