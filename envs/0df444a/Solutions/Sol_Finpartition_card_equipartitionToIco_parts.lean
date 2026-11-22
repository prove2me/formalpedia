-- Prove2me | solution 1 for Finpartition.card_equipartitionToIco_parts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:36:05.933248+00:00
-- url     : https://prove2.me/submissions/32602d41-eedf-46ac-b63f-9ff3c63a8a9d

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc

set_option autoImplicit true
open Finset
open Finpartition
namespace Finpartition
theorem _root_.solution {a b k : ℕ} (hk : k ≠ 0) (hkn : k ≤ b - a) :
    #(equipartitionToIco a b k).parts = k := by
  rw [equipartitionToIco, dif_pos (by simp [hk, hkn]), card_image_of_injective, card_range]
  intro i j h
  by_contra! h'
  have h'' := equipartitionToIco.extracted_2 (a := a) (n := b - a) (k := k) h'
  dsimp at h
  simp only [Function.onFun, h, disjoint_self, bot_eq_empty] at h''
  have : (Ico (a + equiEndpoint (b - a) k j) (a + equiEndpoint (b - a) k (j + 1))).Nonempty :=
    equipartitionToIco_nonempty hk hkn
  simp [h''] at this
end Finpartition
