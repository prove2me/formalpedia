-- Prove2me | solution 1 for Finpartition.exists_equipartition_Ico
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:45:34.361255+00:00
-- url     : https://prove2.me/submissions/c9d1c4f3-8760-4bb7-9371-42234ee7e0f7

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Theorems.Thm_Finpartition_card_equipartitionToIco_parts
import Theorems.Thm_Finpartition_isEquipartition_equipartitionToIco

set_option autoImplicit true
open Finset
open Finpartition
namespace Finpartition
theorem _root_.solution {a b k : ℕ} (hk : k ≠ 0) (hkn : k ≤ b - a) :
    ∃ P : Finpartition (Finset.Ico a b),
      P.IsEquipartition ∧ #P.parts = k ∧ ∀ i ∈ P.parts, ∃ c d, i = Finset.Ico c d := by
  refine ⟨equipartitionToIco _ _ k, isEquipartition_equipartitionToIco hk hkn,
    card_equipartitionToIco_parts hk hkn, ?_⟩
  intro i hi
  simp [equipartitionToIco, hk, hkn] at hi
  grind
end Finpartition
