-- Prove2me | solution 1 for Finset.choose_le_card_mul_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:37:12.285924+00:00
-- url     : https://prove2.me/submissions/f06aa3d4-3144-4047-b1c2-3297f3aebaec

module
public import Definitions.Def_GoodmanSupersaturation_Goodman
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_GoodmanSupersaturation_Supersaturation

set_option autoImplicit true
@[expose] public section
public section
open Finset
namespace Finset
theorem _root_.solution {α : Type*} {s : Finset α}
    {𝓕 : Finset (Finset α)} {t m : ℕ} (h𝓕 : 𝓕 ⊆ s.powersetCard t) (htm : t ≤ m) (hms : m ≤ #s)
    (hcover : ∀ M ∈ s.powersetCard m, ∃ F ∈ 𝓕, F ⊆ M) :
    (#s).choose t ≤ #𝓕 * m.choose t := by
  classical
  -- every `m`-set lies above some member; each member lies below `C(n - t, m - t)` `m`-sets
  have hdc := card_mul_le_card_mul (fun M F => F ⊆ M) (s := s.powersetCard m) (t := 𝓕)
    (m := 1) (n := (#s - t).choose (m - t))
    (fun M hM => by
      obtain ⟨F, hF, hFM⟩ := hcover M hM
      exact card_pos.mpr ⟨F, mem_filter.mpr ⟨hF, hFM⟩⟩)
    (fun F hF => by
      have hFs := mem_powersetCard.mp (h𝓕 hF)
      calc #(bipartiteBelow (fun M F => F ⊆ M) (s.powersetCard m) F)
          ≤ #((s \ F).powersetCard (m - t)) := by
            refine card_le_card_of_injOn (fun M => M \ F) (fun M hM => ?_) ?_
            · rw [mem_coe, mem_bipartiteBelow, mem_powersetCard] at hM
              rw [mem_coe, mem_powersetCard, card_sdiff_of_subset hM.2, hM.1.2, hFs.2]
              exact ⟨sdiff_subset_sdiff hM.1.1 (Subset.refl F), rfl⟩
            · intro M hM M' hM' hMM'
              rw [mem_coe, mem_bipartiteBelow] at hM hM'
              rw [← sdiff_union_of_subset hM.2, ← sdiff_union_of_subset hM'.2]
              exact congrArg (· ∪ F) hMM'
        _ = (#s - t).choose (m - t) := by rw [card_powersetCard, card_sdiff_of_subset hFs.1, hFs.2])
  rw [card_powersetCard, mul_one] at hdc
  have hpos : 0 < (#s - t).choose (m - t) := Nat.choose_pos (by omega)
  have key : (#s).choose t * (#s - t).choose (m - t) ≤
      #𝓕 * m.choose t * (#s - t).choose (m - t) := by
    rw [← Nat.choose_mul htm]
    calc (#s).choose m * m.choose t ≤ #𝓕 * (#s - t).choose (m - t) * m.choose t :=
          Nat.mul_le_mul_right _ hdc
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right key hpos
end Finset
