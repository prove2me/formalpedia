-- Prove2me | solution 1 for Finset.sum_neg_one_pow_mul_sum_strictMono_sum_ite_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/89b59bb1-396e-5434-a506-c95f2d2ffecf

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Finset_sum_neg_one_pow_mul_sum_strictMono_sum_ite_eq_sum

set_option autoImplicit false

universe u v

open Finset

namespace AltChainCount

variable {ι : Type u} [Fintype ι] [LinearOrder ι]

theorem card_filter_strictMono_eq_choose (P : Finset ι) (p : ℕ)
    [DecidablePred (fun s : {s : Fin (p + 1) → ι // StrictMono s} => ∀ j, s.1 j ∈ P)] :
    (univ.filter (fun s : {s : Fin (p + 1) → ι // StrictMono s} => ∀ j, s.1 j ∈ P)).card = P.card.choose (p + 1) := by
  classical
  rw [← Finset.card_powersetCard (p + 1) P]
  refine Finset.card_bij (fun s _ => (univ : Finset (Fin (p + 1))).image s.1) ?_ ?_ ?_
  · intro s hs
    rw [mem_filter] at hs
    rw [mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨j, -, rfl⟩ := mem_image.mp hx
      exact hs.2 j
    · rw [card_image_of_injective _ s.2.injective, card_univ, Fintype.card_fin]
  · intro s hs s' hs' heq
    have heq' : (univ : Finset (Fin (p + 1))).image s.1 = (univ : Finset (Fin (p + 1))).image s'.1 := heq
    apply Subtype.ext
    have h1 : ∀ j, s.1 j ∈ (univ : Finset (Fin (p + 1))).image s.1 := fun j => mem_image_of_mem _ (mem_univ j)
    have h2 : ∀ j, s'.1 j ∈ (univ : Finset (Fin (p + 1))).image s.1 := fun j => by
      rw [heq']; exact mem_image_of_mem _ (mem_univ j)
    have hc : ((univ : Finset (Fin (p + 1))).image s.1).card = p + 1 := by
      rw [card_image_of_injective _ s.2.injective, card_univ, Fintype.card_fin]
    rw [orderEmbOfFin_unique hc h1 s.2, orderEmbOfFin_unique hc h2 s'.2]
  · intro t ht
    rw [mem_powersetCard] at ht
    refine ⟨⟨t.orderEmbOfFin ht.2, (t.orderEmbOfFin ht.2).strictMono⟩, ?_, ?_⟩
    · rw [mem_filter]
      exact ⟨mem_univ _, fun j => ht.1 (orderEmbOfFin_mem t ht.2 j)⟩
    · apply coe_injective
      rw [coe_image, coe_univ, Set.image_univ]
      exact range_orderEmbOfFin t ht.2

theorem sum_neg_one_pow_mul_card_filter_eq_one (P : Finset ι) (hP : P.Nonempty) (N : ℕ)
    (hN : Fintype.card ι ≤ N)
    [∀ p, DecidablePred (fun s : {s : Fin (p + 1) → ι // StrictMono s} => ∀ j, s.1 j ∈ P)] :
    ∑ p ∈ range N, (-1 : ℤ) ^ p *
      ((univ.filter (fun s : {s : Fin (p + 1) → ι // StrictMono s} => ∀ j, s.1 j ∈ P)).card : ℤ) = 1 := by
  have hm : P.card ≠ 0 := by rw [Finset.card_ne_zero]; exact hP
  have hmN : P.card ≤ N := (card_le_univ P).trans hN
  simp_rw [card_filter_strictMono_eq_choose]
  have key : ∑ j ∈ range (P.card + 1), (-1 : ℤ) ^ j * (P.card.choose j : ℤ) = 0 :=
    Int.alternating_sum_range_choose_of_ne hm
  have hvan : ∀ j, P.card < j → (P.card.choose j : ℤ) = 0 := fun j hj => by
    rw [Nat.choose_eq_zero_of_lt hj]; rfl
  have h1 : ∑ p ∈ range N, (-1 : ℤ) ^ p * (P.card.choose (p + 1) : ℤ) =
      ∑ p ∈ range P.card, (-1 : ℤ) ^ p * (P.card.choose (p + 1) : ℤ) := by
    obtain ⟨d, rfl⟩ : ∃ d, N = P.card + d := ⟨N - P.card, by omega⟩
    rw [Finset.sum_range_add]
    conv_rhs => rw [← add_zero (∑ p ∈ range P.card, (-1 : ℤ) ^ p * (P.card.choose (p + 1) : ℤ))]
    congr 1
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [hvan _ (by omega), mul_zero]
  rw [h1]
  rw [Finset.sum_range_succ'] at key
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul] at key
  have : ∑ p ∈ range P.card, (-1 : ℤ) ^ (p + 1) * (P.card.choose (p + 1) : ℤ) =
      -∑ p ∈ range P.card, (-1 : ℤ) ^ p * (P.card.choose (p + 1) : ℤ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [this] at key
  linarith

end AltChainCount

open Classical in

theorem solution
    {ι : Type u} [Fintype ι] [LinearOrder ι] {β : Type v} (T : Finset β) (a : β → ℤ)
    (mem : ι → β → Prop) (hcov : ∀ y ∈ T, ∃ i, mem i y) (N : ℕ) (hN : Fintype.card ι ≤ N) :
    ∑ p ∈ Finset.range N, (-1 : ℤ) ^ p *
        ∑ s : {s : Fin (p + 1) → ι // StrictMono s}, ∑ y ∈ T, (if ∀ j, mem (s.1 j) y then a y else 0) =
      ∑ y ∈ T, a y := by
  classical

  have hx : ∀ p : ℕ, ∑ s : {s : Fin (p + 1) → ι // StrictMono s}, ∑ y ∈ T, (if ∀ j, mem (s.1 j) y then a y else 0) =
      ∑ y ∈ T, a y * ((univ.filter (fun s : {s : Fin (p + 1) → ι // StrictMono s} =>
        ∀ j, s.1 j ∈ univ.filter (fun i => mem i y))).card : ℤ) := by
    intro p
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [mem_filter, mem_univ, true_and]
    split_ifs <;> simp
  simp_rw [hx, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  have hP : (univ.filter (fun i => mem i y)).Nonempty := by
    obtain ⟨i, hi⟩ := hcov y hy
    exact ⟨i, by simp [hi]⟩
  have := AltChainCount.sum_neg_one_pow_mul_card_filter_eq_one (univ.filter (fun i => mem i y)) hP N hN
  calc ∑ p ∈ range N, (-1 : ℤ) ^ p * (a y * ((univ.filter (fun s : {s : Fin (p + 1) → ι // StrictMono s} =>
          ∀ j, s.1 j ∈ univ.filter (fun i => mem i y))).card : ℤ))
      = a y * ∑ p ∈ range N, (-1 : ℤ) ^ p * ((univ.filter (fun s : {s : Fin (p + 1) → ι // StrictMono s} =>
          ∀ j, s.1 j ∈ univ.filter (fun i => mem i y))).card : ℤ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)
    _ = a y := by rw [this, mul_one]

end S_Finset_sum_neg_one_pow_mul_sum_strictMono_sum_ite_eq_sum
end P2MW
export P2MW.S_Finset_sum_neg_one_pow_mul_sum_strictMono_sum_ite_eq_sum (solution)
