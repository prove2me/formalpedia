-- Prove2me | solution 1 for FairSelling.fill_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:11:47.449023+00:00
-- url     : https://prove2.me/submissions/3ece012b-6d33-422b-a295-b415ff7fc09d

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsBagFilling
import Definitions.Def_RequestProject_TwoThirdsProp6
section
open scoped BigOperators
namespace FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G] in
private lemma vbarSum_union_three {w p : G → ℝ} {A C S : Finset G}
    (hAC : Disjoint A C) (hAS : Disjoint A S) (hCS : Disjoint C S) :
    vbarSum w p (A ∪ C ∪ S)
      = (∑ g ∈ A, vbar w p g) + (∑ g ∈ C, vbar w p g) + ∑ g ∈ S, vbar w p g := by
  classical
  have h1 : Disjoint (A ∪ C) S := Finset.disjoint_union_left.mpr ⟨hAS, hCS⟩
  simp only [vbarSum]
  rw [Finset.sum_union h1, Finset.sum_union hAC]
end FairSelling
end

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {ε : ℝ} (hε : 0 ≤ ε)
    (A C S : Finset G) (d r : ℝ) (f₀ : Option G)
    (hS2 : ∀ g ∈ S, vbar w p g = p g)
    (hAC : Disjoint A C) (hAS : Disjoint A S) (hCS : Disjoint C S)
    (hd : 0 ≤ d) (hr : r = 0 ∨ ε ≤ r)
    (hf₀ : ∀ f, f₀ = some f → f ∉ A ∧ f ∉ C ∧ f ∉ S ∧ r ≤ p f ∧ ε ≤ p f)
    (hf₀n : f₀ = none → r = 0)
    (hbud : 2 * ε ≤ (∑ g ∈ A, vbar w p g) + (∑ g ∈ C, vbar w p g) + d + (∑ g ∈ S, p g) + r) :
    Nonempty (FillOut w p ε 1 (A ∪ C ∪ S) d r f₀) := by
  classical
  have hr0 : 0 ≤ r := by rcases hr with h | h <;> linarith
  refine ⟨{ goods := fun j => if j = 0 then A ∪ C ∪ S else ∅
            sell := f₀.toFinset
            src := fun j => if j = 0 then f₀ else none
            dcash := fun j => if j = 0 then d else 0
            scash := fun j => if j = 0 then r else 0
            goods_subset := ?_
            goods_disj := ?_
            goods_zero := ?_
            sell_subset := ?_
            sell_disj := ?_
            src_mem := ?_
            src_zero := ?_
            dcash_nonneg := ?_
            scash_nonneg := ?_
            dcash_zero := ?_
            dcash_sum := ?_
            scash_sum := ?_
            scash_zero := ?_
            price_large := ?_
            acceptable := ?_
            pure_or_singleton := ?_
            singleton_dcash := ?_
            singleton_large := ?_ }⟩
  · intro j; by_cases h : j = 0 <;> simp [h]
  · intro j j' hjj
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have : j' ≠ 0 := fun h => hjj (h.symm)
      simp [this]
    · have : j ≠ 0 := by omega
      simp [this]
  · intro j hj; rw [if_neg (by omega : j ≠ 0)]
  · exact Finset.subset_union_right
  · intro j
    by_cases h : j = 0
    · subst h
      refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
      obtain ⟨hxA, hxC, hxS, _, _⟩ := hf₀ x (Option.mem_toFinset.mp hx)
      rcases Finset.mem_union.mp hx' with hx' | hx'
      · rcases Finset.mem_union.mp hx' with hx' | hx'
        · exact hxA hx'
        · exact hxC hx'
      · exact hxS hx'
    · simp [h]
  · intro j f hf
    by_cases h : j = 0
    · rw [if_pos h] at hf; simpa using hf
    · rw [if_neg h] at hf; exact absurd hf (by simp)
  · intro j hj; rw [if_neg (by omega : j ≠ 0)]
  · intro j; by_cases h : j = 0 <;> simp [h, hd]
  · intro j; by_cases h : j = 0 <;> simp [h, hr0]
  · intro j hj; rw [if_neg (by omega : j ≠ 0)]
  · simp
  · intro f
    have : (Finset.range 1).filter (fun j => (if j = 0 then f₀ else none) = some f)
        ⊆ {0} := by
      intro j hj; simp only [Finset.mem_filter, Finset.mem_range] at hj
      simp; omega
    rcases Option.eq_none_or_eq_some f₀ with h' | ⟨f', h'⟩
    · simp only [h']
      simp
      exact hp f
    · by_cases hff : f' = f
      · subst hff
        rw [show (Finset.range 1).filter (fun j => (if j = 0 then f₀ else none) = some f')
            = {0} by ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
                     constructor
                     · rintro ⟨hj, -⟩; omega
                     · rintro rfl; exact ⟨by omega, by simp [h']⟩]
        simp [h']
      · rw [show (Finset.range 1).filter (fun j => (if j = 0 then f₀ else none) = some f)
            = ∅ by
              ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty,
                iff_false, not_and]
              intro hj
              interval_cases j
              simp [h']
              exact fun hc => hff (by simpa using hc)]
        simp only [Finset.sum_empty]
        split
        · exact hr0
        · exact hp f
  · intro j hj
    by_cases h : j = 0
    · rw [if_pos h] at hj ⊢; simp [hf₀n hj]
    · simp [h]
  · intro f hf; exact (hf₀ f (Option.mem_toFinset.mp hf)).2.2.2.2
  · intro j hj
    have h : j = 0 := by omega
    subst h
    have hSv : ∑ g ∈ S, vbar w p g = ∑ g ∈ S, p g := Finset.sum_congr rfl hS2
    have key : 2 * ε ≤ vbarSum w p (A ∪ C ∪ S) + d + r := by
      rw [vbarSum_union_three hAC hAS hCS, hSv]
      linarith
    simpa using key
  · intro j hj0 hj; omega
  · intro j hj0 hj
    rw [if_neg hj0] at hj; exact absurd rfl hj
  · intro j hj0 hj
    rw [if_neg hj0] at hj; exact absurd rfl hj
end FairSelling
