-- Prove2me | solution 1 for FairSelling.TPS_lt_of_no_fixed_above
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:05.286266+00:00
-- url     : https://prove2.me/submissions/3851e7ed-d76d-4417-9abe-693cc9e7cdbc

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
import Theorems.Thm_FairSelling_truncSum_bracket
import Theorems.Thm_FairSelling_truncSum_of_ge
import Theorems.Thm_FairSelling_TPS_truncSum


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {b : ℝ}
    (hb : truncSum n v p b < b)
    (hbv : ∀ g, b ≤ v g → truncSum n v p (v g) < v g)
    (hbp : ∀ g, b ≤ p g → truncSum n v p (p g) < p g) :
    TPS n v p < b := by
  classical
  by_contra hcon
  push_neg at hcon   -- `b ≤ TPS`
  set t₀ := TPS n v p with ht₀def
  have hfix : truncSum n v p t₀ = t₀ := TPS_truncSum v p hp
  -- `t₀` is not a breakpoint
  have hnotv : ∀ g, v g ≠ t₀ := by
    intro g hg
    have := hbv g (by rw [hg]; exact hcon)
    rw [hg, hfix] at this; exact lt_irrefl _ this
  have hnotp : ∀ g, p g ≠ t₀ := by
    intro g hg
    have := hbp g (by rw [hg]; exact hcon)
    rw [hg, hfix] at this; exact lt_irrefl _ this
  have hbt : b < t₀ := lt_of_le_of_ne hcon (by rintro rfl; exact absurd hfix (ne_of_lt hb))
  -- the left endpoint `a`
  set L : Finset ℝ :=
    (insert b (((Finset.univ.image v) ∪ (Finset.univ.image p)).filter
      (fun s => b ≤ s))).filter (fun s => s < t₀) with hLdef
  have hbL : b ∈ L := by
    simp only [hLdef, Finset.mem_filter]
    exact ⟨Finset.mem_insert_self _ _, hbt⟩
  obtain ⟨a, haL, hamax⟩ := Finset.exists_max_image L (fun x => x) ⟨b, hbL⟩
  have hat₀ : a < t₀ := by
    simp only [hLdef, Finset.mem_filter] at haL; exact haL.2
  have hba : b ≤ a := hamax b hbL
  have hga : truncSum n v p a < a := by
    simp only [hLdef, Finset.mem_filter, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image] at haL
    rcases haL.1 with h | h
    · rw [h]; exact hb
    · rcases h.1 with ⟨g, _, hg⟩ | ⟨g, _, hg⟩
      · rw [← hg]; exact hbv g (by rw [hg]; exact h.2)
      · rw [← hg]; exact hbp g (by rw [hg]; exact h.2)
  -- the right endpoint `c`
  set U : Finset ℝ :=
    (((Finset.univ.image v) ∪ (Finset.univ.image p)).filter (fun s => t₀ < s)) with hUdef
  -- in either case we produce `c > t₀` with `NoBreak v p a c`
  have main : ∀ c : ℝ, t₀ < c → NoBreak v p a c → c < truncSum n v p c := by
    intro c hc hnb
    have h1 := truncSum_bracket (n := n) v p hnb (le_of_lt hat₀) (le_of_lt hc)
    have h2 := truncSum_bracket (n := n) v p hnb (le_refl a) (le_of_lt (lt_trans hat₀ hc))
    have h3 := truncSum_bracket (n := n) v p hnb (le_of_lt (lt_trans hat₀ hc)) (le_refl c)
    set C := flatConst v p a c
    set k := ((slopeGoods v p a c).card : ℝ)
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    -- from `f(t₀) = t₀`
    have e1 : C + k * t₀ = n * t₀ := by
      rw [hfix] at h1
      rw [eq_comm, div_eq_iff (ne_of_gt hn')] at h1
      linarith [h1]
    -- from `f(a) < a`
    have e2 : C + k * a < n * a := by
      rw [h2, div_lt_iff₀ hn'] at hga
      linarith [hga]
    have hkn : (n : ℝ) - k < 0 := by
      nlinarith [hat₀, e1, e2]
    rw [h3, lt_div_iff₀ hn']
    nlinarith [hc, hkn, e1]
  by_cases hU : U.Nonempty
  · obtain ⟨c, hcU, hcmin⟩ := U.exists_min_image id hU
    have hct : t₀ < c := by
      simp only [hUdef, Finset.mem_filter] at hcU; exact hcU.2
    have hnb : NoBreak v p a c := by
      intro g
      constructor
      · rcases lt_trichotomy (v g) t₀ with h | h | h
        · left
          by_contra hcontra
          push_neg at hcontra
          have : v g ∈ L := by
            simp only [hLdef, Finset.mem_filter, Finset.mem_insert, Finset.mem_union,
              Finset.mem_image]
            exact ⟨Or.inr ⟨Or.inl ⟨g, Finset.mem_univ g, rfl⟩, le_trans hba (le_of_lt hcontra)⟩, h⟩
          exact absurd (hamax _ this) (not_le.mpr hcontra)
        · exact absurd h (hnotv g)
        · right
          refine hcmin (v g) ?_
          simp only [hUdef, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
          exact ⟨Or.inl ⟨g, Finset.mem_univ g, rfl⟩, h⟩
      · rcases lt_trichotomy (p g) t₀ with h | h | h
        · left
          by_contra hcontra
          push_neg at hcontra
          have : p g ∈ L := by
            simp only [hLdef, Finset.mem_filter, Finset.mem_insert, Finset.mem_union,
              Finset.mem_image]
            exact ⟨Or.inr ⟨Or.inr ⟨g, Finset.mem_univ g, rfl⟩, le_trans hba (le_of_lt hcontra)⟩, h⟩
          exact absurd (hamax _ this) (not_le.mpr hcontra)
        · exact absurd h (hnotp g)
        · right
          refine hcmin (p g) ?_
          simp only [hUdef, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
          exact ⟨Or.inr ⟨g, Finset.mem_univ g, rfl⟩, h⟩
    have hcgt := main c hct hnb
    -- but `c` is a breakpoint `≥ b`, so `f(c) < c`
    have : truncSum n v p c < c := by
      simp only [hUdef, Finset.mem_filter, Finset.mem_union, Finset.mem_image] at hcU
      rcases hcU.1 with ⟨g, _, hg⟩ | ⟨g, _, hg⟩
      · rw [← hg]; exact hbv g (by rw [hg]; exact le_trans hcon (le_of_lt hct))
      · rw [← hg]; exact hbp g (by rw [hg]; exact le_trans hcon (le_of_lt hct))
    linarith
  · -- no breakpoint above `t₀`
    rw [Finset.not_nonempty_iff_eq_empty] at hU
    have hle : ∀ g, v g ≤ t₀ ∧ p g ≤ t₀ := by
      intro g
      constructor
      · by_contra hcontra
        push_neg at hcontra
        have : v g ∈ U := by
          simp only [hUdef, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
          exact ⟨Or.inl ⟨g, Finset.mem_univ g, rfl⟩, hcontra⟩
        rw [hU] at this; exact absurd this (Finset.notMem_empty _)
      · by_contra hcontra
        push_neg at hcontra
        have : p g ∈ U := by
          simp only [hUdef, Finset.mem_filter, Finset.mem_union, Finset.mem_image]
          exact ⟨Or.inr ⟨g, Finset.mem_univ g, rfl⟩, hcontra⟩
        rw [hU] at this; exact absurd this (Finset.notMem_empty _)
    set c := t₀ + 1 with hcdef
    have hct : t₀ < c := by simp [hcdef]
    have hnb : NoBreak v p a c := by
      intro g
      refine ⟨Or.inl ?_, Or.inl ?_⟩
      · by_contra hcontra
        push_neg at hcontra
        have : v g ∈ L := by
          simp only [hLdef, Finset.mem_filter, Finset.mem_insert, Finset.mem_union,
            Finset.mem_image]
          exact ⟨Or.inr ⟨Or.inl ⟨g, Finset.mem_univ g, rfl⟩, le_trans hba (le_of_lt hcontra)⟩,
            lt_of_le_of_ne (hle g).1 (hnotv g)⟩
        exact absurd (hamax _ this) (not_le.mpr hcontra)
      · by_contra hcontra
        push_neg at hcontra
        have : p g ∈ L := by
          simp only [hLdef, Finset.mem_filter, Finset.mem_insert, Finset.mem_union,
            Finset.mem_image]
          exact ⟨Or.inr ⟨Or.inr ⟨g, Finset.mem_univ g, rfl⟩, le_trans hba (le_of_lt hcontra)⟩,
            lt_of_le_of_ne (hle g).2 (hnotp g)⟩
        exact absurd (hamax _ this) (not_le.mpr hcontra)
    have hcgt := main c hct hnb
    -- but `f(c) = f(t₀) = t₀ < c`
    have hfc : truncSum n v p c = t₀ := by
      rw [truncSum_of_ge v p (fun g => le_trans (hle g).1 (le_of_lt hct)),
        ← truncSum_of_ge (n := n) v p (fun g => (hle g).1), hfix]
    rw [hfc] at hcgt
    linarith
end FairSelling
