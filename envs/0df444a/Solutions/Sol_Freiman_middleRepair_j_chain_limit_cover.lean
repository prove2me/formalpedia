-- Prove2me | solution 1 for Freiman.middleRepair_j_chain_limit_cover
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:56:09.996147+00:00
-- url     : https://prove2.me/submissions/3d79b4d7-bb35-4e8d-8586-43098c0e9363

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Definitions.Def_Freiman_middleRepair

open Freiman

theorem solution :
    ∀ c : MiddleCore,
      (∀ k : ℕ, 1 ≤ k → (middleCover (middleRepairJ c k) ∩ middleCover (middleRepairJ c (k+2))).Nonempty) →
      Filter.Tendsto (fun k : ℕ => (middleBounds (middleRepairJ c k)).1) Filter.atTop (nhds (middleLimitValue c)) →
      Filter.Tendsto (fun k : ℕ => (middleBounds (middleRepairJ c k)).2) Filter.atTop (nhds (middleLimitValue c)) →
      ∀ t ∈ middleRepairJSpan c, t=middleLimitValue c ∨ ∃ k : ℕ, 1 ≤ k ∧ t∈middleCover (middleRepairJ c k) := by
  intro c hc hl hu t ht
  by_contra hnot
  have hne : t ≠ middleLimitValue c := fun h => hnot (Or.inl h)
  have hn : ∀ k : ℕ, 1 ≤ k → t ∉ middleCover (middleRepairJ c k) :=
    fun k hk h => hnot (Or.inr ⟨k,hk,h⟩)
  change min (middleBounds (middleRepairJ c 1)).1
      (middleBounds (middleRepairJ c 2)).1 ≤ t ∧
      t ≤ max (middleBounds (middleRepairJ c 1)).2
      (middleBounds (middleRepairJ c 2)).2 at ht
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstart : ∃ i : ℕ, 1 ≤ i ∧ (middleBounds (middleRepairJ c i)).1 ≤ t := by
      rcases min_le_iff.mp ht.1 with h | h
      · exact ⟨1,by omega,h⟩
      · exact ⟨2,by omega,h⟩
    obtain ⟨i,hi,hs⟩ := hstart
    have hseq : ∀ n : ℕ, (middleBounds (middleRepairJ c (2*n+i))).2 < t := by
      intro n
      induction n with
      | zero =>
        simp only [Nat.mul_zero, Nat.zero_add]
        by_contra h
        exact hn i hi ⟨hs,le_of_not_gt h⟩
      | succ n ih =>
        obtain ⟨x,hx,hx'⟩ := hc (2*n+i) (by omega)
        have hb : (middleBounds (middleRepairJ c (2*n+i+2))).1 < t :=
          lt_of_le_of_lt hx'.1 (lt_of_le_of_lt hx.2 ih)
        have hn' := hn (2*n+i+2) (by omega)
        have hout : (middleBounds (middleRepairJ c (2*n+i+2))).2 < t := by
          by_contra h
          exact hn' ⟨le_of_lt hb,le_of_not_gt h⟩
        convert hout using 1 <;> congr 3 <;> omega
    have hev : ∀ᶠ k : ℕ in Filter.atTop, t < (middleBounds (middleRepairJ c k)).2 :=
      hu.eventually (Ioi_mem_nhds hlt)
    obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hev
    exact (not_lt_of_gt (hseq N)) (hN (2*N+i) (by omega))
  · have hstart : ∃ i : ℕ, 1 ≤ i ∧ t ≤ (middleBounds (middleRepairJ c i)).2 := by
      rcases le_max_iff.mp ht.2 with h | h
      · exact ⟨1,by omega,h⟩
      · exact ⟨2,by omega,h⟩
    obtain ⟨i,hi,hs⟩ := hstart
    have hseq : ∀ n : ℕ, t < (middleBounds (middleRepairJ c (2*n+i))).1 := by
      intro n
      induction n with
      | zero =>
        simp only [Nat.mul_zero, Nat.zero_add]
        by_contra h
        exact hn i hi ⟨le_of_not_gt h,hs⟩
      | succ n ih =>
        obtain ⟨x,hx,hx'⟩ := hc (2*n+i) (by omega)
        have hb : t < (middleBounds (middleRepairJ c (2*n+i+2))).2 :=
          lt_of_lt_of_le (lt_of_lt_of_le ih hx.1) hx'.2
        have hn' := hn (2*n+i+2) (by omega)
        have hout : t < (middleBounds (middleRepairJ c (2*n+i+2))).1 := by
          by_contra h
          exact hn' ⟨le_of_not_gt h,le_of_lt hb⟩
        convert hout using 1 <;> congr 3 <;> omega
    have hev : ∀ᶠ k : ℕ in Filter.atTop, (middleBounds (middleRepairJ c k)).1 < t :=
      hl.eventually (Iio_mem_nhds hgt)
    obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hev
    exact (not_lt_of_gt (hseq N)) (hN (2*N+i) (by omega))

#print axioms solution
