-- Prove2me | solution 1 for FFactor.card_witness_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:02:36.037821+00:00
-- url     : https://prove2.me/submissions/f139c294-ce39-47de-8c3d-851696ba9fe1

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorNec
public import Theorems.Thm_FFactor_sum_split3

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V]
open Classical
namespace FFactor
theorem _root_.solution (G H : SimpleGraph V) (hHG : H ≤ G) (f : V → ℕ)
    (hdeg : ∀ v, #{u | H.Adj v u} = f v) (S T : Finset V) (hST : Disjoint S T) :
    (#{p ∈ (univ \ (S ∪ T)) ×ˢ (univ : Finset V) |
      (p.2 ∈ S ∧ H.Adj p.1 p.2) ∨ (p.2 ∈ T ∧ G.Adj p.1 p.2 ∧ ¬H.Adj p.1 p.2)} : ℤ) ≤
      ∑ v ∈ S, (f v : ℤ) - ∑ v ∈ T, (f v : ℤ) + ∑ v ∈ T, (#{u | G.Adj v u ∧ u ∉ S} : ℤ) := by
  set R := univ \ (S ∪ T) with hR
  let A : V → V → ℤ := fun x y => if H.Adj x y then 1 else 0
  let B : V → V → ℤ := fun x y => if G.Adj x y then 1 else 0
  have hAsymm : ∀ x y, A x y = A y x := fun x y => by simp only [A, H.adj_comm]
  have hBsymm : ∀ x y, B x y = B y x := fun x y => by simp only [B, G.adj_comm]
  have hA0 : ∀ x y, 0 ≤ A x y := fun x y => by simp only [A]; split_ifs <;> norm_num
  have hAB : ∀ x y, A x y ≤ B x y := fun x y => by
    by_cases h1 : H.Adj x y
    · simp [A, B, h1, hHG h1]
    · by_cases h2 : G.Adj x y <;> simp [A, B, h1, h2]
  have hmemR : ∀ u, u ∈ R ↔ u ∉ S ∧ u ∉ T := fun u => by simp [hR]
  have hf : ∀ v, (f v : ℤ) = ∑ u, A v u := fun v => by
    rw [← hdeg v, card_filter]; push_cast; rfl
  have hN : ∀ t, (#{u | G.Adj t u ∧ u ∉ S} : ℤ) = ∑ u ∈ T, B t u + ∑ u ∈ R, B t u := by
    intro t
    rw [card_filter]; push_cast
    rw [sum_split3 hST]
    have h1 : ∑ u ∈ S, (if G.Adj t u ∧ u ∉ S then (1 : ℤ) else 0) = 0 :=
      sum_eq_zero (fun u hu => by simp [hu])
    have h2 : ∑ u ∈ T, (if G.Adj t u ∧ u ∉ S then (1 : ℤ) else 0) = ∑ u ∈ T, B t u :=
      sum_congr rfl (fun u hu => by
        have : u ∉ S := fun h => disjoint_left.mp hST h hu
        simp [B, this])
    have h3 : ∑ u ∈ R, (if G.Adj t u ∧ u ∉ S then (1 : ℤ) else 0) = ∑ u ∈ R, B t u :=
      sum_congr rfl (fun u hu => by simp [B, ((hmemR u).mp hu).1])
    rw [h1, h2, h3, zero_add]
  have hZ : (#{p ∈ R ×ˢ (univ : Finset V) |
      (p.2 ∈ S ∧ H.Adj p.1 p.2) ∨ (p.2 ∈ T ∧ G.Adj p.1 p.2 ∧ ¬H.Adj p.1 p.2)} : ℤ) =
      ∑ w ∈ R, (∑ u ∈ S, A w u + ∑ u ∈ T, (B w u - A w u)) := by
    rw [card_filter]; push_cast
    rw [sum_product]
    refine sum_congr rfl (fun w _ => ?_)
    rw [sum_split3 hST]
    have h1 : ∑ u ∈ S, (if (u ∈ S ∧ H.Adj w u) ∨ (u ∈ T ∧ G.Adj w u ∧ ¬H.Adj w u)
        then (1 : ℤ) else 0) = ∑ u ∈ S, A w u :=
      sum_congr rfl (fun u hu => by
        have : u ∉ T := fun h => disjoint_left.mp hST hu h
        simp [A, hu, this])
    have h2 : ∑ u ∈ T, (if (u ∈ S ∧ H.Adj w u) ∨ (u ∈ T ∧ G.Adj w u ∧ ¬H.Adj w u)
        then (1 : ℤ) else 0) = ∑ u ∈ T, (B w u - A w u) :=
      sum_congr rfl (fun u hu => by
        have : u ∉ S := fun h => disjoint_left.mp hST h hu
        simp only [this, hu, false_and, true_and, false_or, A, B]
        by_cases h1 : H.Adj w u
        · simp [h1, hHG h1]
        · by_cases h2 : G.Adj w u <;> simp [h1, h2])
    have h3 : ∑ u ∈ R, (if (u ∈ S ∧ H.Adj w u) ∨ (u ∈ T ∧ G.Adj w u ∧ ¬H.Adj w u)
        then (1 : ℤ) else 0) = 0 :=
      sum_eq_zero (fun u hu => by simp [((hmemR u).mp hu).1, ((hmemR u).mp hu).2])
    rw [h1, h2, h3, add_zero]
  rw [hZ]
  simp only [hf, hN, sum_split3 hST]
  have e1 : ∑ w ∈ R, ∑ u ∈ S, A w u = ∑ s ∈ S, ∑ u ∈ R, A s u := by
    rw [sum_comm]; exact sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => hAsymm _ _))
  have e2 : ∑ w ∈ R, ∑ u ∈ T, (B w u - A w u) = ∑ t ∈ T, ∑ u ∈ R, (B t u - A t u) := by
    rw [sum_comm]
    exact sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => by rw [hAsymm, hBsymm]))
  have e3 : ∑ s ∈ S, ∑ u ∈ T, A s u = ∑ t ∈ T, ∑ u ∈ S, A t u := by
    rw [sum_comm]; exact sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => hAsymm _ _))
  have p1 : 0 ≤ ∑ s ∈ S, ∑ u ∈ S, A s u := sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => hA0 _ _))
  have p2 : 0 ≤ ∑ t ∈ T, ∑ u ∈ T, (B t u - A t u) :=
    sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sub_nonneg.mpr (hAB _ _)))
  simp only [sum_add_distrib, sum_sub_distrib] at e2 p2 ⊢
  linarith
end FFactor
