-- Prove2me | solution 1 for ConvexOptAlg.CenterGravity.eq_2_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-05T20:00:58.597987+00:00
-- url     : https://prove2.me/submissions/1570183e-ec48-4785-a139-05c73817b1a2

import Mathlib
import Definitions.Def_ConvexOptAlg_CenterGravity_Defs

open MeasureTheory
open scoped InnerProductSpace

namespace CGAux

open ConvexOptAlg.CenterGravity

theorem inner_cut_neg {n : ℕ} (c x w : EuclideanSpace ℝ (Fin n)) :
    ⟪w, c - x⟫_ℝ = -⟪x - c, w⟫_ℝ := by
  rw [real_inner_comm, ← inner_neg_left]; congr 1; abel

theorem S_subset {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {S : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    {c w : ℕ → EuclideanSpace ℝ (Fin n)} (hrun : IsCenterOfGravityRun X f S c w) :
    ∀ s, 1 ≤ s → S s ⊆ X := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => rw [hrun.init]
  | succ s hs ih => rw [hrun.cut s hs]; exact Set.inter_subset_left.trans ih

theorem removed_pos {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {S : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    {c w : ℕ → EuclideanSpace ℝ (Fin n)} (hrun : IsCenterOfGravityRun X f S c w)
    (s : ℕ) (hs : 1 ≤ s) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S s) (hx' : x ∉ S (s + 1)) :
    0 < ⟪x - c s, w s⟫_ℝ := by
  rw [hrun.cut s hs] at hx'
  by_contra h
  exact hx' ⟨hx, not_lt.mp h⟩

theorem removed_gt {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {S : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    {c w : ℕ → EuclideanSpace ℝ (Fin n)} (hrun : IsCenterOfGravityRun X f S c w)
    (s : ℕ) (hs : 1 ≤ s) {x : EuclideanSpace ℝ (Fin n)} (hxX : x ∈ X)
    (hpos : 0 < ⟪x - c s, w s⟫_ℝ) : f (c s) < f x := by
  have h := (hrun.oracle s hs).2 x hxX
  rw [inner_cut_neg] at h
  linarith

theorem xstar_mem {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {S : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    {c w : ℕ → EuclideanSpace ℝ (Fin n)} (hrun : IsCenterOfGravityRun X f S c w)
    {xstar : EuclideanSpace ℝ (Fin n)} (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y) :
    ∀ t, 1 ≤ t → xstar ∈ S t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rw [hrun.init]; exact hxstar
  | succ t ht ih =>
    rw [hrun.cut t ht]
    refine ⟨ih, ?_⟩
    have h1 := (hrun.oracle t ht).2 xstar hxstar
    have h2 := hmin _ (hrun.oracle t ht).1
    rw [inner_cut_neg] at h1
    show ⟪xstar - c t, w t⟫_ℝ ≤ 0
    linarith

end CGAux

theorem solution {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (hX : ConvexOptAlg.CenterGravity.IsConvexBody X)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ} (hfB : ∀ x ∈ X, |f x| ≤ B)
    (hfc : ContinuousOn f X) (hfconv : ConvexOn ℝ X f)
    {xstar : EuclideanSpace ℝ (Fin n)} (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    {S : ℕ → Set (EuclideanSpace ℝ (Fin n))} {c w : ℕ → EuclideanSpace ℝ (Fin n)}
    (hrun : ConvexOptAlg.CenterGravity.IsCenterOfGravityRun X f S c w) (t : ℕ) (ht : 1 ≤ t) :
    (S t \ S (t + 1) ⊆ {x | x ∈ X ∧ 0 < ⟪x - c t, w t⟫_ℝ} ∧
      {x | x ∈ X ∧ 0 < ⟪x - c t, w t⟫_ℝ} ⊆ {x | x ∈ X ∧ f (c t) < f x}) ∧
    xstar ∈ S t := by
  refine ⟨⟨?_, ?_⟩, CGAux.xstar_mem hrun hxstar hmin t ht⟩
  · intro x hx
    exact ⟨CGAux.S_subset hrun t ht hx.1, CGAux.removed_pos hrun t ht hx.1 hx.2⟩
  · intro x hx
    exact ⟨hx.1, CGAux.removed_gt hrun t ht hx.1 hx.2⟩
