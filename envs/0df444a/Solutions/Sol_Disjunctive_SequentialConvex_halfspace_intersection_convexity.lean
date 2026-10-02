-- Prove2me | solution 1 for Disjunctive.SequentialConvex.halfspace_intersection_convexity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T04:02:25.134873+00:00
-- url     : https://prove2.me/submissions/be43b271-8739-4143-80c9-b56e131b24bf

import Mathlib
import Definitions.Def_Disjunctive_SequentialConvex_Basic

set_option autoImplicit false

namespace Disjunctive.SequentialConvex

theorem a336_dot_comb {n : ℕ} (d x y : Fin n → ℝ) (a b : ℝ) :
    dotProduct d (a • x + b • y) = a * dotProduct d x + b * dotProduct d y := by
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]

theorem a336_convex_le {n : ℕ} (d : Fin n → ℝ) (d0 : ℝ) : Convex ℝ (HalfspaceLE d d0) := by
  intro x hx y hy a b ha hb hab
  simp only [HalfspaceLE, Set.mem_ofPred_eq] at hx hy ⊢
  rw [a336_dot_comb]
  have h1 := mul_le_mul_of_nonneg_left hx ha
  have h2 := mul_le_mul_of_nonneg_left hy hb
  have h3 : a * d0 + b * d0 = d0 := by rw [← add_mul, hab, one_mul]
  linarith

theorem a336_convex_ge {n : ℕ} (d : Fin n → ℝ) (d0 : ℝ) : Convex ℝ (HalfspaceGE d d0) := by
  intro x hx y hy a b ha hb hab
  simp only [HalfspaceGE, Set.mem_ofPred_eq] at hx hy ⊢
  rw [a336_dot_comb]
  have h1 := mul_le_mul_of_nonneg_left hx ha
  have h2 := mul_le_mul_of_nonneg_left hy hb
  have h3 : a * d0 + b * d0 = d0 := by rw [← add_mul, hab, one_mul]
  linarith

theorem a336_general {n : ℕ} (S : Set (Fin n → ℝ)) (d : Fin n → ℝ) (d0 : ℝ)
    (hSub : S ⊆ HalfspaceLE d d0) :
    HalfspaceGE d d0 ∩ convexHull ℝ S = convexHull ℝ (HalfspaceGE d d0 ∩ S) := by
  have hLE : convexHull ℝ S ⊆ HalfspaceLE d d0 := convexHull_min hSub (a336_convex_le d d0)
  apply Set.Subset.antisymm
  · rintro x ⟨hxge, hxS⟩
    let C : Set (Fin n → ℝ) := {y | dotProduct d y ≤ d0 ∧
      (dotProduct d y = d0 → y ∈ convexHull ℝ (HalfspaceGE d d0 ∩ S))}
    have hSC : S ⊆ C := by
      intro z hz
      refine ⟨hSub hz, fun hz0 => subset_convexHull ℝ _ ⟨?_, hz⟩⟩
      show d0 ≤ dotProduct d z
      rw [hz0]
    have hCc : Convex ℝ C := by
      intro u hu v hv a b ha hb hab
      obtain ⟨hu', ihu⟩ := hu
      obtain ⟨hv', ihv⟩ := hv
      have h1 := mul_le_mul_of_nonneg_left hu' ha
      have h2 := mul_le_mul_of_nonneg_left hv' hb
      have h3 : a * d0 + b * d0 = d0 := by rw [← add_mul, hab, one_mul]
      refine ⟨?_, fun h0 => ?_⟩
      · show dotProduct d (a • u + b • v) ≤ d0
        rw [a336_dot_comb]; linarith
      · change dotProduct d (a • u + b • v) = d0 at h0
        rw [a336_dot_comb] at h0
        rcases ha.lt_or_eq with ha' | ha'
        · rcases hb.lt_or_eq with hb' | hb'
          · have hu0 : dotProduct d u = d0 := by
              by_contra hne
              have hlt : dotProduct d u < d0 := lt_of_le_of_ne hu' hne
              have := mul_lt_mul_of_pos_left hlt ha'
              linarith
            have hv0 : dotProduct d v = d0 := by
              by_contra hne
              have hlt : dotProduct d v < d0 := lt_of_le_of_ne hv' hne
              have := mul_lt_mul_of_pos_left hlt hb'
              linarith
            exact (convex_convexHull ℝ _) (ihu hu0) (ihv hv0) ha hb hab
          · subst hb'
            have ha1 : a = 1 := by linarith
            subst ha1
            have hu0 : dotProduct d u = d0 := by linarith
            simpa using ihu hu0
        · subst ha'
          have hb1 : b = 1 := by linarith
          subst hb1
          have hv0 : dotProduct d v = d0 := by linarith
          simpa using ihv hv0
    have hxC : x ∈ C := convexHull_min hSC hCc hxS
    have key : ∀ y, y ∈ C → dotProduct d y = d0 →
        y ∈ convexHull ℝ (HalfspaceGE d d0 ∩ S) := fun y hy h => hy.2 h
    have hle : dotProduct d x ≤ d0 := hLE hxS
    have hge : d0 ≤ dotProduct d x := hxge
    exact key x hxC (le_antisymm hle hge)
  · intro x hx
    refine ⟨convexHull_min Set.inter_subset_left (a336_convex_ge d d0) hx,
      convexHull_mono Set.inter_subset_right hx⟩

end Disjunctive.SequentialConvex

open Disjunctive.SequentialConvex in
theorem solution {n r : ℕ} {m : Fin r → ℕ}
    (A : (h : Fin r) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Fin r) → Fin (m h) → ℝ)
    (d : Fin n → ℝ) (d0 : ℝ) (hSub : (⋃ h : Fin r, Poly (A h) (b h)) ⊆ HalfspaceLE d d0) :
    HalfspaceGE d d0 ∩ convexHull ℝ (⋃ h : Fin r, Poly (A h) (b h)) =
      convexHull ℝ (HalfspaceGE d d0 ∩ ⋃ h : Fin r, Poly (A h) (b h)) := by
  exact a336_general _ d d0 hSub
