-- Prove2me | solution 1 for Disjunctive.LiftProject.fractionality_intermediate_points_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:19:19.253719+00:00
-- url     : https://prove2.me/submissions/769051f6-7bfb-4342-9c54-e2a619fa5cac

import Mathlib
import Definitions.Def_Disjunctive_LiftProject_Basic
import Definitions.Def_Disjunctive_LiftProject_BoundRows



namespace Disjunctive.LiftProject

theorem frac_core {n m : ℕ} (Atil : Matrix (Fin m) (Fin n) ℝ)
    (btil : Fin m → ℝ) (Nprime : Finset (Fin n)) (hP : HasBoundRows Atil btil Nprime)
    (i1 ij : Fin n) (hij : ij ∈ Nprime) (α : Fin n → ℝ) (β : ℝ)
    (hValid : ∀ x ∈ SplitConvexify (SplitConvexify (Poly Atil btil) i1) ij, β ≤ dotProduct α x)
    (xstar : Fin n → ℝ)
    (hExt : xstar ∈ Set.extremePoints ℝ
      (SplitConvexify (Poly Atil btil) i1 ∩ {x | β ≤ dotProduct α x}))
    (h1 : 0 < xstar i1 ∧ xstar i1 < 1) :
    0 < xstar ij ∧ xstar ij < 1 := by
  -- bounds on P₁
  have hK : ∀ y ∈ SplitConvexify (Poly Atil btil) i1, 0 ≤ y ij ∧ y ij ≤ 1 := by
    intro y hy
    have hconv : Convex ℝ {y : Fin n → ℝ | 0 ≤ y ij ∧ y ij ≤ 1} := by
      intro a ha b hb s t hs ht hst
      simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha hb ⊢
      constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]
    refine convexHull_min ?_ hconv hy
    rintro x ⟨hx, -⟩
    obtain ⟨ρ, hρA, hρb⟩ := hP.1 ij
    obtain ⟨σ, hσA, hσb⟩ := hP.2 ij hij
    have e1 := hx ρ
    have e2 := hx σ
    simp only [Matrix.mulVec, hρA, hρb, hσA, hσb, dotProduct, Pi.single_apply, Pi.neg_apply,
      ite_mul, one_mul, zero_mul, neg_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_neg_distrib] at e1 e2
    exact ⟨e1, by linarith⟩
  obtain ⟨⟨hxP1, hxH⟩, hxE⟩ := hExt
  by_contra hcon
  have hxb := hK xstar hxP1
  have h01 : xstar ij = 0 ∨ xstar ij = 1 := by
    by_contra h
    push_neg at h
    exact hcon ⟨lt_of_le_of_ne hxb.1 (Ne.symm h.1), lt_of_le_of_ne hxb.2 h.2⟩
  -- xstar is an extreme point of P₁
  have hE : xstar ∈ Set.extremePoints ℝ (SplitConvexify (Poly Atil btil) i1) := by
    refine ⟨hxP1, ?_⟩
    intro y hy z hz hseg
    obtain ⟨a, b, ha, hb, hab, hyz⟩ := hseg
    have hc := congrFun hyz ij
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hc
    have hyb := hK y hy
    have hzb := hK z hz
    have hyz01 : (y ij = 0 ∨ y ij = 1) ∧ (z ij = 0 ∨ z ij = 1) := by
      rcases h01 with h | h
      · rw [h] at hc
        have : y ij = 0 := by nlinarith
        have : z ij = 0 := by nlinarith
        exact ⟨Or.inl ‹_›, Or.inl ‹_›⟩
      · rw [h] at hc
        have : y ij = 1 := by nlinarith
        have : z ij = 1 := by nlinarith
        exact ⟨Or.inr ‹_›, Or.inr ‹_›⟩
    have hyH : β ≤ dotProduct α y := hValid y (subset_convexHull ℝ _ ⟨hy, hyz01.1⟩)
    have hzH : β ≤ dotProduct α z := hValid z (subset_convexHull ℝ _ ⟨hz, hyz01.2⟩)
    exact hxE ⟨hy, hyH⟩ ⟨hz, hzH⟩ ⟨a, b, ha, hb, hab, hyz⟩
  have := extremePoints_convexHull_subset hE
  rcases this.2 with h | h
  · linarith [h1.1]
  · linarith [h1.2]

end Disjunctive.LiftProject

open Disjunctive.LiftProject


theorem solution {n m : ℕ} (Atil : Matrix (Fin m) (Fin n) ℝ)
    (btil : Fin m → ℝ) (Nprime : Finset (Fin n)) (hP : HasBoundRows Atil btil Nprime)
    (i1 ij : Fin n) (hi1 : i1 ∈ Nprime) (hij : ij ∈ Nprime) (α : Fin n → ℝ) (β : ℝ)
    (hValid : ∀ x ∈ SplitConvexify (SplitConvexify (Poly Atil btil) i1) ij, β ≤ dotProduct α x)
    (xstar : Fin n → ℝ)
    (hExt : xstar ∈ Set.extremePoints ℝ
      (SplitConvexify (Poly Atil btil) i1 ∩ {x | β ≤ dotProduct α x}))
    (h1 : 0 < xstar i1 ∧ xstar i1 < 1) :
    0 < xstar ij ∧ xstar ij < 1 := by
  exact frac_core Atil btil Nprime hP i1 ij hij α β hValid xstar hExt h1
