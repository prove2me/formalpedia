-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:08:02.272766+00:00
-- url     : https://prove2.me/submissions/d065201e-86e7-443a-993d-d8820822dfc2

import Definitions.Def_EdgeSublinearMWIS_Main_Relaxation

open scoped BigOperators
open EdgeSublinearMWIS.Main

set_option autoImplicit false

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) (k : ℤ) (hr : 1 ≤ r)
    (D A : Finset (Fin n)) (u : ℝ) (upper : (alpha G D : ℝ) ≤ u) (size : A.card ≤ r) :
    (∀ z : Finset (Fin n) → ℝ, InHull G Finset.univ r k z →
      (∑ v ∈ D, z (insert v A)) ≤ u * z A) ∧
    (∀ y : Finset (Fin n) → ℝ, 0 < y A →
      u < (∑ v ∈ D, y (insert v A) / y A) →
      u * y A < ∑ v ∈ D, y (insert v A)) := by
  classical
  have memA : A ∈ Coordinates (Finset.univ : Finset (Fin n)) r := by
    simp only [Coordinates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ _, by omega⟩
  have memInsert (v : Fin n) : insert v A ∈ Coordinates (Finset.univ : Finset (Fin n)) r := by
    simp only [Coordinates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ _, (Finset.card_insert_le _ _).trans (by omega)⟩
  let S : Set ({B // B ∈ Coordinates (Finset.univ : Finset (Fin n)) r} → ℝ) :=
    {z | (∑ v ∈ D, z ⟨insert v A, memInsert v⟩) ≤ u * z ⟨A, memA⟩}
  have convexS : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    change (∑ v ∈ D, (a * x ⟨insert v A, memInsert v⟩ + b * y ⟨insert v A, memInsert v⟩)) ≤
      u * (a * x ⟨A, memA⟩ + b * y ⟨A, memA⟩)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    change (∑ v ∈ D, x ⟨insert v A, memInsert v⟩) ≤ u * x ⟨A, memA⟩ at hx
    change (∑ v ∈ D, y ⟨insert v A, memInsert v⟩) ≤ u * y ⟨A, memA⟩ at hy
    nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]
  constructor
  · intro z hz
    have generators : {z | ∃ I ⊆ (Finset.univ : Finset (Fin n)),
        G.IsIndepSet (I : Set (Fin n)) ∧ (I.card : ℤ) = k ∧
          z = indicatorPoint Finset.univ I r} ⊆ S := by
      rintro x ⟨I, hI, hind, hcard, rfl⟩
      change (∑ v ∈ D, if insert v A ⊆ I then (1 : ℝ) else 0) ≤
        u * (if A ⊆ I then 1 else 0)
      by_cases hAI : A ⊆ I
      · simp only [hAI, ite_true, mul_one]
        have hsub (v : Fin n) : insert v A ⊆ I ↔ v ∈ I := by
          constructor
          · intro h; exact h (Finset.mem_insert_self _ _)
          · intro h; exact Finset.insert_subset h hAI
        simp only [hsub]
        have heq : (∑ v ∈ D, if v ∈ I then (1 : ℝ) else 0) = ((D ∩ I).card : ℝ) := by
          simp
        rw [heq]
        apply le_trans ?_ upper
        change ((D ∩ I).card : ℝ) ≤ ((D.powerset.filter (fun (J : Finset (Fin n)) => G.IsIndepSet (J : Set (Fin n)))).sup Finset.card : ℕ)
        exact_mod_cast (Finset.le_sup (f := Finset.card)
          (show D ∩ I ∈ D.powerset.filter (fun (J : Finset (Fin n)) => G.IsIndepSet (J : Set (Fin n))) from by
            simp only [Finset.mem_filter, Finset.mem_powerset]
            exact ⟨Finset.inter_subset_left, hind.mono (by
              intro v hv
              exact (Finset.mem_inter.mp hv).2)⟩))
      · have hnot (v : Fin n) : ¬ insert v A ⊆ I := fun h => hAI (Finset.Subset.trans (Finset.subset_insert _ _) h)
        simp [hAI, hnot]
    exact (convexHull_min generators convexS) hz
  · intro y hy hviol
    rw [← Finset.sum_div] at hviol
    exact (lt_div_iff₀ hy).mp hviol
