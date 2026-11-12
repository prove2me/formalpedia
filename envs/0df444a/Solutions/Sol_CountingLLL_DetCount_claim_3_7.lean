-- Prove2me | solution 1 for CountingLLL.DetCount.claim_3_7
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T16:18:35.827209+00:00
-- url     : https://prove2.me/submissions/25a2f150-f201-4f8d-b39c-2ffe2e6cbbbc

import Mathlib

set_option autoImplicit false

private lemma prod_bound {α : Type*} [DecidableEq α] (s : Finset α) (t B : ℝ)
    (ht : t < 1) (hB0 : 0 ≤ B) (x y : α → ℝ)
    (hx : ∀ i ∈ s, |x i| ≤ t) (hy : ∀ i ∈ s, |y i| ≤ t)
    (hB : ∀ i ∈ s, |x i - y i| ≤ B) :
    |∏ i ∈ s, 1 / (1 - x i) - ∏ i ∈ s, 1 / (1 - y i)|
      ≤ s.card / (1 - t) ^ (s.card + 1) * B := by
  classical
  induction s using Finset.induction_on generalizing x y B with
  | empty => simp
  | insert a s ha ih =>
    have h1 : 0 < 1 - t := by linarith
    have hxa : |x a| ≤ t := hx a (Finset.mem_insert_self a s)
    have hya : |y a| ≤ t := hy a (Finset.mem_insert_self a s)
    have hxa_le : x a ≤ t := (abs_le.mp hxa).2
    have hya_le : y a ≤ t := (abs_le.mp hya).2
    have hx1 : 1 - t ≤ 1 - x a := by linarith
    have hy1 : 1 - t ≤ 1 - y a := by linarith
    have hxpos : 0 < 1 - x a := by linarith
    have hypos : 0 < 1 - y a := by linarith
    have hfa : |1 / (1 - x a)| ≤ 1 / (1 - t) := by
      rw [abs_of_pos (by positivity)]
      exact one_div_le_one_div_of_le h1 hx1
    set P : ℝ := ∏ i ∈ s, 1 / (1 - x i) with hP
    set Q : ℝ := ∏ i ∈ s, 1 / (1 - y i) with hQ
    have hPQ : |P - Q| ≤ s.card / (1 - t) ^ (s.card + 1) * B :=
      ih B hB0 x y
        (fun i hi => hx i (Finset.mem_insert_of_mem hi))
        (fun i hi => hy i (Finset.mem_insert_of_mem hi))
        (fun i hi => hB i (Finset.mem_insert_of_mem hi))
    have hQb : |Q| ≤ (1 / (1 - t)) ^ s.card := by
      rw [hQ, Finset.abs_prod]
      calc (∏ i ∈ s, |1 / (1 - y i)|) ≤ ∏ i ∈ s, (1 / (1 - t)) := by
            apply Finset.prod_le_prod
            · intro i hi
              positivity
            · intro i hi
              have hyi : |y i| ≤ t := hy i (Finset.mem_insert_of_mem hi)
              rw [abs_of_pos (by apply div_pos one_pos; linarith [ (abs_le.mp hyi).2 ])]
              exact one_div_le_one_div_of_le h1 (by linarith [ (abs_le.mp hyi).2 ])
        _ = (1 / (1 - t)) ^ s.card := by simp
    have hdiff : |1 / (1 - x a) - 1 / (1 - y a)| ≤ B / (1 - t) ^ 2 := by
      have heq : 1 / (1 - x a) - 1 / (1 - y a) =
          (x a - y a) / ((1 - x a) * (1 - y a)) := by
        field_simp
        ring
      have hprod_pos : 0 < (1 - x a) * (1 - y a) := mul_pos hxpos hypos
      have hprod_ge : (1 - t) ^ 2 ≤ (1 - x a) * (1 - y a) := by nlinarith
      have hsq_pos : 0 < (1 - t) ^ 2 := by positivity
      rw [heq, abs_div, abs_of_pos hprod_pos]
      calc |x a - y a| / ((1 - x a) * (1 - y a))
          ≤ |x a - y a| / (1 - t) ^ 2 :=
            div_le_div_of_nonneg_left (abs_nonneg _) hsq_pos hprod_ge
        _ ≤ B / (1 - t) ^ 2 :=
            div_le_div_of_nonneg_right (hB a (Finset.mem_insert_self a s)) (by positivity)
    have hdecomp : (1 / (1 - x a)) * P - (1 / (1 - y a)) * Q
        = (1 / (1 - x a)) * (P - Q) + ((1 / (1 - x a)) - (1 / (1 - y a))) * Q := by
      ring
    have hgoal : |(1 / (1 - x a)) * P - (1 / (1 - y a)) * Q|
        ≤ ((s.card + 1 : ℕ) : ℝ) / (1 - t) ^ (s.card + 2) * B := by
      rw [hdecomp]
      calc |(1 / (1 - x a)) * (P - Q) + ((1 / (1 - x a)) - (1 / (1 - y a))) * Q|
          ≤ |(1 / (1 - x a)) * (P - Q)| +
              |((1 / (1 - x a)) - (1 / (1 - y a))) * Q| := abs_add_le _ _
        _ = |1 / (1 - x a)| * |P - Q| +
              |1 / (1 - x a) - 1 / (1 - y a)| * |Q| := by
            rw [abs_mul, abs_mul]
        _ ≤ (1 / (1 - t)) * (s.card / (1 - t) ^ (s.card + 1) * B) +
              (B / (1 - t) ^ 2) * (1 / (1 - t)) ^ s.card := by
            apply add_le_add
            · exact mul_le_mul hfa hPQ (abs_nonneg _) (by positivity)
            · exact mul_le_mul hdiff hQb (abs_nonneg _) (by positivity)
        _ = ((s.card + 1 : ℕ) : ℝ) / (1 - t) ^ (s.card + 2) * B := by
            have hp1 : (1 - t) ^ (s.card + 1) = (1 - t) ^ s.card * (1 - t) := by
              rw [pow_add, pow_one]
            have hp2 : (1 - t) ^ (s.card + 2) = (1 - t) ^ s.card * (1 - t) ^ 2 := by
              rw [pow_add]
            rw [hp1, hp2, one_div_pow]
            field_simp
            rw [Nat.cast_add, Nat.cast_one]
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    simpa [hP, hQ, Nat.cast_add, Nat.cast_one] using hgoal

/-- Claim 3.7: the product `∏ 1/(1 - x_i)` is Lipschitz on `[-t,t]^ℓ`. -/
theorem solution (t : ℝ) (ht₀ : 0 < t) (ht₁ : t < 1) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (x y : Fin ℓ → ℝ) (hx : ∀ i, x i ∈ Set.Icc (-t) t)
    (hy : ∀ i, y i ∈ Set.Icc (-t) t) :
    |∏ i, 1 / (1 - x i) - ∏ i, 1 / (1 - y i)| ≤
      (ℓ : ℝ) / (1 - t) ^ (ℓ + 1) *
        (Finset.univ : Finset (Fin ℓ)).sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hℓ⟩⟩)
          (fun i => |x i - y i|) := by
  classical
  have hne : (Finset.univ : Finset (Fin ℓ)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hℓ⟩⟩
  set B : ℝ := (Finset.univ : Finset (Fin ℓ)).sup' hne (fun i => |x i - y i|) with hB
  have hB0 : 0 ≤ B := by
    have h := Finset.le_sup' (s := (Finset.univ : Finset (Fin ℓ)))
      (f := fun i => |x i - y i|) (Finset.mem_univ ⟨0, hℓ⟩)
    have h' : |x ⟨0, hℓ⟩ - y ⟨0, hℓ⟩| ≤ B := by
      rw [hB]
      exact h
    exact le_trans (abs_nonneg _) h' 
  have h := prod_bound (Finset.univ : Finset (Fin ℓ)) t B ht₁ hB0 x y
    (fun i _ => abs_le.mpr (hx i))
    (fun i _ => abs_le.mpr (hy i))
    (fun i _ => by
      rw [hB]
      exact Finset.le_sup' (s := (Finset.univ : Finset (Fin ℓ)))
        (f := fun j => |x j - y j|) (Finset.mem_univ i))
  simpa [B, hB, Finset.card_univ] using h
