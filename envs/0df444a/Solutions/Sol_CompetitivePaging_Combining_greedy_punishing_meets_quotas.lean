-- Prove2me | solution 1 for CompetitivePaging.Combining.greedy_punishing_meets_quotas
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:08:21.15852+00:00
-- url     : https://prove2.me/submissions/b1edf8d4-ec7d-4316-b92e-ceb653d6f4ab

import Mathlib



namespace CompetitivePaging.Combining

theorem greedy_gen {m : ℕ} (c : Fin m → ℝ) (hc : ∀ i, 0 < c i)
    (hsum : ∑ i, 1 / c i ≤ 1) (fault : ℕ → Prop) [DecidablePred fault]
    (choice : ℕ → Fin m) (P : ℕ → Fin m → ℕ) (F : ℕ → ℕ)
    (hP0 : ∀ i, P 0 i = 0) (hF0 : F 0 = 0)
    (hF : ∀ t, F (t + 1) = F t + if fault t then 1 else 0)
    (hP : ∀ t i, P t i + (if fault t ∧ choice t = i then 1 else 0) ≤ P (t + 1) i)
    (hg : ∀ t j, fault t → c (choice t) * ((P t (choice t) : ℝ) + 1) ≤ c j * ((P t j : ℝ) + 1)) :
    ∀ T i, ⌊(F T : ℝ) / c i⌋₊ ≤ P T i := by
  intro T i
  set R : ℕ := F T with hR
  have mono1 : ∀ t j, P t j ≤ P (t + 1) j := fun t j => le_trans (Nat.le_add_right _ _) (hP t j)
  have mono : ∀ s t j, s ≤ t → P s j ≤ P t j := by
    intro s t j hst
    induction t, hst using Nat.le_induction with
    | base => exact le_rfl
    | succ n _ ih => exact le_trans ih (mono1 n j)
  have key1 : ∀ j (p : ℕ), (R : ℝ) < c j * ((p : ℝ) + 1) → ⌊(R : ℝ) / c j⌋₊ ≤ p := by
    intro j p h
    have : (R : ℝ) / c j < (p : ℝ) + 1 := by rw [div_lt_iff₀ (hc j)]; linarith
    have h2 := (Nat.floor_lt (div_nonneg (Nat.cast_nonneg _) (hc j).le)).2 (by exact_mod_cast this : (R : ℝ) / c j < ((p + 1 : ℕ) : ℝ))
    omega
  have key2 : ∀ j (p : ℕ), c j * ((p : ℝ) + 1) ≤ (R : ℝ) → p + 1 ≤ ⌊(R : ℝ) / c j⌋₊ := by
    intro j p h
    apply Nat.le_floor
    rw [le_div_iff₀ (hc j)]; push_cast; linarith
  by_cases hA : ∃ t < T, fault t ∧ (R : ℝ) < c (choice t) * ((P t (choice t) : ℝ) + 1)
  · obtain ⟨t, htT, hft, hlt⟩ := hA
    exact le_trans (key1 i _ (lt_of_lt_of_le hlt (hg t i hft))) (mono t T i htT.le)
  push_neg at hA
  set Q : Fin m → ℕ := fun j => ⌊(R : ℝ) / c j⌋₊ with hQ
  have claim : ∀ t ≤ T, F t ≤ ∑ j, min (P t j) (Q j) := by
    intro t ht
    induction t with
    | zero => simp [hF0]
    | succ t ih =>
      have ih := ih (by omega)
      rw [hF t]
      by_cases hft : fault t
      · simp only [hft, if_true]
        have hle := hA t (by omega) hft
        have hb : ∑ j, (min (P t j) (Q j) + if choice t = j then 1 else 0)
            ≤ ∑ j, min (P (t + 1) j) (Q j) := by
          apply Finset.sum_le_sum
          intro j _
          by_cases hj : choice t = j
          · subst hj
            have h1 := key2 (choice t) _ hle
            have h2 := hP t (choice t)
            simp only [hft, true_and, if_true] at h2
            simp only [if_true]
            simp only [hQ] at h1 ⊢
            omega
          · simp only [hj, if_false, add_zero]
            exact min_le_min_right _ (mono1 t j)
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq] at hb
        simp at hb
        omega
      · simp only [hft, if_false, add_zero]
        refine le_trans ih (Finset.sum_le_sum fun j _ => min_le_min_right _ (mono1 t j))
  have hc1 := claim T le_rfl
  have hQsum : ∑ j, Q j ≤ R := by
    have : (∑ j, (Q j : ℝ)) ≤ R := by
      calc (∑ j, (Q j : ℝ)) ≤ ∑ j, (R : ℝ) / c j :=
            Finset.sum_le_sum fun j _ => Nat.floor_le (div_nonneg (by positivity) (hc j).le)
        _ = (R : ℝ) * ∑ j, 1 / c j := by rw [Finset.mul_sum]; congr 1; ext j; ring
        _ ≤ (R : ℝ) * 1 := mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = R := mul_one _
    exact_mod_cast this
  by_contra hne
  push_neg at hne
  have hlt : ∑ j, min (P T j) (Q j) < ∑ j, Q j := by
    apply Finset.sum_lt_sum (fun j _ => min_le_right _ _)
    exact ⟨i, Finset.mem_univ _, by simp only [hQ]; omega⟩
  omega

theorem greedy_core {m : ℕ} (c : Fin m → ℝ) (hc : ∀ i, 0 < c i)
    (hsum : ∑ i, 1 / c i ≤ 1) (choice : ℕ → Fin m) (pun : ℕ → Fin m → ℕ)
    (hpun0 : ∀ i, pun 0 i = 0)
    (hpun : ∀ (r : ℕ) (i : Fin m), pun r i + (if choice r = i then 1 else 0) ≤ pun (r + 1) i)
    (hgreedy : ∀ (r : ℕ) (j : Fin m),
      c (choice r) * ((pun r (choice r) : ℝ) + 1) ≤ c j * ((pun r j : ℝ) + 1)) :
    ∀ r : ℕ, 0 < r → ∀ i : Fin m, ⌊(r : ℝ) / c i⌋₊ ≤ pun r i := by
  intro r _ i
  have := greedy_gen c hc hsum (fun _ => True) choice pun id hpun0 rfl (fun t => by simp)
    (fun t i => by simpa using hpun t i) (fun t j _ => hgreedy t j) r i
  simpa using this

end CompetitivePaging.Combining

open CompetitivePaging.Combining


theorem solution {m : ℕ} (c : Fin m → ℝ) (hc : ∀ i, 0 < c i)
    (hsum : ∑ i, 1 / c i ≤ 1) (choice : ℕ → Fin m) (pun : ℕ → Fin m → ℕ)
    (hpun0 : ∀ i, pun 0 i = 0)
    (hpun : ∀ (r : ℕ) (i : Fin m), pun r i + (if choice r = i then 1 else 0) ≤ pun (r + 1) i)
    (hgreedy : ∀ (r : ℕ) (j : Fin m),
      c (choice r) * ((pun r (choice r) : ℝ) + 1) ≤ c j * ((pun r j : ℝ) + 1)) :
    ∀ r : ℕ, 0 < r → ∀ i : Fin m, ⌊(r : ℝ) / c i⌋₊ ≤ pun r i := by
  exact greedy_core c hc hsum choice pun hpun0 hpun hgreedy
