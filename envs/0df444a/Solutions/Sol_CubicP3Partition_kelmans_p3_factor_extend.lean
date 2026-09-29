-- Prove2me | solution 1 for CubicP3Partition.kelmans_p3_factor_extend
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T22:01:27.364283+00:00
-- url     : https://prove2.me/submissions/41824ed3-a998-4de1-b071-0eba9d28b5f0

import Definitions.Def_cubic_p3_partition_models

open CubicP3Partition

theorem solution : ∀ (W : Type) [Fintype W], ∀ G : SimpleGraph W,
    ∀ L : P3Path G, Nonempty (P3Factor (eraseP3 G L)) → Nonempty (P3Factor G) := by
  classical
  intro W hW G L hF
  obtain ⟨F⟩ := hF
  set f : Fin (F.blockCount + 1) × Fin 3 → W := fun p =>
    Fin.lastCases (![L.left, L.center, L.right] p.2)
      (fun k : Fin F.blockCount => (F.place (k, p.2)).val) p.1 with hf
  have htri : Function.Injective ![L.left, L.center, L.right] := by
    intro j j' h
    have h1 := L.left_ne_center
    have h2 := L.center_ne_right
    have h3 := L.left_ne_right
    fin_cases j <;> fin_cases j' <;> simp_all [Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons]
  have hinj : Function.Injective f := by
    intro p q hpq
    obtain ⟨i, j⟩ := p
    obtain ⟨i', j'⟩ := q
    obtain ⟨k, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
    · obtain ⟨k', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i'
      · simp only [hf, Fin.lastCases_castSucc] at hpq
        have heq : F.place (k, j) = F.place (k', j') := Subtype.ext hpq
        have h2 := F.place.injective heq
        simp only [Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        rfl
      · simp only [hf, Fin.lastCases_castSucc, Fin.lastCases_last] at hpq
        exfalso
        have hS := (F.place (k, j)).property
        rw [hpq] at hS
        fin_cases j' <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons]
    · obtain ⟨k', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i'
      · simp only [hf, Fin.lastCases_castSucc, Fin.lastCases_last] at hpq
        exfalso
        have hS := (F.place (k', j')).property
        rw [← hpq] at hS
        fin_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons]
      · simp only [hf, Fin.lastCases_last] at hpq
        have hjj : j = j' := htri hpq
        subst hjj
        rfl
  have hsurj : Function.Surjective f := by
    intro w
    by_cases h : w = L.left ∨ w = L.center ∨ w = L.right
    · obtain rfl | rfl | rfl := h
      · exact ⟨(Fin.last _, 0), by simp [hf, Matrix.cons_val_zero]⟩
      · exact ⟨(Fin.last _, 1), by simp [hf, Matrix.cons_val_one]⟩
      · exact ⟨(Fin.last _, 2), by simp [hf, Matrix.cons_val_two, Matrix.head_cons]⟩
    · push_neg at h
      obtain ⟨h1, h2, h3⟩ := h
      obtain ⟨p, hp⟩ := F.place.surjective ⟨w, h1, h2, h3⟩
      obtain ⟨k, j⟩ := p
      refine ⟨(k.castSucc, j), ?_⟩
      simp only [hf, Fin.lastCases_castSucc]
      rw [hp]
  refine ⟨⟨F.blockCount + 1, Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_, ?_⟩⟩
  · intro i
    obtain ⟨k, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
    · simp only [Equiv.coe_ofBijective, hf, Fin.lastCases_castSucc]
      exact F.edge01 k
    · simp only [Equiv.coe_ofBijective, hf, Fin.lastCases_last,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      exact L.edge_left
  · intro i
    obtain ⟨k, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
    · simp only [Equiv.coe_ofBijective, hf, Fin.lastCases_castSucc]
      exact F.edge12 k
    · simp only [Equiv.coe_ofBijective, hf, Fin.lastCases_last,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons]
      exact L.edge_right
