-- Prove2me | solution 1 for EllipticRootFinding.Online.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-19T16:22:13.139659+00:00
-- url     : https://prove2.me/submissions/f3e2a4fb-f235-463b-8d8a-aa20c4c90380

import Mathlib

open Polynomial

theorem solution (F : Type) [Field F] [Fintype F] (hchar : 3 < ringChar F)
    (f h : F[X]) (hsplit : f.Splits) (hsep : f.Separable) :
    ((∀ α : F, f.IsRoot α → IsSquare (h.eval α)) →
      ∃ v : F[X], v.degree < f.degree ∧ f ∣ v ^ 2 - h) ∧
    (∀ β : F, ¬ IsSquare β →
      (∀ α : F, f.IsRoot α → ¬ IsSquare (h.eval α)) →
      ∃ v : F[X], v.degree < f.degree ∧ f ∣ C β * v ^ 2 - h) := by
  classical
  have hf0 : f ≠ 0 := hsep.ne_zero
  have hnodup : f.roots.Nodup := Polynomial.nodup_roots hsep
  have hcard : f.roots.toFinset.card = f.natDegree := by
    rw [Multiset.toFinset_card_of_nodup hnodup, hsplit.natDegree_eq_card_roots]
  have hchar2 : ringChar F ≠ 2 := by omega
  -- Lagrange interpolation machinery: if a polynomial `C c * r^2` agrees with `h` at all
  -- roots of `f`, then there is `v` with `v.eval = r` at those roots, and `f ∣ C c * v^2 - h`.
  have main : ∀ (c : F) (r : F → F),
      (∀ α ∈ f.roots.toFinset, c * (r α * r α) = h.eval α) →
      ∃ v : F[X], v.degree < f.degree ∧ f ∣ C c * v ^ 2 - h := by
    intro c r hr
    refine ⟨Lagrange.interpolate f.roots.toFinset id r, ?_, ?_⟩
    · have hvs : Set.InjOn id (↑f.roots.toFinset : Set F) := fun _ _ _ _ h => h
      calc (Lagrange.interpolate f.roots.toFinset id r).degree
          < ↑(f.roots.toFinset.card) := Lagrange.degree_interpolate_lt r hvs
        _ = ↑f.natDegree := by rw [hcard]
        _ = f.degree := (Polynomial.degree_eq_natDegree hf0).symm
    · set g : F[X] := C c * Lagrange.interpolate f.roots.toFinset id r ^ 2 - h with hg
      by_cases hg0 : g = 0
      · rw [hg0]; exact dvd_zero f
      · refine hsplit.dvd_of_roots_le_roots hf0 ?_
        rw [Multiset.le_iff_count]
        intro a
        by_cases ha : a ∈ f.roots
        · rw [Multiset.count_eq_one_of_mem hnodup ha]
          refine Multiset.count_pos.mpr ?_
          rw [Polynomial.mem_roots hg0]
          have hmem : a ∈ f.roots.toFinset := Multiset.mem_toFinset.mpr ha
          have hv : (Lagrange.interpolate f.roots.toFinset id r).eval a = r a := by
            have h := Lagrange.eval_interpolate_at_node (s := f.roots.toFinset) (v := id)
              (r := r) (i := a) (fun _ _ _ _ h => h) hmem
            simpa using h
          have hev : g.eval a = 0 := by
            rw [hg]
            simp only [eval_sub, eval_mul, eval_pow, eval_C]
            rw [hv, pow_two, hr a hmem]
            ring
          exact hev
        · rw [Multiset.count_eq_zero_of_notMem ha]
          exact Nat.zero_le _
  constructor
  · intro hsq
    have sq_wit : ∀ α : F, f.IsRoot α → ∃ x : F, h.eval α = x * x := by
      intro α hα
      obtain ⟨w, hw⟩ := hsq α hα
      exact ⟨w, hw⟩
    let r : F → F := fun α => if hα : f.IsRoot α then Classical.choose (sq_wit α hα) else 0
    have hr : ∀ α ∈ f.roots.toFinset, (1 : F) * (r α * r α) = h.eval α := by
      intro α hα
      have hroot : f.IsRoot α := (Polynomial.mem_roots hf0).mp (Multiset.mem_toFinset.mp hα)
      have hspec : h.eval α = r α * r α := by
        simp only [r, dif_pos hroot]
        exact Classical.choose_spec (sq_wit α hroot)
      rw [one_mul, hspec]
    simpa using main 1 r hr
  · intro β hβns hhns
    have hβ0 : β ≠ 0 := by
      rintro rfl
      exact hβns ⟨0, by simp⟩
    -- the quotient of two non-squares in a finite field of odd characteristic is a square
    have hdiv_sq : ∀ α : F, f.IsRoot α → IsSquare (h.eval α / β) := by
      intro α hroot
      have hha : h.eval α ≠ 0 := by
        rintro h0
        exact hhns α hroot ⟨0, by simp [h0]⟩
      have hne : h.eval α / β ≠ 0 := div_ne_zero hha hβ0
      rw [FiniteField.isSquare_iff hchar2 hne, div_pow]
      have hpa : h.eval α ^ (Fintype.card F / 2) = -1 := by
        rcases FiniteField.pow_dichotomy hchar2 hha with h1 | h1
        · exact absurd ((FiniteField.isSquare_iff hchar2 hha).mpr h1) (hhns α hroot)
        · exact h1
      have hpb : β ^ (Fintype.card F / 2) = -1 := by
        rcases FiniteField.pow_dichotomy hchar2 hβ0 with h1 | h1
        · exact absurd ((FiniteField.isSquare_iff hchar2 hβ0).mpr h1) hβns
        · exact h1
      rw [hpa, hpb]
      norm_num
    have hdiv_wit : ∀ α : F, f.IsRoot α → ∃ x : F, h.eval α / β = x * x := by
      intro α hα
      obtain ⟨w, hw⟩ := hdiv_sq α hα
      exact ⟨w, hw⟩
    let r : F → F := fun α => if hα : f.IsRoot α then Classical.choose (hdiv_wit α hα) else 0
    have hr : ∀ α ∈ f.roots.toFinset, β * (r α * r α) = h.eval α := by
      intro α hα
      have hroot : f.IsRoot α := (Polynomial.mem_roots hf0).mp (Multiset.mem_toFinset.mp hα)
      have hspec : h.eval α / β = r α * r α := by
        simp only [r, dif_pos hroot]
        exact Classical.choose_spec (hdiv_wit α hroot)
      rw [← hspec]
      field_simp
    simpa using main β r hr
