-- Prove2me | solution 1 for BarvinokCount.ShortFormula.exists_moment_vector_not_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:25:27.332626+00:00
-- url     : https://prove2.me/submissions/279c3402-43e2-4077-851e-b13299531785

import Mathlib

open Polynomial in
theorem ccc7278e_aux (d m : ℕ) (u : Fin m → Fin d → ℚ)
    (hu : ∀ i, u i ≠ 0) :
    ∃ t ∈ Finset.range (m * (d - 1) + 1),
      ∀ i, (fun l : Fin d => (t : ℚ) ^ (l : ℕ)) ⬝ᵥ u i ≠ 0 := by
  classical
  let p : Fin m → ℚ[X] := fun i => ∑ l : Fin d, C (u i l) * X ^ (l : ℕ)
  have hp0 : ∀ i, p i ≠ 0 := by
    intro i h
    obtain ⟨l, hl⟩ := Function.ne_iff.mp (hu i)
    apply hl
    have := congrArg (fun q : ℚ[X] => q.coeff (l : ℕ)) h
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single l] at this
    · simpa using this
    · intro b _ hb
      rw [if_neg]
      intro h'
      exact hb (Fin.ext h'.symm)
    · simp
  have hdeg : ∀ i, (p i).natDegree ≤ d - 1 := by
    intro i
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro l _
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    have := l.isLt
    omega
  have heval : ∀ i (t : ℚ), (fun l : Fin d => t ^ (l : ℕ)) ⬝ᵥ u i = (p i).eval t := by
    intro i t
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, dotProduct]
    exact Finset.sum_congr rfl (fun l _ => mul_comm _ _)
  let B : Finset ℚ := Finset.univ.biUnion (fun i => (p i).roots.toFinset)
  have hB : B.card ≤ m * (d - 1) := by
    calc B.card ≤ ∑ i, ((p i).roots.toFinset).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin m, (d - 1) := by
        apply Finset.sum_le_sum
        intro i _
        exact (Multiset.toFinset_card_le _).trans
          ((Polynomial.card_roots' _).trans (hdeg i))
      _ = m * (d - 1) := by simp
  let T : Finset ℚ := (Finset.range (m * (d - 1) + 1)).image (fun n : ℕ => (n : ℚ))
  have hT : T.card = m * (d - 1) + 1 := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  obtain ⟨x, hxT, hxB⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := B) (t := T)
    (by omega)
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hxT
  refine ⟨n, hn, fun i h => hxB ?_⟩
  rw [heval] at h
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hp0 i)).mpr h)⟩

theorem solution (d m : ℕ) (u : Fin m → Fin d → ℚ)
    (hu : ∀ i, u i ≠ 0) :
    ∃ t ∈ Finset.range (m * (d - 1) + 1),
      ∀ i, (fun l : Fin d => (t : ℚ) ^ (l : ℕ)) ⬝ᵥ u i ≠ 0 := by
  exact ccc7278e_aux d m u hu
