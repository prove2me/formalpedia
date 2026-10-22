-- Prove2me | solution 1 for DissipativePrep.Unique.monomial
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T22:07:35.928089+00:00
-- url     : https://prove2.me/submissions/6fbce3f8-7acd-46e6-9ce9-ca61e89012de

import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16

namespace DPMonoAux
open DissipativePrep.Unique

lemma lowerQ_mulVec {n : ℕ} (k : Fin n) (f : Qubits n → ℂ) (x : Qubits n) (hx : x k = false) :
    (lowerQ k *ᵥ f) x = f (Function.update x k true) := by
  simp only [Matrix.mulVec, dotProduct, lowerQ, Matrix.of_apply]
  rw [Finset.sum_eq_single (Function.update x k true)]
  · have : Function.update (Function.update x k true) k false = x := by
      rw [Function.update_idem]; exact Function.update_eq_self_iff.mpr hx.symm
    simp [this]
  · intro y _ hy
    rw [if_neg, zero_mul]
    rintro ⟨h1, h2⟩
    apply hy
    rw [h2, Function.update_idem]
    exact (Function.update_eq_self_iff.mpr h1.symm).symm
  · simp

lemma prod_lowerQ_mulVec {n : ℕ} (w : List (Fin n)) (hw : w.Nodup) (f : Qubits n → ℂ)
    (x : Qubits n) (hx : ∀ k ∈ w, x k = false) :
    ((w.map lowerQ).prod *ᵥ f) x = f (fun i => if i ∈ w then true else x i) := by
  induction w generalizing x with
  | nil => simp
  | cons a w ih =>
    rw [List.nodup_cons] at hw
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec,
      lowerQ_mulVec a _ x (hx a (by simp))]
    rw [ih hw.2 (Function.update x a true)]
    · congr 1
      funext i
      by_cases hi : i = a
      · subst hi; simp
      · simp [hi, Function.update_of_ne hi]
    · intro k hk
      have hka : k ≠ a := fun h => hw.1 (h ▸ hk)
      rw [Function.update_of_ne hka]
      exact hx k (by simp [hk])

end DPMonoAux

open DissipativePrep.Unique DPMonoAux

theorem solution {n : ℕ} (χ : EuclideanSpace ℂ (Fin (2 ^ n))) (hχ : χ ≠ 0)
    (horth : inner ℂ (ket (0 : Fin (2 ^ n))) χ = 0) :
    ∃ w : List (Fin n), inner ℂ (ket (0 : Fin (2 ^ n))) (act (w.map lower).prod χ) ≠ 0 := by
  set e := bitsEquivFin n
  have he0 : e.symm 0 = fun _ => false := by
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    rw [bitsEquivFin_apply]
    simp [bitsToNat]
  obtain ⟨i, hi⟩ : ∃ i, χ i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hχ
    ext j
    simp [h j]
  set y := e.symm i
  refine ⟨(Finset.univ.filter (fun k => y k = true)).toList, ?_⟩
  set w := (Finset.univ.filter (fun k => y k = true)).toList
  have hprod : (w.map lower).prod = Matrix.reindex e e ((w.map lowerQ).prod) := by
    rw [← Matrix.reindexAlgEquiv_apply ℂ ℂ, map_list_prod, List.map_map]
    rfl
  rw [ket, EuclideanSpace.inner_single_left]
  simp only [map_one, one_mul, act]
  rw [hprod, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_apply, Equiv.symm_symm]
  rw [he0, prod_lowerQ_mulVec w (Finset.nodup_toList _) _ _ (fun _ _ => rfl)]
  have : (fun k => if k ∈ w then true else false) = y := by
    funext k
    simp only [w, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
    cases y k <;> simp
  rw [this]
  simpa [y] using hi

