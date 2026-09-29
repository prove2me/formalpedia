-- Prove2me | solution 1 for ConjGrad.Termination.cd_conjugacy_relations
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:17:13.700041+00:00
-- url     : https://prove2.me/submissions/fc41ed04-5905-4d0d-aa9c-c679aacbc6ef

import Mathlib
import Definitions.Def_ConjGrad_Termination_IsCDRun

open Matrix

namespace ConjGrad.Termination

theorem aux_cdcr_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (v w : Fin n → ℝ) : v ⬝ᵥ (A *ᵥ w) = w ⬝ᵥ (A *ᵥ v) := by
  have hT : Aᵀ = A := by
    have h := hA.1
    unfold Matrix.IsHermitian at h
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hT]

theorem aux_cdcr_res {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n → ℝ) (x r p : ℕ → Fin n → ℝ) (hcd : IsCDRun A k x r p) (i : ℕ) (m : ℕ) :
    p m ⬝ᵥ r (i + 1) = p m ⬝ᵥ r i
      - ((p i ⬝ᵥ r i) / (p i ⬝ᵥ (A *ᵥ p i))) * (p m ⬝ᵥ (A *ᵥ p i)) := by
  have hr : r (i + 1) = r i - ((p i ⬝ᵥ r i) / (p i ⬝ᵥ (A *ᵥ p i))) • (A *ᵥ p i) := by
    rw [hcd.residual (i + 1), hcd.step i, mulVec_add, mulVec_smul, sub_add_eq_sub_sub,
      ← hcd.residual i]
  rw [hr, dotProduct_sub, dotProduct_smul, smul_eq_mul]

theorem aux_cdcr_conj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k : Fin n → ℝ) (x r p : ℕ → Fin n → ℝ) (hcd : IsCDRun A k x r p) :
    ∀ i j, i ≠ j → p i ⬝ᵥ (A *ᵥ p j) = 0 := by
  have key : ∀ i j, j < i → p i ⬝ᵥ (A *ᵥ p j) = 0 := by
    intro i j hji
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    exact hcd.conj i' j (by omega)
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · rw [aux_cdcr_symm A hA]
    exact key j i h
  · exact key i j h

theorem aux_cdcr_self {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k : Fin n → ℝ) (x r p : ℕ → Fin n → ℝ) (hcd : IsCDRun A k x r p) (i : ℕ) :
    p i ⬝ᵥ r (i + 1) = 0 := by
  rw [aux_cdcr_res A k x r p hcd i i]
  by_cases h0 : p i ⬝ᵥ (A *ᵥ p i) = 0
  · have hp : p i = 0 := by
      by_contra hne
      have := hA.dotProduct_mulVec_pos hne
      simp only [star_trivial] at this
      linarith
    simp [hp]
  · field_simp
    ring

end ConjGrad.Termination

open ConjGrad.Termination
open Matrix

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k : Fin n → ℝ) (x r p : ℕ → Fin n → ℝ) (hcd : IsCDRun A k x r p) :
    (∀ i j, i ≠ j → p i ⬝ᵥ (A *ᵥ p j) = 0) ∧
    (∀ i j, j < i → p j ⬝ᵥ r i = 0) ∧
    (∀ i j, j ≤ i → p i ⬝ᵥ r j = p i ⬝ᵥ r 0) ∧
    (∀ i, x (i + 1) = x i + ((p i ⬝ᵥ r 0) / (p i ⬝ᵥ (A *ᵥ p i))) • p i) := by
  have hconj := aux_cdcr_conj A hA k x r p hcd
  have h2 : ∀ i j, j < i → p j ⬝ᵥ r i = 0 := by
    intro i j hji
    induction i with
    | zero => omega
    | succ i ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hji with h | h
      · rw [aux_cdcr_res A k x r p hcd i j, ih h, hconj j i (by omega)]
        ring
      · subst h
        exact aux_cdcr_self A hA k x r p hcd j
  have h3 : ∀ i j, j ≤ i → p i ⬝ᵥ r j = p i ⬝ᵥ r 0 := by
    intro i j hji
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [aux_cdcr_res A k x r p hcd j i, ih (by omega), hconj i j (by omega)]
      ring
  refine ⟨hconj, h2, h3, ?_⟩
  intro i
  rw [hcd.step i, h3 i i le_rfl]
