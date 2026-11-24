-- Prove2me | solution 1 for GMRDiversity.lemma_2_step_i_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:11:18.53544+00:00
-- url     : https://prove2.me/submissions/182177d6-0642-4b0b-a022-9bbf7749baf5

import Mathlib
import Definitions.Def_GMRDiversity_Nondeg

set_option autoImplicit false

open GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- The dot pairing as a Mathlib bilinear form (the identity matrix form). -/
private noncomputable abbrev dotB (n : ℕ) : LinearMap.BilinForm (ZMod 2) (V n) :=
  Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) (ZMod 2))

private lemma dotB_apply {n : ℕ} (x y : V n) : dotB n x y = dot x y := by
  simp [dotB, Matrix.toBilin'_apply', dot, dotProduct]

private lemma dot_comm' {n : ℕ} (x y : V n) : dot x y = dot y x := by
  simp only [dot]; exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

private lemma orth_eq {n : ℕ} (W : Submodule (ZMod 2) (V n)) :
    orth W = (dotB n).orthogonal W := by
  ext y
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, dotB_apply]
  constructor
  · intro h x hx; exact h x hx
  · intro h x hx; exact h x hx

private lemma dotB_nondeg (n : ℕ) : (dotB n).Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _ (by simp)

private lemma dotB_refl (n : ℕ) : (dotB n).IsRefl := by
  intro x y h
  rw [dotB_apply] at h ⊢; rw [dot_comm']; exact h

private lemma finrank_orth {n : ℕ} (W : Submodule (ZMod 2) (V n)) :
    Module.finrank (ZMod 2) (orth W) = n - Module.finrank (ZMod 2) W := by
  rw [orth_eq, LinearMap.BilinForm.finrank_orthogonal (dotB_nondeg n)]
  simp

private lemma orth_orth {n : ℕ} (W : Submodule (ZMod 2) (V n)) : orth (orth W) = W := by
  rw [orth_eq, orth_eq]
  exact LinearMap.BilinForm.orthogonal_orthogonal (dotB_nondeg n) (dotB_refl n) W

theorem solution {n : ℕ} (S : Submodule (ZMod 2) (V n)) (hS : Nondeg S) :
    IsCompl S (orth S) ∧ orth (orth S) = S ∧ Nondeg (orth S) ∧
    (∀ h ∈ orth S, Nat.card {a : V n // a - h ∈ S} = Nat.card S) ∧
    (∀ h h' : V n, dot (h + h') (h + h') = dot h h + dot h' h') := by
  refine ⟨?_, orth_orth S, ?_, ?_, ?_⟩
  · rw [orth_eq]
    exact (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint (dotB_refl n)).mpr
      (by rw [← orth_eq, disjoint_iff]; exact hS)
  · unfold Nondeg at hS ⊢
    rw [orth_orth, inf_comm]; exact hS
  · intro h _
    exact Nat.card_congr
      { toFun := fun a => ⟨a.1 - h, a.2⟩
        invFun := fun s => ⟨s.1 + h, by simp⟩
        left_inv := fun a => by ext; simp
        right_inv := fun s => by ext; simp }
  · intro h h'
    have key : ∀ a b : ZMod 2, (a + b) * (a + b) = a * a + b * b := by decide
    simp only [dot, Pi.add_apply, key, Finset.sum_add_distrib]
