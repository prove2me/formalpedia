-- Prove2me | solution 1 for BookProof.ChapterA3x.projMixed_three_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:53:18.610983+00:00
-- url     : https://prove2.me/submissions/192ec2f1-e65a-4202-b89b-49c5c772b33c

-- Generated from ChapterA3x.lean — theorem BookProof.ChapterA3x.projMixed_three_ne_zero
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3p
import Mathlib
import Definitions.Def_ChapterA3x
import Definitions.Def_ChapterA3l
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3o
open BookProof.ChapterA3n
open BookProof.ChapterA3o
open BookProof.ChapterA3x


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open BookProof.ChapterA3p

private theorem projSym_apply {N : ℕ} (a b : Idx N) :
    projSym N a b = (Nat.factorial N : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin N),
      (if b = a ∘ σ then (1 : ℂ) else 0) := by
  simp [projSym, permMat, Matrix.sum_apply]

private theorem projAnti_apply {N : ℕ} (a b : Idx N) :
    projAnti N a b = (Nat.factorial N : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin N),
      signC σ * (if b = a ∘ σ then (1 : ℂ) else 0) := by
  simp [projAnti, permMat, Matrix.sum_apply, signC]

theorem solution : projMixed 3 ≠ 0 := by
  intro h
  set a : Idx 3 := (![0, 0, 1] : Fin 3 → Fin 4) with hadef
  have ha : (projMixed 3) a a = 0 := by rw [h]; simp
  have hsym : ∑ σ : Equiv.Perm (Fin 3), (if a = a ∘ σ then (1 : ℂ) else 0) = 2 := by
    have hZ : ∑ σ : Equiv.Perm (Fin 3), (if a = a ∘ σ then (1 : ℤ) else 0) = 2 := by decide
    calc ∑ σ : Equiv.Perm (Fin 3), (if a = a ∘ σ then (1 : ℂ) else 0)
        = ((∑ σ : Equiv.Perm (Fin 3), (if a = a ∘ σ then (1 : ℤ) else 0) : ℤ) : ℂ) := by
          push_cast
          exact Finset.sum_congr rfl fun σ _ => by split <;> simp
      _ = 2 := by rw [hZ]; norm_num
  have hanti : ∑ σ : Equiv.Perm (Fin 3), signC σ * (if a = a ∘ σ then (1 : ℂ) else 0) = 0 := by
    have hZ : ∑ σ : Equiv.Perm (Fin 3),
        ((Equiv.Perm.sign σ : ℤ) * (if a = a ∘ σ then (1 : ℤ) else 0)) = 0 := by decide
    calc ∑ σ : Equiv.Perm (Fin 3), signC σ * (if a = a ∘ σ then (1 : ℂ) else 0)
        = ((∑ σ : Equiv.Perm (Fin 3),
            ((Equiv.Perm.sign σ : ℤ) * (if a = a ∘ σ then (1 : ℤ) else 0)) : ℤ) : ℂ) := by
          push_cast [signC]
          exact Finset.sum_congr rfl fun σ _ => by split <;> simp
      _ = 0 := by rw [hZ]; norm_num
  rw [projMixed] at ha
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, projSym_apply, projAnti_apply,
    hsym, hanti] at ha
  norm_num [Nat.factorial] at ha

#print axioms solution
