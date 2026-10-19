-- Prove2me | solution 2 for BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_subset_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:49:00.966753+00:00
-- url     : https://prove2.me/submissions/fe9666d2-54d4-4034-9d93-6d26bf083f9d

import Mathlib
import Definitions.Def_ChapterAbelianAtomicCondensation
import Definitions.Def_ChapterAbelianDiagonalCountable
-- Generated from ChapterAbelianAtomicCondensation.lean — theorem BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_subset_diagonal
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianAtomicCondensation


open scoped ENNReal

noncomputable section


open BookProof.ChapterAbelianDiagonalCountable
theorem cap_aux (T : Ell2C →L[ℂ] Ell2C) :
    (∀ i : ℕ, T.comp (atomProj i) = (atomProj i).comp T) ↔ ∃ d : EllInf, T = diagOp d := by
  have hdiag : ∀ (d : EllInf) (f : Ell2C) (k : ℕ), ((diagOp d f : Ell2C) : ℕ → ℂ) k =
      (d : ℕ → ℂ) k * (f : ℕ → ℂ) k := fun d f k => rfl
  have hcu : ∀ i k : ℕ, ((coordUnit i : EllInf) : ℕ → ℂ) k = if k = i then 1 else 0 := by
    intro i k
    simp only [coordUnit, lp.single_apply, Pi.single_apply]
  have hP : ∀ i (f : Ell2C), atomProj i f = lp.single (E := fun _ : ℕ => ℂ) 2 i ((f : ℕ → ℂ) i) := by
    intro i f
    ext k
    simp only [atomProj, hdiag, hcu, lp.single_apply, Pi.single_apply]
    split_ifs with h
    · subst h; simp
    · simp
  constructor
  · intro h
    have hbd : ∀ i, ‖((T (lp.single (E := fun _ : ℕ => ℂ) 2 i (1 : ℂ)) : Ell2C) : ℕ → ℂ) i‖ ≤ ‖T‖ := by
      intro i
      calc _ ≤ ‖T (lp.single (E := fun _ : ℕ => ℂ) 2 i (1 : ℂ))‖ := lp.norm_apply_le_norm (by norm_num) _ i
        _ ≤ ‖T‖ * ‖lp.single (E := fun _ : ℕ => ℂ) 2 i (1 : ℂ)‖ := T.le_opNorm _
        _ = ‖T‖ := by rw [lp.norm_single (by norm_num), norm_one, mul_one]
    refine ⟨⟨fun i => ((T (lp.single (E := fun _ : ℕ => ℂ) 2 i (1 : ℂ)) : Ell2C) : ℕ → ℂ) i,
      memℓp_infty ⟨‖T‖, by rintro _ ⟨i, rfl⟩; exact hbd i⟩⟩, ?_⟩
    ext x i
    rw [hdiag]
    have h1 : ((T x : Ell2C) : ℕ → ℂ) i = ((atomProj i (T x) : Ell2C) : ℕ → ℂ) i := by
      rw [hP]; simp [lp.single_apply]
    have h2 := congrArg (fun S : Ell2C →L[ℂ] Ell2C => ((S x : Ell2C) : ℕ → ℂ) i) (h i)
    simp only [ContinuousLinearMap.comp_apply] at h2
    rw [h1, ← h2, hP, show lp.single (E := fun _ : ℕ => ℂ) 2 i ((x : ℕ → ℂ) i) = (x : ℕ → ℂ) i • lp.single (E := fun _ : ℕ => ℂ) 2 i (1 : ℂ) by
      rw [← lp.single_smul, smul_eq_mul, mul_one], map_smul]
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring
  · rintro ⟨d, rfl⟩ i
    ext x k
    simp only [ContinuousLinearMap.comp_apply, atomProj, hdiag]
    ring


theorem solution {A : Set (Ell2C →L[ℂ] Ell2C)}
    (hA : IsAtomicAbelian A) : A ⊆ Set.range diagOp := by
  intro T hT
  obtain ⟨d, hd⟩ := (cap_aux T).1 (fun i => (hA.abelian T hT _ (hA.atoms_mem i)))
  exact ⟨d, hd.symm⟩
