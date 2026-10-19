-- Prove2me | solution 1 for BookProof.ChapterAbelianAtomicCondensation.commutes_atomProj_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:48:31.530277+00:00
-- url     : https://prove2.me/submissions/98634839-8e05-491f-88e5-c4d06a3bfcaa

import Mathlib
import Definitions.Def_ChapterAbelianAtomicCondensation
import Definitions.Def_ChapterAbelianDiagonalCountable
-- Generated from ChapterAbelianAtomicCondensation.lean — theorem BookProof.ChapterAbelianAtomicCondensation.commutes_atomProj_iff
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianAtomicCondensation


open scoped ENNReal

noncomputable section


open BookProof.ChapterAbelianDiagonalCountable
theorem solution (T : Ell2C →L[ℂ] Ell2C) :
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
