-- Prove2me | solution 1 for BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_maximal_eq_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:56:40.573256+00:00
-- url     : https://prove2.me/submissions/07c97686-e8f6-4b3a-82c4-ab7cb9db090a

-- Generated from ChapterAbelianAtomicCondensation.lean — theorem BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_maximal_eq_diagonal
import Mathlib
import Definitions.Def_ChapterAbelianAtomicCondensation
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianAtomicCondensation


open scoped ENNReal

noncomputable section


open BookProof.ChapterAbelianDiagonalCountable

namespace BookProof.ChapterAbelianDiagonalCountable
@[simp] theorem diagOp_apply (d : EllInf) (f : Ell2C) (i : ℕ) :
    ((diagOp d f : Ell2C) : ℕ → ℂ) i = (d : ℕ → ℂ) i * (f : ℕ → ℂ) i := rfl

theorem diagOp_comm (d e : EllInf) :
    (diagOp d).comp (diagOp e) = (diagOp e).comp (diagOp d) := by
  ext f i
  simp [mul_left_comm]

@[simp] theorem norm_atom (i : ℕ) : ‖atom i‖ = 1 := by
  rw [atom, lp.norm_single (by norm_num)]
  simp

theorem diagOp_coordUnit_apply (i : ℕ) (f : Ell2C) (j : ℕ) :
    ((diagOp (coordUnit i) f : Ell2C) : ℕ → ℂ) j = if j = i then (f : ℕ → ℂ) i else 0 := by
  rw [diagOp_apply]
  by_cases h : j = i
  · subst h; simp [coordUnit, lp.single_apply]
  · simp [coordUnit, lp.single_apply, h]

theorem diagOp_coordUnit_eq (i : ℕ) (f : Ell2C) :
    diagOp (coordUnit i) f = (f : ℕ → ℂ) i • atom i := by
  apply lp.ext
  funext j
  rw [diagOp_coordUnit_apply]
  by_cases h : j = i
  · subst h; simp [atom, lp.single_apply]
  · simp [atom, lp.single_apply, h]
end BookProof.ChapterAbelianDiagonalCountable
namespace BookProof.ChapterAbelianAtomicCondensation
theorem atomProj_apply (i : ℕ) (f : Ell2C) : atomProj i f = (f : ℕ → ℂ) i • atom i :=
  diagOp_coordUnit_eq i f

theorem commutes_atomProj_iff (T : Ell2C →L[ℂ] Ell2C) :
    (∀ i : ℕ, T.comp (atomProj i) = (atomProj i).comp T) ↔ ∃ d : EllInf, T = diagOp d := by
  constructor
  · intro hT
    set c : ℕ → ℂ := fun i => ((T (atom i) : Ell2C) : ℕ → ℂ) i with hc
    have hbdd : ∀ i, ‖c i‖ ≤ ‖T‖ := by
      intro i
      calc ‖c i‖ ≤ ‖T (atom i)‖ := lp.norm_apply_le_norm (by simp) _ i
        _ ≤ ‖T‖ * ‖atom i‖ := T.le_opNorm _
        _ = ‖T‖ := by rw [norm_atom, mul_one]
    have hmem : Memℓp c ∞ := by
      refine memℓp_infty ⟨‖T‖, ?_⟩
      rintro x ⟨i, rfl⟩
      exact hbdd i
    refine ⟨⟨c, hmem⟩, ?_⟩
    ext f i
    have hcomm := congrArg (fun S => ((S f : Ell2C) : ℕ → ℂ) i) (hT i)
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at hcomm
    have hleft : T (atomProj i f) = (f : ℕ → ℂ) i • T (atom i) := by
      rw [atomProj_apply, map_smul]
    rw [hleft] at hcomm
    have hright : ((atomProj i (T f) : Ell2C) : ℕ → ℂ) i = ((T f : Ell2C) : ℕ → ℂ) i := by
      rw [atomProj, diagOp_coordUnit_apply]; simp
    rw [hright] at hcomm
    have hval : ((f : ℕ → ℂ) i • T (atom i) : Ell2C) i = (f : ℕ → ℂ) i * c i := rfl
    rw [hval] at hcomm
    rw [← hcomm, diagOp_apply]
    simp [mul_comm]
  · rintro ⟨d, rfl⟩
    intro i
    exact diagOp_comm d (coordUnit i)

theorem atomic_abelian_subset_diagonal {A : Set (Ell2C →L[ℂ] Ell2C)}
    (hA : IsAtomicAbelian A) : A ⊆ Set.range diagOp := by
  intro T hT
  obtain ⟨d, hd⟩ := (commutes_atomProj_iff T).1
    (fun i => hA.abelian T hT (atomProj i) (hA.atoms_mem i))
  exact ⟨d, hd.symm⟩
end BookProof.ChapterAbelianAtomicCondensation

theorem solution {A : Set (Ell2C →L[ℂ] Ell2C)}
    (hA : IsAtomicAbelian A)
    (hmax : ∀ T : Ell2C →L[ℂ] Ell2C, (∀ S ∈ A, T.comp S = S.comp T) → T ∈ A) :
    A = Set.range diagOp := by
  refine Set.Subset.antisymm (atomic_abelian_subset_diagonal hA) ?_
  rintro T ⟨d, rfl⟩
  refine hmax _ fun S hS => ?_
  obtain ⟨e, rfl⟩ := atomic_abelian_subset_diagonal hA hS
  exact diagOp_comm d e

#print axioms solution

