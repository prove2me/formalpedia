-- Prove2me | solution 1 for BookProof.NavierStokesFlow.CanonicalVector.canH_crd
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T18:03:52.090417+00:00
-- url     : https://prove2.me/submissions/664f4986-6038-4f9d-ba2e-bc459b8237d9

import Mathlib
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.CanonicalVector
open scoped ENNReal
open LpNat BookProof.FarisLavine IkebeKato ThreeComponent ShiftHamiltonian SignedShift

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem crd_add (x y : lpFiniteModes Vel) : crd (x + y) = crd x + crd y := rfl
theorem crd_smul (a : ℂ) (x : lpFiniteModes Vel) : crd (a • x) = a • crd x := rfl
theorem crd_sum {ι : Type*} (s : Finset ι) (f : ι → lpFiniteModes Vel) :
    crd (∑ i ∈ s, f i) = ∑ i ∈ s, crd (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, crd_add, ih]
theorem crd_ann (i : Fin 3) (x : lpFiniteModes Vel) : crd (ann i x) = aFun i (crd x) := rfl
theorem crd_cre (i : Fin 3) (x : lpFiniteModes Vel) : crd (cre i x) = cFun i (crd x) := rfl
theorem crd_pos (i : Fin 3) (x : lpFiniteModes Vel) : crd (pos i x) = pFun i (crd x) := by
  simp only [pos, LinearMap.smul_apply, LinearMap.add_apply, crd_smul, crd_add, crd_ann, crd_cre, pFun]
theorem crd_mom (i : Fin 3) (x : lpFiniteModes Vel) : crd (mom i x) = mFun i (crd x) := by
  simp only [mom, LinearMap.smul_apply, LinearMap.sub_apply, crd_smul, mFun]
  rfl
theorem lm_sum_apply {ι : Type*} (s : Finset ι) (f : ι → lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel) (x : lpFiniteModes Vel) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := LinearMap.sum_apply s f x
theorem crd_fieldV (i : Fin 3) (x : lpFiniteModes Vel) : crd (fieldV A c i x) = vFun A c i (crd x) := by
  simp only [fieldV, vFun, lm_sum_apply, LinearMap.add_apply, Finset.sum_apply,
    LinearMap.smul_apply, LinearMap.id_apply, crd_add, crd_sum, crd_smul, crd_pos]

theorem canH_crd' (x : lpFiniteModes Vel) (γ : Vel) :
    crd (canH A c x) γ = canFun A c (crd x) γ := by
  simp only [canH, canFun, lm_sum_apply, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.comp_apply, crd_sum, crd_smul, crd_add, crd_mom, crd_fieldV]
  simp [Finset.sum_apply, smul_eq_mul, crd_sum, crd_add, crd_smul, crd_mom, crd_fieldV]

theorem solution (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) (x : lpFiniteModes Vel) (γ : Vel) :
    crd (canH A c x) γ = canFun A c (crd x) γ :=
  canH_crd' A c x γ
