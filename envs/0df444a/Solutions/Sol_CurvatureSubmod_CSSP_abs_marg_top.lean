-- Prove2me | solution 1 for CurvatureSubmod.CSSP.abs_marg_top
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:15:48.851236+00:00
-- url     : https://prove2.me/submissions/7158035a-838f-4d39-a44c-50c413c90e68

import Mathlib
import Definitions.Def_CurvatureSubmod_CSSP_Setting
set_option autoImplicit false
open CurvatureSubmod.CSSP

theorem proj_self_of_mem {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) {S : Finset (Fin n)}
    {j : Fin n} (hj : j ∈ S) : proj c S (c j) = c j := by
  unfold proj
  rw [Submodule.starProjection_eq_self_iff]
  exact Submodule.subset_span ⟨j, hj, rfl⟩

theorem solution {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (i : Fin n) :
    |marg (fA c) (Finset.univ.erase i) i| =
      ‖c i - proj c (Finset.univ.erase i) (c i)‖ ^ 2 := by
  unfold marg
  rw [Finset.insert_erase (Finset.mem_univ i)]
  have h1 : fA c Finset.univ = 0 := by
    unfold fA
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [proj_self_of_mem c (Finset.mem_univ j)]
    simp
  have h2 : fA c (Finset.univ.erase i) = ‖c i - proj c (Finset.univ.erase i) (c i)‖ ^ 2 := by
    unfold fA
    refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rw [proj_self_of_mem c (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)]
    simp
  rw [h1, h2, zero_sub, abs_neg]
  exact abs_of_nonneg (sq_nonneg _)

