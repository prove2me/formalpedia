-- Prove2me | solution 1 for CurvatureSubmod.CSSP.exists_unit_small
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:16:04.269033+00:00
-- url     : https://prove2.me/submissions/9a5da26e-489b-4f25-b5f8-a85a78d5ecd8

import Mathlib
import Definitions.Def_CurvatureSubmod_CSSP_Setting
set_option autoImplicit false
open CurvatureSubmod.CSSP

theorem proj_self_of_mem {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) {S : Finset (Fin n)}
    {j : Fin n} (hj : j ∈ S) : proj c S (c j) = c j := by
  unfold proj
  rw [Submodule.starProjection_eq_self_iff]
  exact Submodule.subset_span ⟨j, hj, rfl⟩

theorem sol_abs_marg_top {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (i : Fin n) :
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

theorem exists_coeff {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (S : Finset (Fin n))
    (y : EuclideanSpace ℝ (Fin m)) (hy : y ∈ colSpan c S) :
    ∃ a : Fin n → ℝ, (∀ j, j ∉ S → a j = 0) ∧ ∑ j, a j • c j = y := by
  unfold colSpan at hy
  rw [Finsupp.mem_span_image_iff_linearCombination ℝ] at hy
  obtain ⟨l, hl, hly⟩ := hy
  refine ⟨fun j => l j, ?_, ?_⟩
  · intro j hj
    exact (Finsupp.mem_supported' ℝ l).1 hl j (by simpa using hj)
  · rw [← hly, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]

theorem applyA_smul {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : applyA c (r • x) = r • applyA c x := by
  simp [applyA, Finset.smul_sum, smul_smul]

theorem solution {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (i : Fin n) :
    ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 ∧
      ‖applyA c x‖ ≤ Real.sqrt |marg (fA c) (Finset.univ.erase i) i| := by
  rw [sol_abs_marg_top, Real.sqrt_sq (norm_nonneg _)]
  obtain ⟨a, ha0, hay⟩ := exists_coeff c (Finset.univ.erase i) (proj c (Finset.univ.erase i) (c i))
    (Submodule.starProjection_apply_mem _ _)
  set x0 : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1 - WithLp.toLp 2 a with hx0
  have hai : a i = 0 := ha0 i (by simp)
  have hx0i : x0 i = 1 := by simp [hx0, hai]
  have hApp : applyA c x0 = c i - proj c (Finset.univ.erase i) (c i) := by
    rw [← hay]
    simp [applyA, hx0, sub_smul, Finset.sum_sub_distrib, EuclideanSpace.single_apply]
  have hn : 1 ≤ ‖x0‖ := by
    have := PiLp.norm_apply_le x0 i
    rw [hx0i] at this
    simpa using this
  refine ⟨(‖x0‖⁻¹) • x0, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (by linarith)
  · rw [applyA_smul, norm_smul, hApp, norm_inv, norm_norm]
    calc ‖x0‖⁻¹ * ‖c i - proj c (Finset.univ.erase i) (c i)‖
        ≤ 1 * ‖c i - proj c (Finset.univ.erase i) (c i)‖ := by
          gcongr
          exact inv_le_one_of_one_le₀ hn
      _ = _ := one_mul _

