-- Prove2me | solution 1 for CosetTreeSVP.SVP.lemma_2_7
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-23T23:29:19.153946+00:00
-- url     : https://prove2.me/submissions/661c5f3b-84ed-4f1e-9ca9-2f4d4497816a

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Definitions.Def_CosetTreeSVP_SVP_Basics

open MeasureTheory Filter Topology
open scoped ENNReal
open CosetTreeSVP.SVP

theorem solution {n : ℕ} (x y : E n) (hy : y ≠ 0) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hxy : ‖x - y‖ ≤ ε * ‖y‖) :
    x ≠ 0 ∧ ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2 * ε / (1 - ε) := by
  have hb : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hx : x ≠ 0 := by
    rintro rfl
    rw [zero_sub, norm_neg] at hxy
    nlinarith
  refine ⟨hx, ?_⟩
  have ha : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hd : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
  have key : ‖x‖⁻¹ • x - ‖y‖⁻¹ • y = (‖x‖⁻¹ - ‖y‖⁻¹) • x + ‖y‖⁻¹ • (x - y) := by
    rw [smul_sub, sub_smul]; abel
  have hxne := ha.ne'
  have hyne := hb.ne'
  have h1 : ‖(‖x‖⁻¹ - ‖y‖⁻¹) • x‖ ≤ ε := by
    rw [norm_smul, Real.norm_eq_abs]
    have e1 : (‖x‖⁻¹ - ‖y‖⁻¹) * ‖x‖ = (‖y‖ - ‖x‖) / ‖y‖ := by
      field_simp
    calc |‖x‖⁻¹ - ‖y‖⁻¹| * ‖x‖ = |(‖x‖⁻¹ - ‖y‖⁻¹) * ‖x‖| := by rw [abs_mul, abs_of_pos ha]
      _ = |‖y‖ - ‖x‖| / ‖y‖ := by rw [e1, abs_div, abs_of_pos hb]
      _ ≤ ε := by rw [div_le_iff₀ hb, abs_sub_comm]; linarith
  have h2 : ‖‖y‖⁻¹ • (x - y)‖ ≤ ε := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hb]; linarith
  have h3 : 2 * ε ≤ 2 * ε / (1 - ε) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  calc ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ = ‖(‖x‖⁻¹ - ‖y‖⁻¹) • x + ‖y‖⁻¹ • (x - y)‖ := by rw [key]
    _ ≤ ‖(‖x‖⁻¹ - ‖y‖⁻¹) • x‖ + ‖‖y‖⁻¹ • (x - y)‖ := norm_add_le _ _
    _ ≤ 2 * ε := by linarith
    _ ≤ 2 * ε / (1 - ε) := h3
