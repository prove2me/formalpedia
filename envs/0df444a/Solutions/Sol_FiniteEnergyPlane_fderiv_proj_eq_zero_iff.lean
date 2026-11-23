-- Prove2me | solution 1 for FiniteEnergyPlane.fderiv_proj_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-23T21:26:29.015414+00:00
-- url     : https://prove2.me/submissions/ce738cf3-3d97-4bfd-aaa2-391e5d52c3eb

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib
import Definitions.Def_FiniteEnergyPlane_OpenBook
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
import Theorems.Thm_FiniteEnergyPlane_proj_aCoord_exp_smul
import Theorems.Thm_FiniteEnergyPlane_injective_fderiv_aCoord_proj_comp_iff



/-! Transversality of a curve of leaves to a family of embedded fast planes. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The kernel of the derivative of the radial projection is the radial line. -/
theorem fderiv_proj_eq_zero_iff_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (y : V n) (hy : y ≠ 0) (v : V n) :
    fderiv ℝ (proj H) y v = 0 ↔ ∃ c : ℝ, v = c • y := by
  obtain ⟨hac, hpc⟩ := contDiffAt_aCoord_proj H hH y hy
  have ha := (hac.differentiableAt (by simp)).hasFDerivAt
  have hp := (hpc.differentiableAt (by simp)).hasFDerivAt
  -- the radial curve
  have hcurve : HasDerivAt (fun c : ℝ => Real.exp (2 * c) • y) ((2 : ℝ) • y) 0 := by
    have h1 : HasDerivAt (fun c : ℝ => Real.exp (2 * c)) 2 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).const_mul 2).exp
      simpa using this
    exact h1.smul_const y
  have hbase : Real.exp (2 * (0 : ℝ)) • y = y := by simp
  have hpr : fderiv ℝ (proj H) y ((2 : ℝ) • y) = 0 := by
    have h1 : HasDerivAt (fun c : ℝ => proj H (Real.exp (2 * c) • y))
        (fderiv ℝ (proj H) y ((2 : ℝ) • y)) 0 := by
      rw [← hbase] at hp
      have := hp.comp_hasDerivAt (0 : ℝ) hcurve
      rw [hbase] at this
      exact this
    have h2 : (fun c : ℝ => proj H (Real.exp (2 * c) • y)) = fun _ => proj H y :=
      funext fun c => (proj_aCoord_exp_smul H hH c y hy).1
    rw [h2] at h1
    exact h1.unique (hasDerivAt_const _ _)
  have har : fderiv ℝ (aCoord H) y ((2 : ℝ) • y) = 1 := by
    have h1 : HasDerivAt (fun c : ℝ => aCoord H (Real.exp (2 * c) • y))
        (fderiv ℝ (aCoord H) y ((2 : ℝ) • y)) 0 := by
      rw [← hbase] at ha
      have := ha.comp_hasDerivAt (0 : ℝ) hcurve
      rw [hbase] at this
      exact this
    have h2 : (fun c : ℝ => aCoord H (Real.exp (2 * c) • y)) = fun c => aCoord H y + c :=
      funext fun c => (proj_aCoord_exp_smul H hH c y hy).2
    rw [h2] at h1
    exact h1.unique ((hasDerivAt_id (0 : ℝ)).const_add _)
  constructor
  · intro hv
    have hinj := (injective_fderiv_aCoord_proj_comp_iff H hH (fun x : V n => x) y
      differentiableAt_id hy).2 (by rw [fderiv_id']; exact fun a b h => h)
    have hpair : HasFDerivAt (fun x : V n => (aCoord H x, proj H x))
        ((fderiv ℝ (aCoord H) y).prod (fderiv ℝ (proj H) y)) y := ha.prodMk hp
    rw [hpair.fderiv] at hinj
    refine ⟨fderiv ℝ (aCoord H) y v * 2, ?_⟩
    rw [mul_smul]
    refine hinj ?_
    have e1 : fderiv ℝ (aCoord H) y (fderiv ℝ (aCoord H) y v • (2 : ℝ) • y) =
        fderiv ℝ (aCoord H) y v := by
      rw [ContinuousLinearMap.map_smul _ _ ((2 : ℝ) • y), har, smul_eq_mul, mul_one]
    have e2 : fderiv ℝ (proj H) y (fderiv ℝ (aCoord H) y v • (2 : ℝ) • y) = 0 := by
      rw [ContinuousLinearMap.map_smul _ _ ((2 : ℝ) • y), hpr, smul_zero]
    simp only [ContinuousLinearMap.prod_apply]
    rw [e1, e2, hv]
  · rintro ⟨c, rfl⟩
    have h : fderiv ℝ (proj H) y y = 0 := by
      have := hpr
      rw [map_smul] at this
      exact (smul_eq_zero.1 this).resolve_left two_ne_zero
    rw [map_smul, h, smul_zero]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (y : V n) (hy : y ≠ 0) (v : V n) :
    fderiv ℝ (proj H) y v = 0 ↔ ∃ c : ℝ, v = c • y :=
  fderiv_proj_eq_zero_iff_aux H hH y hy v
