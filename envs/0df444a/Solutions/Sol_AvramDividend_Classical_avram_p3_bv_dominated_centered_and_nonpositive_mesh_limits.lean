-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_dominated_centered_and_nonpositive_mesh_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:52:16.441562+00:00
-- url     : https://prove2.me/submissions/02e26cf9-08d1-41ea-bd26-f86d11e891f7

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_dominated_mesh_residual_integrable_limit
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_dominated_mesh_residual_mean_nonpos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical

/-- Both the centred jump martingale and nonpositive HJB drift survive a
common integrably dominated original-process finite-mesh passage. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Mmesh Bmesh : ℕ → Ω → ℝ) (M B DM DB : Ω → ℝ)
    (hMMeas : ∀ n, AEStronglyMeasurable (Mmesh n) P)
    (hBMeas : ∀ n, AEStronglyMeasurable (Bmesh n) P)
    (hDM : Integrable DM P) (hDB : Integrable DB P)
    (hMDom : ∀ n, ∀ᵐ ω ∂P, |Mmesh n ω| ≤ DM ω)
    (hBDom : ∀ n, ∀ᵐ ω ∂P, |Bmesh n ω| ≤ DB ω)
    (hMLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω)))
    (hBLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω)))
    (hMMean : ∀ n, (∫ ω, Mmesh n ω ∂P) = 0)
    (hBMean : ∀ n, (∫ ω, Bmesh n ω ∂P) ≤ 0) :
    (Integrable M P ∧ (∫ ω, M ω ∂P) = 0) ∧
      (Integrable B P ∧ (∫ ω, B ω ∂P) ≤ 0) := by
  have hMI := avram_p3_c_bvchain_dominated_mesh_residual_integrable_limit
    P Mmesh M DM hMMeas hDM hMDom hMLim
  have hMU := avram_p3_c_bvchain_dominated_mesh_residual_mean_nonpos
    P Mmesh M DM hMMeas hDM hMDom hMLim
      (fun n => le_of_eq (hMMean n))
  have hMinusMeas : ∀ n,
      AEStronglyMeasurable (fun ω => -Mmesh n ω) P := by
    intro n
    exact (hMMeas n).neg
  have hMinusDom : ∀ n, ∀ᵐ ω ∂P, |-(Mmesh n ω)| ≤ DM ω := by
    intro n
    filter_upwards [hMDom n] with ω hω
    simpa only [abs_neg] using hω
  have hMinusLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => -Mmesh n ω) atTop (nhds (-M ω)) := by
    filter_upwards [hMLim] with ω hω
    exact hω.neg
  have hMinusMean : ∀ n, (∫ ω, -(Mmesh n ω) ∂P) ≤ 0 := by
    intro n
    rw [integral_neg, hMMean n]
    norm_num
  have hML := avram_p3_c_bvchain_dominated_mesh_residual_mean_nonpos
    P (fun n ω => -Mmesh n ω) (fun ω => -M ω) DM
    hMinusMeas hDM hMinusDom hMinusLim hMinusMean
  have hMZero : (∫ ω, M ω ∂P) = 0 := by
    have hLower : -(∫ ω, M ω ∂P) ≤ 0 := by
      rw [integral_neg] at hML
      exact hML
    linarith
  have hBI := avram_p3_c_bvchain_dominated_mesh_residual_integrable_limit
    P Bmesh B DB hBMeas hDB hBDom hBLim
  have hBU := avram_p3_c_bvchain_dominated_mesh_residual_mean_nonpos
    P Bmesh B DB hBMeas hDB hBDom hBLim hBMean
  exact ⟨⟨hMI, hMZero⟩, ⟨hBI, hBU⟩⟩
