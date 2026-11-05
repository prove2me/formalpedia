-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_L1_mesh_error_rate_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:46:32.140702+00:00
-- url     : https://prove2.me/submissions/ba114289-410a-4f99-887a-d7fd7efa647a

import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_L1_mesh_residual_mean_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical

/-- A vanishing scalar L1 mesh-error rate transfers nonpositive source means. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R : Ω → ℝ) (Rmesh : ℕ → Ω → ℝ) (δ : ℕ → ℝ)
    (hR : Integrable R P)
    (hMesh : ∀ n, Integrable (Rmesh n) P)
    (hMean : ∀ n, (∫ ω, Rmesh n ω ∂P) ≤ 0)
    (hδ : Tendsto δ atTop (nhds (0 : ℝ)))
    (hRate : ∀ n,
      (∫ ω, |Rmesh n ω - R ω| ∂P) ≤ δ n) :
    (∫ ω, R ω ∂P) ≤ 0 := by
  have hError : Tendsto
      (fun n => (∫ ω, |Rmesh n ω - R ω| ∂P))
      atTop (nhds (0 : ℝ)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ))
        atTop (nhds 0)) hδ
    · intro n
      exact integral_nonneg (fun ω => abs_nonneg _)
    · exact hRate
  exact avram_p3_c_bvchain_L1_mesh_residual_mean_nonpos
    P R Rmesh hR hMesh hMean hError
