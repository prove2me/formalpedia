-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_triple_mesh_signed_budget_ae_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:52:49.993041+00:00
-- url     : https://prove2.me/submissions/5dd7886f-438d-4150-a086-fa0240b71d4f

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter

/-- The original-process stopped reward, centred source-jump term and HJB
drift may all be approximated on the same finite time meshes. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Ymesh Mmesh Bmesh : ℕ → Ω → ℝ)
    (Y M B : Ω → ℝ) (K : ℝ)
    (hMesh : ∀ᵐ ω ∂P, ∀ n,
      Ymesh n ω ≤ K + Mmesh n ω + Bmesh n ω)
    (hYLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Ymesh n ω) atTop (nhds (Y ω)))
    (hMLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω)))
    (hBLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω))) :
    ∀ᵐ ω ∂P, Y ω ≤ K + M ω + B ω := by
  filter_upwards [hMesh, hYLim, hMLim, hBLim] with ω hMeshω hYω hMω hBω
  have hRhs : Tendsto
      (fun n => K + Mmesh n ω + Bmesh n ω) atTop
      (nhds (K + M ω + B ω)) :=
    (tendsto_const_nhds.add hMω).add hBω
  have hDiff : Tendsto
      (fun n => Ymesh n ω - (K + Mmesh n ω + Bmesh n ω)) atTop
      (nhds (Y ω - (K + M ω + B ω))) := hYω.sub hRhs
  have hLimit : Y ω - (K + M ω + B ω) ≤ 0 := by
    apply le_of_tendsto hDiff
    exact Filter.Eventually.of_forall (fun n => sub_nonpos.mpr (hMeshω n))
  linarith
