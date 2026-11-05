-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_mesh_pathwise_signed_upper_bound_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:48:03.780337+00:00
-- url     : https://prove2.me/submissions/3c4511a1-fbbe-453c-970d-f9b43f947f9f

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter

/-- An original-path BV cash-plus-terminal upper bound on every mesh passes
to the a.e. limits of its signed martingale and HJB terms. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y M B : Ω → ℝ) (Mmesh Bmesh : ℕ → Ω → ℝ) (K : ℝ)
    (hMesh : ∀ᵐ ω ∂P, ∀ n,
      Y ω ≤ K + Mmesh n ω + Bmesh n ω)
    (hMLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω)))
    (hBLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω))) :
    ∀ᵐ ω ∂P, Y ω ≤ K + M ω + B ω := by
  filter_upwards [hMesh, hMLim, hBLim] with ω hMeshω hMω hBω
  have hTend : Tendsto
      (fun n => K + Mmesh n ω + Bmesh n ω) atTop
      (nhds (K + M ω + B ω)) :=
    (tendsto_const_nhds.add hMω).add hBω
  have hNeg : -(K + M ω + B ω) ≤ -(Y ω) := by
    apply le_of_tendsto hTend.neg
    exact Filter.Eventually.of_forall (fun n => neg_le_neg (hMeshω n))
  linarith
