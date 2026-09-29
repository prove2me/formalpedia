-- Prove2me | solution 2 for FamousTheorems.integral_curve_local_existence
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:46:27.902977+00:00
-- url     : https://prove2.me/submissions/96b55835-716f-4080-8036-0941ca36a465

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [BoundarylessManifold I M] {v : (x : M) → TangentSpace I x} (t₀ : ℝ) {x₀ : M}
    (hv : ContMDiffAt I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) x₀) :
    ∃ γ : ℝ → M, γ t₀ = x₀ ∧ IsMIntegralCurveAt γ v t₀ :=
  exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless t₀ hv
