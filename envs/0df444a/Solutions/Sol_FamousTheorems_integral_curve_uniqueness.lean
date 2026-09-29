-- Prove2me | solution 1 for FamousTheorems.integral_curve_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:47:35.959376+00:00
-- url     : https://prove2.me/submissions/49d1e7f4-a1d9-46b1-87bb-e97ee720177c

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [T2Space M]
    [BoundarylessManifold I M] {v : (x : M) → TangentSpace I x} {γ γ' : ℝ → M} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurveOn γ v (Set.Ioo a b)) (hγ' : IsMIntegralCurveOn γ' v (Set.Ioo a b)) (h : γ t₀ = γ' t₀) :
    Set.EqOn γ γ' (Set.Ioo a b) :=
  isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht₀ hv hγ hγ' h
