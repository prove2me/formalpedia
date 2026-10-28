-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_source_stein_identity_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:30.447066+00:00
-- url     : https://prove2.me/submissions/34abd4bb-03e9-4816-a5b4-663e7a241203

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_ProductCoupling
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_translated_directional_identity_of_bounded_lipschitz_test_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussian_product_source_stein_pairings_integrable_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_source_affine_stein_identity_of_bounded_lipschitz_test_readable

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace Topology
set_option maxHeartbeats 800000 in
theorem solution {n : ℕ}
    {u h : EuclideanSpace ℝ (Fin n) → ℝ} {L G Lh : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
    (hh : ContDiff ℝ 1 h) (hhLip : LipschitzWith Lh h)
    (C : ℝ) (hbound : ∀ x, ‖h x‖ ≤ C)
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : 0 < s) :
    let P := ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).prod
      (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw (V := EuclideanSpace ℝ (Fin n)) s)
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ⟪S (gradient u p.1) + p.2, v⟫ * h (S (gradient u p.1) + p.2)) P ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ⟪S.adjoint v, FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u p.1)
        (S.adjoint (gradient h (S (gradient u p.1) + p.2)))⟫ +
          (2 * s)⁻¹ * fderiv ℝ h (S (gradient u p.1) + p.2) v) P ∧
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ⟪S (gradient u p.1) + p.2, v⟫ * h (S (gradient u p.1) + p.2) ∂P) =
      ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ⟪S.adjoint v, FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u p.1)
          (S.adjoint (gradient h (S (gradient u p.1) + p.2)))⟫ +
            (2 * s)⁻¹ * fderiv ℝ h (S (gradient u p.1) + p.2) v ∂P := by
  let E := EuclideanSpace ℝ (Fin n)
  let rho : Measure E := volume.tilted (-u)
  let nu : Measure E := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s
  let P := rho.prod nu
  let SL : E × E → ℝ := fun p => ⟪S (gradient u p.1),v⟫ * h (S (gradient u p.1)+p.2)
  let NL : E × E → ℝ := fun p => ⟪p.2,v⟫ * h (S (gradient u p.1)+p.2)
  let SR : E × E → ℝ := fun p =>
    ⟪S.adjoint v,FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u p.1) (S.adjoint (gradient h (S (gradient u p.1)+p.2)))⟫
  let NR : E × E → ℝ := fun p => fderiv ℝ h (S (gradient u p.1)+p.2) v
  have hexp : Integrable (fun y : E => Real.exp (-u y)) volume :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  let : IsProbabilityMeasure rho := isProbabilityMeasure_tilted hexp
  let : IsProbabilityMeasure nu := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_probability hs
  obtain ⟨_hZ,_hF,_hGH,hSL,hNL,hSR,hNR⟩ :=
    FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_source_stein_pairings_integrable_readable hu hL hG hnorm hh hhLip C hbound S v hs
  have hsrc : (∫ p, SL p ∂P) = ∫ p, SR p ∂P := by
    rw [integral_prod_symm SL hSL,integral_prod_symm SR hSR]
    apply integral_congr_ae
    filter_upwards [] with z
    exact (FunctionalInequalities.KLS.LogConcave.source_affine_stein_identity_of_bounded_lipschitz_test_readable hu hL hG hnorm
      hh hhLip C hbound S z v).2.2
  have hnoise : (∫ p, NL p ∂P) = (2*s)⁻¹ * ∫ p, NR p ∂P := by
    calc
      _ = ∫ y, ∫ z, NL (y,z) ∂nu ∂rho := integral_prod NL hNL
      _ = ∫ y, (2*s)⁻¹ * ∫ z, NR (y,z) ∂nu ∂rho := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_translated_directional_identity_of_bounded_lipschitz_test_readable
          hh hhLip C hbound (S (gradient u y)) v hs).2.2
      _ = (2*s)⁻¹ * ∫ y, ∫ z, NR (y,z) ∂nu ∂rho := integral_const_mul _ _
      _ = _ := by rw [← integral_prod NR hNR]
  have hleft (p : E × E) : ⟪S (gradient u p.1)+p.2,v⟫ * h (S (gradient u p.1)+p.2) =
      SL p + NL p := by
    dsimp only [SL,NL]
    rw [inner_add_left,add_mul]
  have hLtotal : Integrable (fun p : E × E =>
      ⟪S (gradient u p.1)+p.2,v⟫ * h (S (gradient u p.1)+p.2)) P :=
    (hSL.add hNL).congr (ae_of_all _ fun p => (hleft p).symm)
  have hRtotal : Integrable (fun p : E × E => SR p + (2*s)⁻¹ * NR p) P :=
    hSR.add (hNR.const_mul ((2*s)⁻¹))
  refine ⟨hLtotal,hRtotal,?_⟩
  calc
    _ = ∫ p, SL p + NL p ∂P := integral_congr_ae (ae_of_all _ hleft)
    _ = (∫ p, SL p ∂P) + ∫ p, NL p ∂P := integral_add hSL hNL
    _ = (∫ p, SR p ∂P) + (2*s)⁻¹ * ∫ p, NR p ∂P := by rw [hsrc,hnoise]
    _ = (∫ p, SR p ∂P) + ∫ p, (2*s)⁻¹ * NR p ∂P := by rw [integral_const_mul]
    _ = _ := (integral_add hSR (hNR.const_mul ((2*s)⁻¹))).symm
