-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_bounded_weak_mul_weightedLaplacian_of_contDiff_one_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:03:18.380991+00:00
-- url     : https://prove2.me/submissions/cfda7c40-a3e5-40a2-a131-4d8e0d53ffe5

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakLaplacian
import Theorems.Thm_FunctionalInequalities_Analysis_integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test_readable

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ContDiff Topology RealInnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery
set_option maxHeartbeats 1000000 in
/-- Rough integration by parts for the ordinary weighted Laplacian at a C1 potential with mass-one exponential
weight: for a smooth compactly supported `v` and a globally bounded locally integrable weak `η` with compact-local
L2 coordinate weak derivatives `aᵢ`, both tilted pairings are integrable and `∫ η ℒv dν = -∫ ∑ aᵢ ∂ᵢv dν`. -/
theorem solution {n : ℕ}
    {U v eta : EuclideanSpace ℝ (Fin n) → ℝ}
    (hU : ContDiff ℝ 1 U) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (hnorm : (∫ x, Real.exp (-U x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ)
    (heta : LocallyIntegrable eta (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖eta x‖ ≤ C)
    (hweak : ∀ i : Fin n, FunctionalInequalities.Analysis.HasWeakDerivAlong eta (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    Integrable (fun x => eta x * FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U v x)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) ∧
    Integrable (fun x => ∑ i : Fin n, a i x *
      fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) ∧
    (∫ x, eta x * FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U v x
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))) =
      -(∫ x, (∑ i : Fin n, a i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i))
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))) := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let rho := fun x => Real.exp (-U x)
  let dv := fun i x => fderiv ℝ v x (e i)
  let J := fun i x => rho x * dv i x
  let F := fun x => rho x * FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U v x
  have hv1 : ContDiff ℝ 1 v := hv.of_le (WithTop.coe_le_coe.mpr le_top)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (WithTop.coe_le_coe.mpr le_top)
  have hrho : Continuous rho := Real.continuous_exp.comp hU.continuous.neg
  have hdv (i : Fin n) : Continuous (dv i) :=
    (hv1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdvc (i : Fin n) : HasCompactSupport (dv i) := hvc.fderiv_apply ℝ (e i)
  have hJc (i : Fin n) : HasCompactSupport (J i) := (hdvc i).mul_left
  have hJcont (i : Fin n) : Continuous (J i) := hrho.mul (hdv i)
  have hFcont : Continuous F := hrho.mul (FunctionalInequalities.Analysis.BakryEmery.continuous_weightedLaplacian hU hv2)
  have hFc : HasCompactSupport F := (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_weightedLaplacian U hvc).mul_left
  have hJ2 (i : Fin n) (S : Set (EuclideanSpace ℝ (Fin n))) (_hS : IsCompact S) :
      MemLp (J i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    ((hJcont i).memLp_of_hasCompactSupport (hJc i)).restrict S
  have hFloc : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hFcont.integrable_of_hasCompactSupport hFc).locallyIntegrable
  have hcoord (psi : EuclideanSpace ℝ (Fin n) → ℝ) (x) :
      ⟪gradient v x, gradient psi x⟫ =
        ∑ i : Fin n, dv i x * fderiv ℝ psi x (e i) := by
    rw [← e.sum_inner_mul_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_gradient_left, real_inner_comm, inner_gradient_left]
  have hId (psi : EuclideanSpace ℝ (Fin n) → ℝ) (hpsi : ContDiff ℝ 1 psi)
      (_hcpsi : HasCompactSupport psi) :
      (∫ x, ∑ i : Fin n, J i x * fderiv ℝ psi x (e i)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * psi x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    have hi := FunctionalInequalities.Analysis.BakryEmery.integral_inner_gradient_tilted (volume : Measure (EuclideanSpace ℝ (Fin n)))
      hU hv2 hvc hpsi
    rw [integral_tilted, integral_tilted] at hi
    simp only [Pi.neg_apply, hnorm, div_one, smul_eq_mul] at hi
    calc
      _ = ∫ x, rho x * ⟪gradient v x, gradient psi x⟫
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hcoord]
        simp only [J, Finset.mul_sum, mul_assoc]
      _ = ∫ x, rho x * (-FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U v x * psi x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hi
      _ = _ := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp only [F]
        ring
  obtain ⟨hJa, hFeta, hEq⟩ :=
    FunctionalInequalities.Analysis.integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test_readable
      hJ2 hFloc hJc hFc hId heta hbound hweak ha2
  have hexp : Integrable (fun x => Real.exp (-U x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  have hSum := integrable_finsetSum Finset.univ fun i _ => hJa i
  have hFetaEq : (fun x => F x * eta x) =
      (fun x => rho x * (eta x * FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U v x)) := by
    funext x
    dsimp only [F]
    ring
  have hSumEq : (fun x => ∑ i : Fin n, J i x * a i x) =
      (fun x => rho x * ∑ i : Fin n, a i x * dv i x) := by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [J]
    ring
  refine ⟨?_, ?_, ?_⟩
  · apply (integrable_tilted_iff hexp _).mpr
    simpa only [Pi.neg_apply, smul_eq_mul, rho] using hFetaEq ▸ hFeta
  · apply (integrable_tilted_iff hexp _).mpr
    simpa only [Pi.neg_apply, smul_eq_mul, rho, dv, e] using hSumEq ▸ hSum
  · rw [integral_tilted, integral_tilted]
    simp only [Pi.neg_apply, hnorm, div_one, smul_eq_mul]
    rw [hFetaEq, hSumEq] at hEq
    change (∫ x, Real.exp (-U x) * (∑ i : Fin n,
      a i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i))
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-U x) * (eta x * FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U v x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) at hEq
    linarith only [hEq]
