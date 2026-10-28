-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_rough_mul_generator_eq_neg_energy_of_contDiff_one_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:03:17.126482+00:00
-- url     : https://prove2.me/submissions/e6bd484a-ee25-4a64-a7f5-c94543441df9

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_WeakCutoff
import Theorems.Thm_FunctionalInequalities_Analysis_integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test_readable
import Theorems.Thm_FunctionalInequalities_Analysis_integral_mul_generator_eq_neg_energy_of_contDiff_one_readable

section
noncomputable section
open MeasureTheory
open scoped ContDiff
universe u
section SharedCompactLocalTools
open MeasureTheory Set Filter
open scoped ContDiff RealInnerProductSpace Topology
section
/-- A continuous function is essentially bounded on every compact set. -/
theorem FunctionalInequalities.Analysis.memLp_top_restrict_of_continuous {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp f (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.measurable.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  exact hC x hx
end
end SharedCompactLocalTools
end
end

noncomputable section
open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology RealInnerProductSpace
private theorem FunctionalInequalities.Analysis.hasCompactSupport_inverse_hessian_cutoff_flux_generator {n : ℕ}
    (u V χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : HasCompactSupport χ) :
    (∀ i j : Fin n, HasCompactSupport (fun x => hessianMatrix χ x i j)) ∧
    (∀ i : Fin n, HasCompactSupport (fun x => Real.exp (-u x) *
      ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
        fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ j))) ∧
    HasCompactSupport (fun x =>
      (((hessianMatrix u x)⁻¹ * hessianMatrix χ x).trace -
        fderiv ℝ V (gradient u x) (gradient χ x)) * Real.exp (-u x)) := by
  have hd (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ tsupport χ) :
      fderiv ℝ χ x = 0 := fderiv_of_notMem_tsupport ℝ hx
  have hdd (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ tsupport χ) :
      fderiv ℝ (fderiv ℝ χ) x = 0 := by
    exact fderiv_of_notMem_tsupport ℝ (fun h => hx ((tsupport_fderiv_subset ℝ) h))
  have hH (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ tsupport χ) :
      hessianMatrix χ x = 0 := by
    ext i j
    simp [hessianMatrix, bilinearIteratedFDerivTwo, hdd x hx]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    apply HasCompactSupport.intro hχ
    intro x hx
    simp [hH x hx]
  · intro i
    apply HasCompactSupport.intro hχ
    intro x hx
    simp [hd x hx]
  · apply HasCompactSupport.intro hχ
    intro x hx
    have hg : gradient χ x = 0 := by simp [gradient, hd x hx]
    simp [hH x hx, hg]
/-- A globally bounded locally integrable weak function `η` with compact-local L2 coordinate weak derivatives `aᵢ`,
paired with the inverse-Hessian generator of a compactly supported C1 cutoff `χ` with Lipschitz gradient at a C1
Monge–Ampère potential `u`: both pairings are integrable and the generator pairing equals minus the weighted energy
pairing `∫ ∑ (∇²u)⁻¹ᵢⱼ aᵢ ∂ⱼχ e^{-u}`. -/
theorem solution {n : ℕ}
    {u V χ η : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) {LF : NNReal}
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hχ : ContDiff ℝ 1 χ) {Gχ : NNReal} (hGχ : LipschitzWith Gχ (gradient χ))
    (hχc : HasCompactSupport χ)
    (hInv : ∀ i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hForce : Integrable (fun x =>
      (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix χ x).trace -
        fderiv ℝ V (gradient u x) (gradient χ x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {C : ℝ} (hbound : ∀ x, ‖η x‖ ≤ C)
    (hweak : ∀ i : Fin n, FunctionalInequalities.Analysis.HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    Integrable (fun x => η x *
      (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix χ x).trace -
        fderiv ℝ V (gradient u x) (gradient χ x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => (∑ i : Fin n, ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
      a i x * fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, η x * (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix χ x).trace -
      fderiv ℝ V (gradient u x) (gradient χ x)) * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
    -(∫ x, (∑ i : Fin n, ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
      a i x * fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let J := fun i x => Real.exp (-u x) *
    ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j * fderiv ℝ χ x (e j)
  let F := fun x => (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix χ x).trace -
    fderiv ℝ V (gradient u x) (gradient χ x)) * Real.exp (-u x)
  have he : Continuous (fun x => Real.exp (-u x)) := Real.continuous_exp.comp hu.continuous.neg
  have hcoord (j : Fin n) : Continuous (fun x => fderiv ℝ χ x (e j)) :=
    (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hJ (i : Fin n) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
      MemLp (J i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    have hsum : MemLp (fun x => ∑ j : Fin n,
        (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j * fderiv ℝ χ x (e j)) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
      apply memLp_finsetSum Finset.univ
      intro j _
      exact (FunctionalInequalities.Analysis.memLp_top_restrict_of_continuous (hcoord j) S hS).mul' (hInv i j S hS)
    have hp : MemLp (J i) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      hsum.mul' (FunctionalInequalities.Analysis.memLp_top_restrict_of_continuous he S hS)
    exact hp.mono_exponent (by norm_num)
  have hsupport := FunctionalInequalities.Analysis.hasCompactSupport_inverse_hessian_cutoff_flux_generator u V χ hχc
  have hJeq (b : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
      (∑ i : Fin n, J i x * b i x) =
        (∑ i : Fin n, ∑ j : Fin n, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j * b i x *
          fderiv ℝ χ x (e j)) * Real.exp (-u x) := by
    simp only [J, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hFeq (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
      F x * ψ x = ψ x * (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix χ x).trace -
        fderiv ℝ V (gradient u x) (gradient χ x)) * Real.exp (-u x) := by dsimp only [F]; ring
  have hId (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (hψ : ContDiff ℝ 1 ψ)
      (hψc : HasCompactSupport ψ) :
      (∫ x, ∑ i : Fin n, J i x * fderiv ℝ ψ x (e i)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    have hp := FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy_of_contDiff_one_readable hu hG hV hF hdet
      hχ hGχ hψ hψc
    have hj := integral_congr_ae (μ := volume) (Filter.Eventually.of_forall (hJeq (fun i x => fderiv ℝ ψ x (e i))))
    have hf := integral_congr_ae (μ := volume) (Filter.Eventually.of_forall (hFeq ψ))
    rw [hj, hf]
    simpa only [neg_neg] using (congrArg Neg.neg hp).symm
  obtain ⟨hprod, hforce, hEq⟩ := FunctionalInequalities.Analysis.integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test_readable
    hJ hForce.locallyIntegrable hsupport.2.1 hsupport.2.2 hId hη hbound hweak ha2
  have hE : Integrable (fun x => ∑ i : Fin n, J i x * a i x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    integrable_finsetSum Finset.univ fun i _ => hprod i
  refine ⟨hforce.congr (Filter.Eventually.of_forall (hFeq η)),
    hE.congr (Filter.Eventually.of_forall (hJeq a)), ?_⟩
  have hj := integral_congr_ae (μ := volume) (Filter.Eventually.of_forall (hJeq a))
  have hf := integral_congr_ae (μ := volume) (Filter.Eventually.of_forall (hFeq η))
  rw [hj, hf] at hEq
  simpa only [neg_neg] using (congrArg Neg.neg hEq).symm
