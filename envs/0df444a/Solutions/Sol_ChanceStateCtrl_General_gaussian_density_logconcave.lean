-- Prove2me | solution 1 for ChanceStateCtrl.General.gaussian_density_logconcave
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-25T01:07:34.955526+00:00
-- url     : https://prove2.me/submissions/6f2a4d1e-0b7a-4ac0-88f2-4f51be0344e2

import Mathlib
open MeasureTheory ProbabilityTheory

/-- The product of standard Gaussians has the product density. -/
lemma pi_gaussian_eq_withDensity (m : ℕ) :
    Measure.pi (fun _ : Fin m => gaussianReal 0 1) =
      (volume : Measure (Fin m → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  refine Measure.pi_eq fun s hs => ?_
  have hbox : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hbox, ← lintegral_indicator hbox]
  set ψ : Fin m → ℝ → ℝ := fun i => (s i).indicator (gaussianPDFReal 0 1) with hψ
  have hpt : (Set.pi Set.univ s).indicator
      (fun x : Fin m → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) =
      fun x => ENNReal.ofReal (∏ i, ψ i (x i)) := by
    funext x
    by_cases hx : x ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hx]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hψ]; simp only; rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hψ, hi]), ENNReal.ofReal_zero]
  rw [hpt]
  have hψint : ∀ i, Integrable (ψ i) volume := fun i =>
    (integrable_gaussianPDFReal 0 1).indicator (hs i)
  have hψnn : ∀ i y, 0 ≤ ψ i y := fun i y =>
    Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) y
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [volume_pi, integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg]
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [gaussianReal_apply_eq_integral 0 one_ne_zero, hψ, integral_indicator (hs i)]
    · exact fun i _ => integral_nonneg (hψnn i)
  · rw [volume_pi]; exact Integrable.fintype_prod hψint
  · exact Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun i _ => hψnn i (x i)

/-- Pushing a measure with density forward along a measurable equivalence. -/
lemma map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (e : α ≃ᵐ β) (f : α → ENNReal) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, setLIntegral_map hs (hf.comp e.symm.measurable) e.measurable]
  simp

/-- Log-concavity in the multiplicative form used by Prékopa's theorem. -/
def LogConc {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → ℝ) : Prop :=
  ∀ z w : E, ∀ t ∈ Set.Icc (0 : ℝ) 1, f z ^ t * f w ^ (1 - t) ≤ f (t • z + (1 - t) • w)

lemma logConc_mul {E : Type*} [AddCommGroup E] [Module ℝ E] {f g : E → ℝ}
    (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z) (hf : LogConc f) (hg : LogConc g) :
    LogConc (fun z => f z * g z) := by
  intro z w t ht
  simp only
  rw [Real.mul_rpow (hf0 z) (hg0 z), Real.mul_rpow (hf0 w) (hg0 w)]
  calc f z ^ t * g z ^ t * (f w ^ (1 - t) * g w ^ (1 - t))
      = (f z ^ t * f w ^ (1 - t)) * (g z ^ t * g w ^ (1 - t)) := by ring
    _ ≤ f (t • z + (1 - t) • w) * g (t • z + (1 - t) • w) :=
      mul_le_mul (hf z w t ht) (hg z w t ht)
        (mul_nonneg (Real.rpow_nonneg (hg0 z) _) (Real.rpow_nonneg (hg0 w) _)) (hf0 _)

lemma logConc_const {E : Type*} [AddCommGroup E] [Module ℝ E] {c : ℝ} (hc : 0 ≤ c) :
    LogConc (fun _ : E => c) := by
  intro z w t ht
  simp only
  rw [← Real.rpow_add' hc (by norm_num : t + (1 - t) ≠ 0)]
  norm_num

lemma logConc_prod {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} (s : Finset ι)
    (f : ι → E → ℝ) (hf0 : ∀ i z, 0 ≤ f i z) (hf : ∀ i, LogConc (f i)) :
    LogConc (fun z => ∏ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using logConc_const (E := E) (c := 1) zero_le_one
  | insert a s ha ih =>
    have := logConc_mul (hf0 a) (fun z => Finset.prod_nonneg fun i _ => hf0 i z) (hf a) ih
    simpa [Finset.prod_insert ha] using this

lemma logConc_gaussian_comp {E : Type*} [AddCommGroup E] [Module ℝ E] (L : E →ₗ[ℝ] ℝ) :
    LogConc (fun z => gaussianPDFReal 0 1 (L z)) := by
  have hexp : LogConc (fun z : E => Real.exp (-(L z) ^ 2 / 2)) := by
    intro z w t ht
    simp only
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, map_add, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul]
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg ht.1 (sub_nonneg.2 ht.2), sq_nonneg (L z - L w),
      mul_nonneg (mul_nonneg ht.1 (sub_nonneg.2 ht.2)) (sq_nonneg (L z - L w))]
  have := logConc_mul (fun _ => by positivity) (fun _ => (Real.exp_pos _).le)
    (logConc_const (E := E) (c := (√(2 * Real.pi * ((1 : NNReal) : ℝ)))⁻¹) (by positivity)) hexp
  intro z w t ht
  have h := this z w t ht
  simpa [gaussianPDFReal, sub_zero] using h

open scoped MatrixOrder in
theorem solution {m : ℕ} (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (hS : Sigma.PosDef) :
    ∃ dens : EuclideanSpace ℝ (Fin m) → ℝ, (∀ z, 0 ≤ dens z) ∧ Measurable dens ∧
      multivariateGaussian 0 Sigma = volume.withDensity (fun z => ENNReal.ofReal (dens z)) ∧
      ∀ z w : EuclideanSpace ℝ (Fin m), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dens z ^ t * dens w ^ (1 - t) ≤ dens (t • z + (1 - t) • w) := by
  classical
  set E := EuclideanSpace ℝ (Fin m)
  set S := CFC.sqrt Sigma with hSdef
  have hS0 : 0 ≤ Sigma := Matrix.nonneg_iff_posSemidef.2 hS.posSemidef
  have hSS : S * S = Sigma := CFC.sqrt_mul_sqrt_self Sigma hS0
  have hdet : IsUnit S.det := by
    have h1 : S.det * S.det = Sigma.det := by rw [← Matrix.det_mul, hSS]
    have h2 : 0 < Sigma.det := hS.det_pos
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, zero_mul] at h1; linarith
  set A : E →L[ℝ] E := Matrix.toEuclideanCLM (𝕜 := ℝ) S with hA
  set B : E →L[ℝ] E := Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ with hB
  have hAB : A * B = 1 := by
    rw [hA, hB, ← map_mul, Matrix.mul_nonsing_inv S hdet, map_one]
  have hBA : B * A = 1 := by
    rw [hA, hB, ← map_mul, Matrix.nonsing_inv_mul S hdet, map_one]
  have hleft : Function.LeftInverse B A := fun x => by
    have := congrArg (fun L : E →L[ℝ] E => L x) hBA
    simpa using this
  have hright : Function.RightInverse B A := fun x => by
    have := congrArg (fun L : E →L[ℝ] E => L x) hAB
    simpa using this
  set Aeq : E ≃L[ℝ] E := ContinuousLinearEquiv.equivOfInverse A B hleft hright with hAeq
  set T : (Fin m → ℝ) ≃ᵐ E :=
    (MeasurableEquiv.toLp 2 (Fin m → ℝ)).trans Aeq.toHomeomorph.toMeasurableEquiv with hT
  set L : Fin m → E →L[ℝ] ℝ := fun i => (EuclideanSpace.proj i).comp B with hL
  have hTsymm : ∀ z i, (T.symm z) i = L i z := fun z i => rfl
  set c : ℝ := |(LinearMap.det (A : E →ₗ[ℝ] E))⁻¹| with hc
  set dens : E → ℝ := fun z => c * ∏ i, gaussianPDFReal 0 1 (L i z) with hdens
  have hdens0 : ∀ z, 0 ≤ dens z := fun z =>
    mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _)
  refine ⟨dens, hdens0, ?_, ?_, ?_⟩
  · exact (Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDFReal 0 1).comp (L i).continuous.measurable).const_mul c
  · -- the law
    have hmg : multivariateGaussian 0 Sigma = (stdGaussian E).map A := by
      simp only [multivariateGaussian, zero_add]; rfl
    have hstd : stdGaussian E = (Measure.pi fun _ : Fin m => gaussianReal 0 1).map (WithLp.toLp 2) :=
      (map_pi_eq_stdGaussian).symm
    have hT' : (⇑T : (Fin m → ℝ) → E) = A ∘ WithLp.toLp 2 := rfl
    have hF : Measurable (fun x : Fin m → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) :=
      ENNReal.measurable_ofReal.comp
        (Finset.measurable_prod _ fun i _ => (measurable_gaussianPDFReal 0 1).comp
          (measurable_pi_apply i))
    have h1 : multivariateGaussian 0 Sigma =
        (Measure.pi fun _ : Fin m => gaussianReal 0 1).map T := by
      rw [hmg, hstd, Measure.map_map A.continuous.measurable (by fun_prop), hT']
    have hvolT : (volume : Measure (Fin m → ℝ)).map T = ENNReal.ofReal c • volume := by
      have hdetne : LinearMap.det (A : E →ₗ[ℝ] E) ≠ 0 := by
        have := LinearEquiv.isUnit_det' (Aeq.toLinearEquiv)
        exact this.ne_zero
      have hv : (volume : Measure (Fin m → ℝ)).map (MeasurableEquiv.toLp 2 (Fin m → ℝ)) = volume :=
        (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).symm.map_eq
      rw [show (⇑T : (Fin m → ℝ) → E) = A ∘ (MeasurableEquiv.toLp 2 (Fin m → ℝ)) from rfl,
        ← Measure.map_map A.continuous.measurable (MeasurableEquiv.measurable _), hv]
      exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdetne
    rw [h1, pi_gaussian_eq_withDensity, map_withDensity_equiv _ T _ hF, hvolT,
      withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext z
    simp only [Pi.smul_apply, Function.comp, smul_eq_mul, hdens, hTsymm]
    rw [ENNReal.ofReal_mul (abs_nonneg _)]
  · -- log-concavity
    have := logConc_mul (fun _ => abs_nonneg _)
      (fun z => Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _)
      (logConc_const (E := E) (c := c) (abs_nonneg _))
      (logConc_prod Finset.univ (fun i z => gaussianPDFReal 0 1 ((L i : E →ₗ[ℝ] ℝ) z))
        (fun i z => gaussianPDFReal_nonneg 0 1 _) fun i => logConc_gaussian_comp _)
    exact this
