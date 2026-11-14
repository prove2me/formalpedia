-- Prove2me | solution 1 for BosonicLearn.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-14T03:46:50.791308+00:00
-- url     : https://prove2.me/submissions/62a13a22-bc86-4cc7-ad17-7074f6878dae

/-
Direct proof of BosonicLearn.proposition_1.
All helper theorems are proved. Existing platform imports are Proved.
Lean v4.33.1; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Definitions.Def_BosonicLearn_priorMu
import Definitions.Def_BosonicLearn_Ggood
import Definitions.Def_BosonicLearn_Herm0
import Definitions.Def_WHMultiplicativity_schattenNorm
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_HighDimProb_RandomProcesses_ProcessESup
import Theorems.Thm_HighDimProb_RandomProcesses_sudakov_fernique
import Theorems.Thm_GaussianMatrix_gaussian_concentration_vector
import Theorems.Thm_GaussianMatrix_sudakov_fernique
import Definitions.Def_BosonicLearn_herm0Ball
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_fugacityFamily
import Definitions.Def_BosonicLearn_Gsupp
import Theorems.Thm_BosonicLearn_gammaFock_mul
import Theorems.Thm_BosonicLearn_gammaFock_posSemidef
import Definitions.Def_BosonicLearn_PhiMap

set_option autoImplicit false

/- Local helper source: Solutions.Prop1Likelihood -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- Markov's inequality for an unnormalized numerator against an arbitrary sampling density.
This formulation avoids division by that density, including at its zeros. -/
theorem density_weighted_markov {Ω : Type*} [MeasurableSpace Ω]
    (ref : Measure Ω) (p A : Ω → ℝ≥0∞) (hp : Measurable p) (hA : Measurable A)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    (ref.withDensity p) {x | c * p x < A x} ≤ (∫⁻ x, A x ∂ref) / c := by
  have hb : MeasurableSet {x | c * p x < A x} := measurableSet_lt (measurable_const.mul hp) hA
  rw [withDensity_apply _ hb]
  calc
    _ ≤ ∫⁻ x in {x | c * p x < A x}, A x / c ∂ref := by
      apply setLIntegral_mono' hb
      intro x hx
      apply (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct)).mpr
      simpa only [mul_comm] using hx.le
    _ = (∫⁻ x in {x | c * p x < A x}, A x ∂ref) / c := by
      simp only [div_eq_mul_inv]
      exact lintegral_mul_const _ hA
    _ ≤ _ := by
      exact ENNReal.div_le_div_right (lintegral_mono' Measure.restrict_le_self le_rfl) c

/-- A mixture of normalized likelihoods has total mass equal to the parameter mass. -/
theorem lintegral_mixture_likelihood {Θ Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω]
    (μ : Measure Θ) [SFinite μ] (ref : Measure Ω) [SFinite ref]
    (p : Θ → Ω → ℝ≥0∞) (hp : Measurable (Function.uncurry p))
    (hnorm : ∀ θ, IsProbabilityMeasure (ref.withDensity (p θ))) (B : Set Θ) :
    (∫⁻ x, ∫⁻ θ in B, p θ x ∂μ ∂ref) = μ B := by
  rw [← lintegral_lintegral_swap hp.aemeasurable]
  have hone (θ : Θ) : (∫⁻ x, p θ x ∂ref) = 1 := by
    have := hnorm θ
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using
      (measure_univ (μ := ref.withDensity (p θ)))
  simp_rw [hone]
  simp

/-- The statistical part of Proposition 1. Geometric domination supplies the denominator;
only the small mass of the numerator set is required for the probability estimate. -/
theorem likelihood_ratio_event_of_geometry {Θ Ω : Type*}
    [MeasurableSpace Θ] [MeasurableSpace Ω]
    (μ : Measure Θ) [SFinite μ] (ref : Measure Ω) [SFinite ref]
    (p : Θ → Ω → ℝ≥0∞) (hp : Measurable (Function.uncurry p))
    (hnorm : ∀ θ, IsProbabilityMeasure (ref.withDensity (p θ)))
    (θ₀ : Θ) (B C : Set Θ) (F : Ω → ℝ≥0∞)
    (e d δ : ℝ≥0∞) (he0 : e ≠ 0) (het : e ≠ ⊤) (hd0 : d ≠ 0) (hdt : d ≠ ⊤)
    (hmass : μ B ≤ δ * (e * d))
    (hdom : ∀ x, d * F x ≤ ∫⁻ θ in C, p θ x ∂μ) :
    1 - δ ≤ (ref.withDensity (p θ₀))
      {x | (∫⁻ θ in B, p θ x ∂μ) * F x ≤ e * p θ₀ x * ∫⁻ θ in C, p θ x ∂μ} := by
  have := hnorm θ₀
  let A := fun x => ∫⁻ θ in B, p θ x ∂μ
  have hp₀ : Measurable (p θ₀) := hp.of_uncurry_left
  have hA : Measurable A := hp.lintegral_prod_left
  have hbad := density_weighted_markov ref (p θ₀) A hp₀ hA (e * d)
    (mul_ne_zero he0 hd0) (ENNReal.mul_ne_top het hdt)
  have hbadδ : (ref.withDensity (p θ₀)) {x | e * d * p θ₀ x < A x} ≤ δ := by
    apply hbad.trans
    rw [lintegral_mixture_likelihood μ ref p hp hnorm B]
    exact (ENNReal.div_le_iff (mul_ne_zero he0 hd0) (ENNReal.mul_ne_top het hdt)).mpr hmass
  have hgood : 1 - δ ≤ (ref.withDensity (p θ₀)) {x | A x ≤ e * d * p θ₀ x} := by
    have hb : MeasurableSet {x | e * d * p θ₀ x < A x} :=
      measurableSet_lt (measurable_const.mul hp₀) hA
    have hcompl := prob_compl_eq_one_sub (μ := ref.withDensity (p θ₀)) hb
    have hsub := tsub_le_tsub_left hbadδ 1
    rw [← hcompl] at hsub
    simpa only [Set.compl_ofPred, not_lt] using hsub
  apply hgood.trans (measure_mono ?_)
  intro x hx
  change A x ≤ e * d * p θ₀ x at hx
  change A x * F x ≤ e * p θ₀ x * _
  calc
    A x * F x ≤ (e * d * p θ₀ x) * F x := mul_le_mul hx le_rfl zero_le zero_le
    _ = (e * p θ₀ x) * (d * F x) := by ring
    _ ≤ _ := mul_le_mul le_rfl (hdom x) zero_le zero_le

/-- A likelihood-independent geometric measure comparison implies Proposition 1's
statistical event for every normalized jointly measurable model. -/
theorem likelihood_ratio_event_of_measure_domination {Θ Z Ω : Type*}
    [MeasurableSpace Θ] [MeasurableSpace Z] [MeasurableSpace Ω]
    (μ : Measure Θ) [SFinite μ] (ν : Measure Z) (ref : Measure Ω) [SFinite ref]
    (p : Θ → Ω → ℝ≥0∞) (hp : Measurable (Function.uncurry p))
    (hnorm : ∀ θ, IsProbabilityMeasure (ref.withDensity (p θ)))
    (θ₀ : Θ) (B C : Set Θ) (Φ : Z → Θ) (hΦ : Measurable Φ)
    (e d δ : ℝ≥0∞) (he0 : e ≠ 0) (het : e ≠ ⊤) (hd0 : d ≠ 0) (hdt : d ≠ ⊤)
    (hmass : μ B ≤ δ * (e * d))
    (hdom : d • ν.map Φ ≤ μ.restrict C) :
    1 - δ ≤ (ref.withDensity (p θ₀))
      {x | (∫⁻ θ in B, p θ x ∂μ) * (∫⁻ z, p (Φ z) x ∂ν) ≤
        e * p θ₀ x * ∫⁻ θ in C, p θ x ∂μ} := by
  apply likelihood_ratio_event_of_geometry μ ref p hp hnorm θ₀ B C _
    e d δ he0 het hd0 hdt hmass
  intro x
  have h := lintegral_mono' hdom (le_refl (fun θ => p θ x))
  rw [lintegral_smul_measure, lintegral_map hp.of_uncurry_right hΦ] at h
  exact h

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop1GaussianVolume -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal Pointwise

namespace BosonicLearn.Prop5

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Haar scaling of a radial Gaussian, with no normalization constants to compute. -/
theorem gaussian_scaled_mass (μ : Measure E) [μ.IsAddHaarMeasure]
    (a s : ℝ) (hs : 0 < s) :
    (∫⁻ x : E, ENNReal.ofReal (Real.exp (-a * ‖x‖ ^ 2 / s ^ 2)) ∂μ) =
      ENNReal.ofReal (s ^ Module.finrank ℝ E) *
        ∫⁻ x : E, ENNReal.ofReal (Real.exp (-a * ‖x‖ ^ 2)) ∂μ := by
  have hf : Measurable (fun x : E => ENNReal.ofReal (Real.exp (-a * ‖x‖^2))) := by fun_prop
  have h := lintegral_map (μ := μ) hf
    (show Measurable (fun x : E => s⁻¹ • x) from by fun_prop)
  rw [Measure.map_addHaar_smul μ (inv_ne_zero hs.ne'), lintegral_smul_measure] at h
  rw [inv_pow, inv_inv, abs_of_nonneg (pow_nonneg hs.le _)] at h
  simp only [smul_eq_mul] at h
  rw [h]
  apply lintegral_congr
  intro x
  congr 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), mul_pow]
  ring

/-- A Euclidean small ball has volume at most a scaled Gaussian partition function.
The estimate avoids any formula for the volume of the unit ball. -/
theorem gaussian_small_ball_volume (μ : Measure E) [μ.IsAddHaarMeasure]
    (a s R : ℝ) (ha : 0 ≤ a) (hs : 0 < s) :
    μ {x : E | ‖x‖ ^ 2 ≤ R} ≤
      ENNReal.ofReal (Real.exp (a * R / s ^ 2)) *
        ENNReal.ofReal (s ^ Module.finrank ℝ E) *
          ∫⁻ x : E, ENNReal.ofReal (Real.exp (-a * ‖x‖ ^ 2)) ∂μ := by
  calc
    _ = ∫⁻ x in {x : E | ‖x‖ ^ 2 ≤ R}, (1 : ℝ≥0∞) ∂μ := by simp
    _ ≤ ∫⁻ x in {x : E | ‖x‖ ^ 2 ≤ R},
        ENNReal.ofReal (Real.exp (a * R / s ^ 2)) *
          ENNReal.ofReal (Real.exp (-a * ‖x‖ ^ 2 / s ^ 2)) ∂μ := by
      apply setLIntegral_mono (by fun_prop)
      intro x hx
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      apply ENNReal.one_le_ofReal.mpr
      apply Real.one_le_exp_iff.mpr
      have hmul := mul_le_mul_of_nonneg_left hx ha
      rw [← add_div]
      apply div_nonneg _ (sq_nonneg s)
      linarith
    _ ≤ ∫⁻ x : E, ENNReal.ofReal (Real.exp (a * R / s ^ 2)) *
          ENNReal.ofReal (Real.exp (-a * ‖x‖ ^ 2 / s ^ 2)) ∂μ :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop), gaussian_scaled_mass μ a s hs, mul_assoc]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The same scaling identity for any continuous linear image norm. -/
theorem gaussian_scaled_mass_linear (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : E →L[ℝ] F) (a s : ℝ) (hs : 0 < s) :
    (∫⁻ x : E, ENNReal.ofReal (Real.exp (-a * ‖L x‖ ^ 2 / s ^ 2)) ∂μ) =
      ENNReal.ofReal (s ^ Module.finrank ℝ E) *
        ∫⁻ x : E, ENNReal.ofReal (Real.exp (-a * ‖L x‖ ^ 2)) ∂μ := by
  have hf : Measurable (fun x : E => ENNReal.ofReal (Real.exp (-a * ‖L x‖^2))) := by
    exact (Real.continuous_exp.comp ((L.continuous.norm.pow 2).const_mul (-a))).measurable.ennreal_ofReal
  have h := lintegral_map (μ := μ) hf
    (show Measurable (fun x : E => s⁻¹ • x) from by fun_prop)
  rw [Measure.map_addHaar_smul μ (inv_ne_zero hs.ne'), lintegral_smul_measure] at h
  rw [inv_pow, inv_inv, abs_of_nonneg (pow_nonneg hs.le _)] at h
  simp only [smul_eq_mul] at h
  rw [h]
  apply lintegral_congr
  intro x
  congr 2
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), mul_pow]
  ring

/-- A translated ellipsoid has volume bounded by a Gaussian partition function. -/
theorem gaussian_small_ball_volume_linear (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : E →L[ℝ] F) (x₀ : E) (a s R : ℝ) (ha : 0 ≤ a) (hs : 0 < s) :
    μ {x : E | ‖L (x - x₀)‖ ^ 2 ≤ R} ≤
      ENNReal.ofReal (Real.exp (a * R / s ^ 2)) *
        ENNReal.ofReal (s ^ Module.finrank ℝ E) *
          ∫⁻ x : E, ENNReal.ofReal (Real.exp (-a * ‖L x‖ ^ 2)) ∂μ := by
  have htranslate : μ {x : E | ‖L (x - x₀)‖ ^ 2 ≤ R} =
      μ {x : E | ‖L x‖ ^ 2 ≤ R} := by
    simpa only [Set.preimage_ofPred_eq, sub_eq_add_neg] using
      measure_preimage_add_right μ (-x₀) {x : E | ‖L x‖ ^ 2 ≤ R}
  rw [htranslate]
  have hq : Measurable (fun x : E => ‖L x‖) := L.continuous.norm.measurable
  calc
    _ = ∫⁻ x in {x : E | ‖L x‖ ^ 2 ≤ R}, (1 : ℝ≥0∞) ∂μ := by simp
    _ ≤ ∫⁻ x in {x : E | ‖L x‖ ^ 2 ≤ R},
        ENNReal.ofReal (Real.exp (a * R / s ^ 2)) *
          ENNReal.ofReal (Real.exp (-a * ‖L x‖ ^ 2 / s ^ 2)) ∂μ := by
      apply setLIntegral_mono (by fun_prop)
      intro x hx
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      apply ENNReal.one_le_ofReal.mpr
      apply Real.one_le_exp_iff.mpr
      have hmul := mul_le_mul_of_nonneg_left hx ha
      rw [← add_div]
      apply div_nonneg _ (sq_nonneg s)
      linarith
    _ ≤ ∫⁻ x : E, ENNReal.ofReal (Real.exp (a * R / s ^ 2)) *
          ENNReal.ofReal (Real.exp (-a * ‖L x‖ ^ 2 / s ^ 2)) ∂μ :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop), gaussian_scaled_mass_linear μ L a s hs,
        mul_assoc]

/-- Haar volume scales in the dimension for balls of a linear-image norm. -/
theorem linear_ball_volume (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : E →L[ℝ] F) (s r : ℝ) (hs : 0 < s) :
    μ {x : E | ‖L x‖ ≤ s * r} = ENNReal.ofReal (s ^ Module.finrank ℝ E) *
      μ {x : E | ‖L x‖ ≤ r} := by
  have heq : s • {x : E | ‖L x‖ ≤ r} = {x : E | ‖L x‖ ≤ s * r} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change ‖L (s • y)‖ ≤ s * r
      rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
      exact mul_le_mul_of_nonneg_left hy hs.le
    · intro hx
      refine ⟨s⁻¹ • x, ?_, ?_⟩
      · change ‖L (s⁻¹ • x)‖ ≤ r
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
        apply (inv_mul_le_iff₀ hs).mpr
        exact hx
      · change s • (s⁻¹ • x) = x
        rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  rw [← heq, Measure.addHaar_smul, abs_of_nonneg (pow_nonneg hs.le _)]

end BosonicLearn.Prop5

end

/- Local helper source: Definitions.Def_BosonicLearn_tracelessGUE -/
section
open MeasureTheory

namespace BosonicLearn

/-- Unnormalized traceless-GUE density in the convention of Definition 6 and
Equation (32) of Chen--Mele--Mele--Preskill, arXiv:2609.26705. Its covariance
on the real Hilbert space of traceless Hermitian matrices is `2/n` times the
identity. The arbitrary normalization of additive Haar measure cancels below. -/
noncomputable def tracelessGUEWeight (n : ℕ) : Measure (Herm0 n) :=
  (Measure.addHaar : Measure (Herm0 n)).withDensity
    (fun X => ENNReal.ofReal (Real.exp (-(n / 4 : ℝ) *
      WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) ^ 2)))

/-- The normalized, unconditioned traceless Gaussian unitary ensemble.
This is the law of `G - (Tr G/n) I` when `G` has diagonal variance `2/n`
and independent real/imaginary off-diagonal variances `1/n`.
The equivalence with independent coordinates is mathematical background;
this definition fixes the density directly. -/
noncomputable def tracelessGUE (n : ℕ) : Measure (Herm0 n) :=
  ProbabilityTheory.cond (tracelessGUEWeight n) Set.univ

end BosonicLearn

end

/- Local helper source: Solutions.Prop5Prior -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace BosonicLearn.Prop5

/-- Conditioning on a superset of a good event cannot increase its failure probability. -/
theorem cond_superset_compl_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G S : Set Ω) (hG : MeasurableSet G) (hS : MeasurableSet S) (hGS : G ⊆ S) :
    ProbabilityTheory.cond μ S Gᶜ ≤ μ Gᶜ := by
  by_cases hzero : μ S = 0
  · rw [cond_eq_zero_of_meas_eq_zero hzero]
    simp
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ S) := cond_isProbabilityMeasure hzero
  rw [prob_compl_eq_one_sub hG, prob_compl_eq_one_sub hG]
  apply tsub_le_tsub_left
  rw [cond_apply hS, Set.inter_eq_right.mpr hGS]
  calc
    μ G = 1 * μ G := (one_mul _).symm
    _ ≤ (μ S)⁻¹ * μ G := mul_le_mul' (ENNReal.one_le_inv.mpr prob_le_one) le_rfl

/-- The same conditioning comparison for an arbitrary finite unnormalized law. -/
theorem cond_superset_compl_le_normalized {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) (hfin : m Set.univ ≠ ⊤)
    (G S : Set Ω) (hG : MeasurableSet G) (hS : MeasurableSet S) (hGS : G ⊆ S) :
    ProbabilityTheory.cond m S Gᶜ ≤ ProbabilityTheory.cond m Set.univ Gᶜ := by
  by_cases hzero : m Set.univ = 0
  · have hm : m = 0 := Measure.measure_univ_eq_zero.mp hzero
    simp [hm, ProbabilityTheory.cond]
  have : IsProbabilityMeasure (ProbabilityTheory.cond m Set.univ) :=
    cond_isProbabilityMeasure_of_finite hzero hfin
  have h := cond_superset_compl_le (ProbabilityTheory.cond m Set.univ) G S hG hS hGS
  have heq : ProbabilityTheory.cond (ProbabilityTheory.cond m Set.univ) S = ProbabilityTheory.cond m S := by
    simpa using cond_cond_eq_cond_inter' MeasurableSet.univ hS hfin
  simpa only [heq] using h

/-- Local abbreviation for the reusable unconditioned Gaussian density. -/
noncomputable abbrev gueWeight (n : ℕ) : Measure (Herm0 n) := tracelessGUEWeight n

/-- The prior is exactly the traceless Gaussian density conditioned on `Gsupp`. -/
theorem priorMu_eq_cond_gueWeight (n : ℕ) :
    priorMu n = ProbabilityTheory.cond (gueWeight n) (Gsupp n) := by
  have hs : MeasurableSet (Gsupp n) := by
    have hc : Continuous fun X : Herm0 n =>
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ := by
      apply Continuous.norm
      exact (LinearMap.continuous_of_finiteDimensional
        ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)).comp
          continuous_subtype_val
    simpa [Gsupp, WHMultiplicativity.schattenNorm] using
      measurableSet_le hc.measurable measurable_const
  unfold priorMu ProbabilityTheory.cond gueWeight tracelessGUEWeight
  dsimp only
  rw [← restrict_withDensity hs, Measure.restrict_apply_univ]

/-- The prior's bad-set mass is no larger than the unconditioned traceless-GUE
bad-set mass. No loss in the exponential rate is needed. -/
theorem prior_bad_le_gue_bad (n : ℕ) (hfin : gueWeight n Set.univ ≠ ⊤) :
    priorMu n (Ggood n)ᶜ ≤ ProbabilityTheory.cond (gueWeight n) Set.univ (Ggood n)ᶜ := by
  have hc : Continuous fun X : Herm0 n =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ := by
    apply Continuous.norm
    exact (LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)).comp
        continuous_subtype_val
  have hG : MeasurableSet (Ggood n) := by
    simpa [Ggood, WHMultiplicativity.schattenNorm] using
      measurableSet_le hc.measurable measurable_const
  have hS : MeasurableSet (Gsupp n) := by
    simpa [Gsupp, WHMultiplicativity.schattenNorm] using
      measurableSet_le hc.measurable measurable_const
  rw [priorMu_eq_cond_gueWeight]
  apply cond_superset_compl_le_normalized (gueWeight n) hfin (Ggood n) (Gsupp n) hG hS
  intro X hX
  exact le_trans hX (by norm_num : (3 : ℝ) ≤ 4)


/-- A radial Gaussian is integrable for any finite-dimensional real norm. -/
theorem integrable_exp_neg_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : Measure E) [m.IsAddHaarMeasure] (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : E => Real.exp (-b * ‖x‖ ^ 2)) m := by
  rcases subsingleton_or_nontrivial E with hsub | hnon
  · have : CompactSpace E := ⟨Set.finite_univ.isCompact⟩
    have : IsFiniteMeasure m := ⟨isCompact_univ.measure_lt_top⟩
    have hconst : (fun x : E => Real.exp (-b * ‖x‖ ^ 2)) = fun _ => (1 : ℝ) := by
      funext x
      rw [Subsingleton.elim x 0]
      simp
    rw [hconst]
    exact integrable_const 1
  · apply (integrable_fun_norm_addHaar m (f := fun r : ℝ => Real.exp (-b * r ^ 2))).mpr
    simpa only [smul_eq_mul, Real.rpow_natCast] using
      integrableOn_rpow_mul_exp_neg_mul_sq hb
        (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _))


/-- Frobenius norm in the published Schatten convention. -/
theorem schatten_two_eq_sqrt (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2 X = Real.sqrt (∑ i, ∑ j, ‖X j i‖ ^ 2) := by
  unfold WHMultiplicativity.schattenNorm
  rw [if_neg (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [h2]
  have hfun : (fun x : ℝ => x ^ ((2 : ℝ) / 2)) = fun x => x := by
    funext x
    rw [div_self (by norm_num), Real.rpow_one]
  rw [hfun, cfc_id' ℝ (X.conjTranspose * X)
    (by rw [← Matrix.star_eq_conjTranspose]; exact IsSelfAdjoint.star_mul_self X)]
  rw [Real.sqrt_eq_rpow]
  congr 1
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.conj_mul', ← Complex.ofReal_pow]


/-- The entrywise supremum norm is bounded by the Frobenius norm. -/
theorem norm_le_schatten_two (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖fun i j => X i j‖ ≤ WHMultiplicativity.schattenNorm 2 X := by
  rw [schatten_two_eq_sqrt]
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro j
  have hs : (0 : ℝ) ≤ ∑ a, ∑ b, ‖X b a‖ ^ 2 := by positivity
  have h1 : ‖X i j‖ ^ 2 ≤ ∑ b, ‖X b j‖ ^ 2 :=
    Finset.single_le_sum (fun b _ => sq_nonneg (‖X b j‖)) (Finset.mem_univ i)
  have h2 : (∑ b, ‖X b j‖ ^ 2) ≤ ∑ a, ∑ b, ‖X b a‖ ^ 2 :=
    Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg (‖X b a‖))) (Finset.mem_univ j)
  nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg (∑ a, ∑ b, ‖X b a‖ ^ 2), norm_nonneg (X i j)]

/-- The unconditioned traceless-GUE density has finite mass. -/
theorem gueWeight_finite (n : ℕ) (hn : 0 < n) : gueWeight n Set.univ ≠ ⊤ := by
  let : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → ℂ))
  let : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedSpace ℝ (Fin n → Fin n → ℂ))
  have hi := integrable_exp_neg_norm_sq (Measure.addHaar : Measure (Herm0 n))
    (n / 4 : ℝ) (by positivity)
  let f : Herm0 n → ℝ := fun X => Real.exp (-(n / 4 : ℝ) *
    WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) ^ 2)
  have hcont : Continuous f := by
    dsimp only [f]
    simp_rw [schatten_two_eq_sqrt]
    have he : ∀ i j : Fin n, Continuous (fun X : Herm0 n => (X : Matrix (Fin n) (Fin n) ℂ) i j) :=
      fun i j => (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
    apply Real.continuous_exp.comp
    apply Continuous.mul continuous_const
    apply Continuous.pow
    apply Real.continuous_sqrt.comp
    apply continuous_finsetSum
    intro i hi
    apply continuous_finsetSum
    intro j hj
    exact (he j i).norm.pow 2
  have hint : Integrable f (Measure.addHaar : Measure (Herm0 n)) := by
    apply hi.mono' hcont.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro X
    dsimp only [f]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hX := norm_le_schatten_two n (X : Matrix (Fin n) (Fin n) ℂ)
    have hF : 0 ≤ WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) := by
      rw [schatten_two_eq_sqrt]
      positivity
    have hb : (0 : ℝ) ≤ n / 4 := by positivity
    change ‖X‖ ≤ WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) at hX
    have hsq : ‖X‖ ^ 2 ≤ WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) ^ 2 := by
      nlinarith [norm_nonneg X]
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_left hsq hb)
  have hf : ∀ᵐ X ∂(Measure.addHaar : Measure (Herm0 n)), 0 ≤ f X :=
    Filter.Eventually.of_forall (fun X => (Real.exp_pos _).le)
  have hfin := (hasFiniteIntegral_iff_ofReal hf).mp hint.hasFiniteIntegral
  unfold gueWeight tracelessGUEWeight
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hfin.ne


/-- The Gaussian weight has positive mass in every dimension. -/
theorem gueWeight_pos (n : ℕ) : 0 < gueWeight n Set.univ := by
  let f : Herm0 n → ℝ≥0∞ := fun X => ENNReal.ofReal (Real.exp (-(n / 4 : ℝ) *
    WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) ^ 2))
  have hf : Measurable f := by
    dsimp only [f]
    simp_rw [schatten_two_eq_sqrt]
    apply Continuous.measurable
    apply ENNReal.continuous_ofReal.comp
    apply Real.continuous_exp.comp
    apply Continuous.mul continuous_const
    apply Continuous.pow
    apply Real.continuous_sqrt.comp
    apply continuous_finsetSum
    intro i hi
    apply continuous_finsetSum
    intro j hj
    have he : Continuous (fun X : Herm0 n => (X : Matrix (Fin n) (Fin n) ℂ) j i) :=
      (continuous_apply i).comp ((continuous_apply j).comp continuous_subtype_val)
    exact he.norm.pow 2
  have hpos : ∀ X, 0 < f X := fun X => ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hsupp : Function.support f = Set.univ := by
    ext X
    simp [Function.mem_support, (hpos X).ne']
  unfold gueWeight tracelessGUEWeight
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change 0 < ∫⁻ X, f X ∂(Measure.addHaar : Measure (Herm0 n))
  rw [lintegral_pos_iff_support hf, hsupp]
  exact isOpen_univ.measure_pos _ ⟨0, Set.mem_univ _⟩

/-- The normalized unconditioned density is a genuine probability law. -/
theorem gue_probability (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (ProbabilityTheory.cond (gueWeight n) Set.univ) :=
  cond_isProbabilityMeasure_of_finite (gueWeight_pos n).ne' (gueWeight_finite n hn)

/-- The conditioning bridge with normalization discharged. -/
theorem prior_bad_le_gue_bad_of_pos (n : ℕ) (hn : 0 < n) :
    priorMu n (Ggood n)ᶜ ≤ ProbabilityTheory.cond (gueWeight n) Set.univ (Ggood n)ᶜ :=
  prior_bad_le_gue_bad n (gueWeight_finite n hn)

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5GUEGeometry -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

section Rayleigh
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The supremum of Rayleigh quotients, including zero. On a nonzero traceless
Hermitian operator this is its largest eigenvalue. -/
noncomputable def upperRayleigh (T : E →L[ℂ] E) : ℝ := ⨆ v, T.rayleighQuotient v

lemma bddAbove_rayleigh (T : E →L[ℂ] E) : BddAbove (Set.range T.rayleighQuotient) :=
  ⟨‖T‖, fun _ ⟨v, hv⟩ => hv ▸ (le_abs_self _).trans (T.rayleighQuotient_le_norm v)⟩

lemma rayleigh_le_upperRayleigh (T : E →L[ℂ] E) (v : E) :
    T.rayleighQuotient v ≤ upperRayleigh T := le_ciSup (bddAbove_rayleigh T) v

lemma upperRayleigh_nonneg (T : E →L[ℂ] E) : 0 ≤ upperRayleigh T := by
  simpa using rayleigh_le_upperRayleigh T 0

lemma upperRayleigh_le_norm (T : E →L[ℂ] E) : upperRayleigh T ≤ ‖T‖ := by
  apply ciSup_le
  intro v
  exact (le_abs_self _).trans (T.rayleighQuotient_le_norm v)

lemma upperRayleigh_le_add_norm_sub (T S : E →L[ℂ] E) :
    upperRayleigh T ≤ upperRayleigh S + ‖T - S‖ := by
  apply ciSup_le
  intro v
  have heq : T.rayleighQuotient v = S.rayleighQuotient v + (T - S).rayleighQuotient v := by
    rw [← ContinuousLinearMap.rayleighQuotient_add]
    congr 1
    abel
  rw [heq]
  exact add_le_add (rayleigh_le_upperRayleigh S v)
    ((le_abs_self _).trans ((T - S).rayleighQuotient_le_norm v))

/-- Rayleigh maxima are 1-Lipschitz for operator norm. -/
theorem upperRayleigh_lipschitz (T S : E →L[ℂ] E) :
    |upperRayleigh T - upperRayleigh S| ≤ ‖T - S‖ := by
  have h1 := upperRayleigh_le_add_norm_sub T S
  have h2 := upperRayleigh_le_add_norm_sub S T
  rw [norm_sub_rev S T] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Both signs of the Rayleigh maximum control a self-adjoint operator norm. -/
theorem norm_le_max_upperRayleigh (T : E →L[ℂ] E) (hT : T.IsSymmetric) :
    ‖T‖ ≤ max (upperRayleigh T) (upperRayleigh (-T)) := by
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  apply ciSup_le
  intro v
  have h1 := rayleigh_le_upperRayleigh T v
  have h2 := rayleigh_le_upperRayleigh (-T) v
  rw [ContinuousLinearMap.rayleighQuotient_neg_apply] at h2
  exact abs_le.mpr ⟨by linarith [le_max_right (upperRayleigh T) (upperRayleigh (-T))],
    h1.trans (le_max_left _ _)⟩

end Rayleigh


open scoped Matrix.Norms.Frobenius in
/-- The published Schatten 2-norm agrees with the matrix Frobenius norm. -/
theorem schatten_two_eq_frobenius (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2 X = ‖X‖ := by
  rw [schatten_two_eq_sqrt, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  rw [Finset.sum_comm]
  simp only [Real.rpow_two]

open scoped Matrix.Norms.Frobenius in
/-- Euclidean operator norm is bounded by the Frobenius norm. -/
theorem operator_norm_le_schatten_two (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖ ≤ WHMultiplicativity.schattenNorm 2 X := by
  rw [schatten_two_eq_frobenius]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg X)
  intro v
  have h := Matrix.frobenius_norm_mul X (Matrix.replicateCol Unit (WithLp.ofLp v))
  rw [← Matrix.replicateCol_mulVec, Matrix.frobenius_norm_replicateCol,
    Matrix.frobenius_norm_replicateCol] at h
  exact h

/-- The largest Rayleigh quotient is 1-Lipschitz in the Frobenius metric. -/
theorem matrix_upperRayleigh_lipschitz (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    |upperRayleigh (Matrix.toEuclideanCLM (𝕜 := ℂ) X) -
      upperRayleigh (Matrix.toEuclideanCLM (𝕜 := ℂ) Y)| ≤
      WHMultiplicativity.schattenNorm 2 (X - Y) := by
  refine (upperRayleigh_lipschitz _ _).trans ?_
  rw [← map_sub]
  exact operator_norm_le_schatten_two n (X - Y)

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5GUEMax -/
section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal

noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 1000000

/-- Finite maxima preserve integrability. -/
lemma integrable_finset_sup' {Ω T : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : T → Ω → ℝ) (hX : ∀ t, Integrable (X t) μ)
    (s : Finset T) (hs : s.Nonempty) :
    Integrable (fun ω => s.sup' hs (fun t => X t ω)) μ := by
  have h := Finset.sup'_induction hs X (p := fun f => Integrable f μ)
    (fun _ ha _ hb => ha.sup hb) (fun t _ => hX t)
  convert h using 1
  funext ω
  exact (Finset.sup'_apply hs X ω).symm

/-- On a separable parameter space, a continuous process dominated by an integrable
function has its ordinary expected supremum below the finite-marginal expected supremum.
This supplies the analytic bridge needed to apply abstract Gaussian comparison to Rayleigh maxima. -/
theorem integral_iSup_le_processESup {Ω T : Type} [MeasurableSpace Ω]
    [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
    (μ : Measure Ω) (X : T → Ω → ℝ)
    (hX : ∀ t, AEStronglyMeasurable (X t) μ)
    (hcont : ∀ ω, Continuous (fun t => X t ω))
    (g : Ω → ℝ) (hg : Integrable g μ) (hbound : ∀ t ω, ‖X t ω‖ ≤ g ω) :
    ((∫ ω, (⨆ t, X t ω) ∂μ : ℝ) : EReal) ≤
      HighDimProb.RandomProcesses.processESup μ X := by
  classical
  let d : ℕ → T := TopologicalSpace.denseSeq T
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq T
  let s : ℕ → Finset T := fun n => (Finset.range (n+1)).image d
  have hs : ∀ n, (s n).Nonempty := fun n =>
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n)).image d
  let f : ℕ → Ω → ℝ := fun n ω => (s n).sup' (hs n) (fun t => X t ω)
  have hi : ∀ t, Integrable (X t) μ := fun t => hg.mono' (hX t) (ae_of_all μ (hbound t))
  have hfi : ∀ n, Integrable (f n) μ := fun n => integrable_finset_sup' μ X hi (s n) (hs n)
  have hfb : ∀ n ω, ‖f n ω‖ ≤ g ω := by
    intro n ω
    obtain ⟨t, _, ht⟩ := Finset.exists_mem_eq_sup' (hs n) (fun t => X t ω)
    change ‖(s n).sup' (hs n) (fun t => X t ω)‖ ≤ g ω
    rw [ht]
    exact hbound t ω
  have hmono : ∀ ω, Monotone (fun n => f n ω) := by
    intro ω n m hnm
    exact Finset.sup'_mono _ (Finset.image_subset_image
      (Finset.range_mono (Nat.add_le_add_right hnm 1))) (hs n)
  have hb : ∀ ω, BddAbove (Set.range (fun n => f n ω)) := fun ω =>
    ⟨g ω, fun _ ⟨n, hn⟩ => hn ▸ (le_abs_self _).trans (hfb n ω)⟩
  have hBX : ∀ ω, BddAbove (Set.range (fun t => X t ω)) := fun ω =>
    ⟨g ω, fun _ ⟨t, ht⟩ => ht ▸ (le_abs_self _).trans (hbound t ω)⟩
  have heq : ∀ ω, (⨆ n, f n ω) = ⨆ t, X t ω := by
    intro ω
    apply le_antisymm
    · apply ciSup_le
      intro n
      exact Finset.sup'_le (hs n) _ (fun t _ => le_ciSup (hBX ω) t)
    · apply ciSup_le
      intro t
      refine hd.induction_on (p := fun t => X t ω ≤ ⨆ n, f n ω) t
        (isClosed_le (hcont ω) continuous_const) ?_
      intro k
      apply (Finset.le_sup' (fun t => X t ω) ?_).trans (le_ciSup (hb ω) k)
      exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), rfl⟩
  have hlim : ∀ ω, Tendsto (fun n => f n ω) atTop (𝓝 (⨆ t, X t ω)) := by
    intro ω
    rw [← heq ω]
    exact tendsto_atTop_ciSup (hmono ω) (hb ω)
  have hiLim := tendsto_integral_of_dominated_convergence g
    (fun n => (hfi n).aestronglyMeasurable) hg (fun n => ae_of_all μ (hfb n))
    (ae_of_all μ hlim)
  apply le_of_tendsto' ((continuous_coe_real_ereal.tendsto _).comp hiLim)
  intro n
  exact le_iSup (fun s : {s : Finset T // s.Nonempty} =>
    ((∫ ω, s.1.sup' s.2 (fun t => X t ω) ∂μ : ℝ) : EReal)) ⟨s n, hs n⟩

/-- Any integrable envelope bounds the finite-marginal expected supremum. -/
theorem processESup_le_integral {Ω T : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : T → Ω → ℝ) (hX : ∀ t, Integrable (X t) μ)
    (g : Ω → ℝ) (hg : Integrable g μ) (hbound : ∀ t ω, X t ω ≤ g ω) :
    HighDimProb.RandomProcesses.processESup μ X ≤ ((∫ ω, g ω ∂μ : ℝ) : EReal) := by
  apply iSup_le
  intro s
  apply EReal.coe_le_coe_iff.mpr
  apply integral_mono (integrable_finset_sup' μ X hX s.1 s.2) hg
  intro ω
  exact Finset.sup'_le s.2 _ (fun t _ => hbound t ω)

/-- A directly usable version of Sudakov--Fernique for continuous processes.
It controls the usual real expected maximum by an integrable comparison envelope. -/
theorem expected_sup_le_of_gaussian_comparison {Ω T : Type} [MeasurableSpace Ω]
    [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : T → Ω → ℝ)
    (hXG : IsGaussianProcess X μ) (hYG : IsGaussianProcess Y μ)
    (hXmean : ∀ t, ∫ ω, X t ω ∂μ = 0) (hYmean : ∀ t, ∫ ω, Y t ω ∂μ = 0)
    (hinc : ∀ t s, ∫ ω, (X t ω - X s ω)^2 ∂μ ≤ ∫ ω, (Y t ω - Y s ω)^2 ∂μ)
    (hX : ∀ t, AEStronglyMeasurable (X t) μ)
    (hcont : ∀ ω, Continuous (fun t => X t ω))
    (gX : Ω → ℝ) (hgX : Integrable gX μ) (hbX : ∀ t ω, ‖X t ω‖ ≤ gX ω)
    (hY : ∀ t, Integrable (Y t) μ)
    (gY : Ω → ℝ) (hgY : Integrable gY μ) (hbY : ∀ t ω, Y t ω ≤ gY ω) :
    (∫ ω, (⨆ t, X t ω) ∂μ) ≤ ∫ ω, gY ω ∂μ := by
  apply EReal.coe_le_coe_iff.mp
  exact (integral_iSup_le_processESup μ X hX hcont gX hgX hbX).trans
    ((HighDimProb.RandomProcesses.sudakov_fernique μ X Y hXG hYG hXmean hYmean hinc).trans
      (processESup_le_integral μ Y hY gY hgY hbY))

section RayleighIndex
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Unit vectors together with a distinguished zero vector. This compact index space
represents the nonnegative Rayleigh maximum, including the zero-dimensional case. -/
abbrev RayleighIndex (E : Type) [NormedAddCommGroup E] :=
  Metric.sphere (0 : E) 1 ⊕ Unit

/-- The Rayleigh process on unit vectors, extended by zero at its distinguished point. -/
def indexedRayleigh (T : E →L[ℂ] E) : RayleighIndex E → ℝ :=
  Sum.elim (fun v => T.rayleighQuotient v) (fun _ => 0)

lemma indexedRayleigh_norm_le (T : E →L[ℂ] E) (v : RayleighIndex E) :
    ‖indexedRayleigh T v‖ ≤ ‖T‖ := by
  cases v with
  | inl v => exact T.rayleighQuotient_le_norm v
  | inr v => simp [indexedRayleigh]

lemma continuous_indexedRayleigh (T : E →L[ℂ] E) : Continuous (indexedRayleigh T) := by
  apply continuous_sum_dom.mpr
  constructor
  · have heq : (indexedRayleigh T ∘ Sum.inl) =
        fun v : Metric.sphere (0 : E) 1 => T.reApplyInnerSelf v := by
      funext v
      simp [indexedRayleigh, ContinuousLinearMap.rayleighQuotient]
    rw [heq]
    exact T.reApplyInnerSelf_continuous.comp continuous_subtype_val
  · exact continuous_const

lemma iSup_indexedRayleigh (T : E →L[ℂ] E) :
    (⨆ v : RayleighIndex E, indexedRayleigh T v) = upperRayleigh T := by
  have hb : BddAbove (Set.range (indexedRayleigh T)) :=
    ⟨‖T‖, fun _ ⟨v, hv⟩ => hv ▸ (le_abs_self _).trans (indexedRayleigh_norm_le T v)⟩
  apply le_antisymm
  · apply ciSup_le
    intro v
    cases v with
    | inl v => exact rayleigh_le_upperRayleigh T v
    | inr v => exact upperRayleigh_nonneg T
  · apply ciSup_le
    intro v
    by_cases hv : v = 0
    · simpa [hv, indexedRayleigh] using le_ciSup hb (Sum.inr ())
    · have hmem : T.rayleighQuotient v ∈ T.rayleighQuotient '' ({0}ᶜ : Set E) :=
        ⟨v, hv, rfl⟩
      rw [T.image_rayleigh_eq_image_rayleigh_sphere (show (0 : ℝ) < 1 by norm_num)] at hmem
      obtain ⟨w, hw, heq⟩ := hmem
      simpa [indexedRayleigh, heq] using le_ciSup hb (Sum.inl ⟨w, hw⟩)

lemma continuous_rayleigh_at (v : E) :
    Continuous (fun T : E →L[ℂ] E => T.rayleighQuotient v) := by
  have h : Continuous (fun T : E →L[ℂ] E => T v) := continuous_id.clm_apply continuous_const
  exact (RCLike.continuous_re.comp (h.inner continuous_const)).div_const _

/-- The operator maximum can be bounded using Gaussian comparison on the unit sphere
with its distinguished zero vector. Only an integrable operator-norm envelope is needed. -/
theorem expected_upperRayleigh_le_of_comparison {Ω : Type} [MeasurableSpace Ω]
    [SecondCountableTopology E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → E →L[ℂ] E)
    (Y : RayleighIndex E → Ω → ℝ)
    (hXG : IsGaussianProcess (fun v ω => indexedRayleigh (T ω) v) μ)
    (hYG : IsGaussianProcess Y μ)
    (hXm : ∀ v, ∫ ω, indexedRayleigh (T ω) v ∂μ = 0)
    (hYm : ∀ v, ∫ ω, Y v ω ∂μ = 0)
    (hinc : ∀ v w, ∫ ω, (indexedRayleigh (T ω) v - indexedRayleigh (T ω) w)^2 ∂μ ≤
      ∫ ω, (Y v ω - Y w ω)^2 ∂μ)
    (hT : Integrable (fun ω => ‖T ω‖) μ)
    (g : Ω → ℝ) (hg : Integrable g μ) (hYb : ∀ v ω, Y v ω ≤ g ω) :
    (∫ ω, upperRayleigh (T ω) ∂μ) ≤ ∫ ω, g ω ∂μ := by
  simpa only [iSup_indexedRayleigh] using expected_sup_le_of_gaussian_comparison μ
    (fun v ω => indexedRayleigh (T ω) v) Y hXG hYG hXm hYm hinc
    (fun v => (hXG.hasGaussianLaw_eval v).integrable.aestronglyMeasurable)
    (fun ω => continuous_indexedRayleigh (T ω))
    (fun ω => ‖T ω‖) hT (fun v ω => indexedRayleigh_norm_le (T ω) v)
    (fun v => (hYG.hasGaussianLaw_eval v).integrable) g hg hYb

/-- The linear comparison process used for the complex Gaussian Rayleigh process. -/
def indexedLinearComparison (c : ℝ) (g : E) : RayleighIndex E → ℝ :=
  Sum.elim (fun v => c * (inner ℂ g (v : E)).re) (fun _ => 0)

lemma indexedLinearComparison_le (c : ℝ) (hc : 0 ≤ c) (g : E) (v : RayleighIndex E) :
    indexedLinearComparison c g v ≤ c * ‖g‖ := by
  cases v with
  | inl v =>
      apply mul_le_mul_of_nonneg_left _ hc
      calc
        (inner ℂ g (v : E)).re ≤ ‖inner ℂ g (v : E)‖ := Complex.re_le_norm _
        _ ≤ ‖g‖ * ‖(v : E)‖ := norm_inner_le_norm _ _
        _ = ‖g‖ := by rw [norm_eq_of_mem_sphere v, mul_one]
  | inr v => exact mul_nonneg hc (norm_nonneg g)

end RayleighIndex

/-- The elementary second-moment bound for a real mean. -/
theorem integral_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    (∫ ω, f ω ∂μ) ≤ Real.sqrt (∫ ω, (f ω)^2 ∂μ) := by
  have hv := variance_nonneg f μ
  rw [variance_eq_sub hf] at hv
  have hsecond : 0 ≤ ∫ ω, (f ω)^2 ∂μ := integral_nonneg (fun ω => sq_nonneg _)
  have hsq := Real.sq_sqrt hsecond
  have hn := Real.sqrt_nonneg (∫ ω, (f ω)^2 ∂μ)
  simp only [Pi.pow_apply] at hv
  nlinarith

/-- The linear comparison envelope has mean at most `2√2` when its complex Gaussian
vector has total second moment at most `2n`. -/
theorem comparison_envelope_mean_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (Z : Ω → E)
    (hZ : MemLp (fun ω => ‖Z ω‖) 2 μ)
    (hsecond : (∫ ω, ‖Z ω‖^2 ∂μ) ≤ 2 * n) :
    (∫ ω, (2 / Real.sqrt n) * ‖Z ω‖ ∂μ) ≤ 2 * Real.sqrt 2 := by
  rw [integral_const_mul]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  calc
    (2 / Real.sqrt n) * (∫ ω, ‖Z ω‖ ∂μ) ≤
        (2 / Real.sqrt n) * Real.sqrt (2 * n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (integral_le_sqrt_integral_sq μ _ hZ).trans (Real.sqrt_le_sqrt hsecond)
    _ = 2 * Real.sqrt 2 := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp



section Projector
variable {ι : Type*} [Fintype ι]

/-- The rank-one projector encoded as a Euclidean vector of matrix entries. -/
def projectorVector (u : EuclideanSpace ℂ ι) : EuclideanSpace ℂ (ι × ι) :=
  WithLp.toLp 2 (fun ij => u ij.1 * star (u ij.2))

lemma inner_projectorVector (u v : EuclideanSpace ℂ ι) :
    inner ℂ (projectorVector u) (projectorVector v) =
      inner ℂ u v * star (inner ℂ u v) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, projectorVector,
    starRingEnd_apply, star_mul, star_star, star_sum]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma real_inner_projectorVector (u v : EuclideanSpace ℂ ι) :
    (inner ℂ (projectorVector u) (projectorVector v)).re = ‖inner ℂ u v‖^2 := by
  rw [inner_projectorVector, Complex.star_def, Complex.mul_conj,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]

lemma norm_projectorVector_sq (u : EuclideanSpace ℂ ι) :
    ‖projectorVector u‖^2 = ‖u‖^4 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  change (inner ℂ (projectorVector u) (projectorVector u)).re = _
  rw [real_inner_projectorVector, inner_self_eq_norm_sq_to_K]
  simp only [norm_pow, RCLike.norm_ofReal, abs_norm]
  ring

lemma projectorVector_dist_sq (u v : EuclideanSpace ℂ ι)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖projectorVector u - projectorVector v‖^2 = 2 * (1 - ‖inner ℂ u v‖^2) := by
  rw [norm_sub_sq (𝕜 := ℂ), norm_projectorVector_sq, norm_projectorVector_sq,
    ]
  change ‖u‖^4 - 2 * (inner ℂ (projectorVector u) (projectorVector v)).re + ‖v‖^4 = _
  rw [real_inner_projectorVector, hu, hv]
  ring

lemma unit_projector_increment_bound (u v : EuclideanSpace ℂ ι)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖projectorVector u - projectorVector v‖^2 ≤ 2 * ‖u-v‖^2 := by
  rw [projectorVector_dist_sq u v hu hv, norm_sub_sq (𝕜 := ℂ), hu, hv]
  have hre : (inner ℂ u v).re^2 ≤ ‖inner ℂ u v‖^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [sq_nonneg (inner ℂ u v).im]
  change 2 * (1 - ‖inner ℂ u v‖^2) ≤
    2 * (1^2 - 2 * (inner ℂ u v).re + 1^2)
  nlinarith [sq_nonneg (1 - (inner ℂ u v).re)]

/-- Matrix entries as a Euclidean vector; its norm is the Frobenius norm. -/
def matrixVector (A : Matrix ι ι ℂ) : EuclideanSpace ℂ (ι × ι) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

lemma inner_projector_matrixVector [DecidableEq ι] (A : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) :
    inner ℂ (projectorVector v) (matrixVector A) =
      inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) A v) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, projectorVector, matrixVector,
    starRingEnd_apply, star_mul, star_star, Matrix.ofLp_toEuclideanCLM,
    Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma rayleigh_unit_eq_real_inner_projector [DecidableEq ι]
    (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) A).rayleighQuotient v =
      (inner ℂ (projectorVector v) (matrixVector A)).re := by
  rw [inner_projector_matrixVector, ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, hv, one_pow, div_one]
  exact inner_re_symm (𝕜 := ℂ) _ _

lemma norm_matrixVector (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖matrixVector A‖ = WHMultiplicativity.schattenNorm 2 A := by
  rw [schatten_two_eq_sqrt, ← Real.sqrt_sq (norm_nonneg (matrixVector A)),
    EuclideanSpace.norm_sq_eq]
  congr 1
  simp only [matrixVector, WithLp.ofLp_toLp, Fintype.sum_prod_type]
  exact Finset.sum_comm

end Projector

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5GaussianDensity -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace BosonicLearn.Prop5

/-- An integrable product density is the density of the product measures. -/
theorem pi_withDensity_ofReal {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → E i → ℝ)
    (hf : ∀ i, Integrable (f i) (μ i)) (hn : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod_dep (fun i => (hf i).restrict))
    (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => hn i (x i))))]
  rw [integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg (hn i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hf i).restrict (ae_of_all _ (hn i))

/-- Transporting a density through a measurable equivalence composes it with the inverse. -/
theorem map_withDensity_equiv {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (e : E ≃ᵐ F) (f : E → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs), withDensity_apply _ hs,
    ← lintegral_indicator hs]
  rw [lintegral_map (show Measurable (s.indicator (fun y => f (e.symm y))) from
    (hf.comp e.symm.measurable).indicator hs) e.measurable]
  rw [← lintegral_indicator (e.measurable hs)]
  apply lintegral_congr
  intro x
  by_cases hx : e x ∈ s <;> simp [Set.indicator, hx]

/-- Independent real Gaussian coordinates have the product of their scalar densities. -/
theorem pi_gaussian_density {ι : Type*} [Fintype ι] (v : ℝ≥0) (hv : v ≠ 0) :
    Measure.pi (fun _ : ι => gaussianReal 0 v) =
      (volume : Measure (ι → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 v (x i))) := by
  simp_rw [gaussianReal_of_var_ne_zero _ hv]
  exact pi_withDensity_ofReal (fun _ => volume) (fun _ => gaussianPDFReal 0 v)
    (fun _ => integrable_gaussianPDFReal 0 v) (fun _ => gaussianPDFReal_nonneg 0 v)

theorem prod_gaussianPDFReal {ι : Type*} [Fintype ι] (v : ℝ≥0) (x : ι → ℝ) :
    (∏ i, gaussianPDFReal 0 v (x i)) =
      (Real.sqrt (2 * Real.pi * v))⁻¹ ^ Fintype.card ι *
        Real.exp (-(∑ i, x i ^ 2) / (2 * v)) := by
  simp only [gaussianPDFReal, sub_zero, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, ← Real.exp_sum, ← Finset.sum_div, ← Finset.sum_neg_distrib]

/-- A nonzero finite constant multiplying a measure does not change its normalization. -/
theorem cond_smul_univ {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    ProbabilityTheory.cond (c • μ) Set.univ = ProbabilityTheory.cond μ Set.univ := by
  simp only [ProbabilityTheory.cond, Measure.restrict_univ, Measure.smul_apply,
    smul_eq_mul, smul_smul]
  congr 1
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct), mul_comm c⁻¹,
    ENNReal.inv_mul_cancel_right hc0 hct]

theorem map_cond_univ {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (f : E → F) (hf : Measurable f) :
    (ProbabilityTheory.cond μ Set.univ).map f =
      ProbabilityTheory.cond (μ.map f) Set.univ := by
  simp only [ProbabilityTheory.cond, Measure.restrict_univ, Measure.map_smul,
    Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]

/-- A product of centered real Gaussians is the normalized radial Gaussian density. -/
theorem pi_gaussian_eq_cond_radial {ι : Type*} [Fintype ι]
    (v : ℝ≥0) (hv : v ≠ 0) :
    Measure.pi (fun _ : ι => gaussianReal 0 v) =
      ProbabilityTheory.cond
        ((volume : Measure (ι → ℝ)).withDensity
          (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / (2 * v))))) Set.univ := by
  let c : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹ ^ Fintype.card ι
  have hc : 0 < c := by
    dsimp [c]
    apply pow_pos
    apply inv_pos.mpr
    apply Real.sqrt_pos.mpr
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv))
  have heq : Measure.pi (fun _ : ι => gaussianReal 0 v) =
      ENNReal.ofReal c • (volume : Measure (ι → ℝ)).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / (2 * v)))) := by
    rw [pi_gaussian_density v hv]
    simp_rw [prod_gaussianPDFReal]
    change (volume : Measure (ι → ℝ)).withDensity
      (fun x => ENNReal.ofReal (c * Real.exp (-(∑ i, x i ^ 2) / (2 * v)))) = _
    simp_rw [ENNReal.ofReal_mul hc.le]
    exact withDensity_smul _ (by fun_prop)
  calc
    _ = ProbabilityTheory.cond (Measure.pi (fun _ : ι => gaussianReal 0 v)) Set.univ :=
      (ProbabilityTheory.cond_univ _).symm
    _ = _ := by
      rw [heq]
      exact cond_smul_univ _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top

/-- Normalizing a density makes it independent of the normalization of additive Haar measure. -/
theorem cond_withDensity_haar_eq {E : Type*} [AddCommGroup E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [LocallyCompactSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (μ ν : Measure E) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] (f : E → ℝ≥0∞) :
    ProbabilityTheory.cond (μ.withDensity f) Set.univ =
      ProbabilityTheory.cond (ν.withDensity f) Set.univ := by
  have heq : μ = (Measure.addHaarScalarFactor μ ν : ℝ≥0∞) • ν :=
    Measure.isAddLeftInvariant_eq_smul μ ν
  rw [heq, withDensity_smul_measure]
  exact cond_smul_univ _ _
    (by exact_mod_cast (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν).ne')
    ENNReal.coe_ne_top

/-- A quadratic form represented by orthonormal real coordinates has its expected Gaussian
density with respect to any additive Haar measure. No determinant normalization is needed. -/
theorem map_pi_gaussian_eq_cond_quadratic {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [LocallyCompactSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : (ι → ℝ) ≃L[ℝ] E)
    (Q : E → ℝ) (he : ∀ x, Q (e x) = ∑ i, x i ^ 2)
    (v : ℝ≥0) (hv : v ≠ 0) :
    (Measure.pi (fun _ : ι => gaussianReal 0 v)).map e =
      ProbabilityTheory.cond (μ.withDensity
        (fun y => ENNReal.ofReal (Real.exp (-Q y / (2 * v))))) Set.univ := by
  rw [pi_gaussian_eq_cond_radial v hv, map_cond_univ _ _ e.continuous.measurable]
  let em := e.toHomeomorph.toMeasurableEquiv
  have hmap := map_withDensity_equiv (volume : Measure (ι → ℝ)) em
    (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / (2 * v)))) (by fun_prop)
  change (Measure.map e ((volume : Measure (ι → ℝ)).withDensity
    (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / (2 * v)))))) =
      (Measure.map e volume).withDensity
        (fun y => ENNReal.ofReal (Real.exp (-(∑ i, (e.symm y) i ^ 2) / (2 * v)))) at hmap
  rw [hmap]
  have he' : ∀ y, (∑ i, (e.symm y) i ^ 2) = Q y := by
    intro y
    simpa only [e.apply_symm_apply] using (he (e.symm y)).symm
  simp_rw [he']
  exact cond_withDensity_haar_eq _ μ _

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5GUECoordinates -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace BosonicLearn.Prop5

noncomputable section

/-- Flattening matrix entries gives the usual Frobenius Hilbert space. -/
def frobeniusMatrixEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ ≃L[ℝ] EuclideanSpace ℂ (Fin n × Fin n) where
  toFun A := WithLp.toLp 2 (fun ij => A ij.1 ij.2)
  invFun x := fun i j => x (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := (PiLp.continuous_toLp _ _).comp (by fun_prop)
  continuous_invFun := by fun_prop

def FrobHerm0 (n : ℕ) : Submodule ℝ (EuclideanSpace ℂ (Fin n × Fin n)) :=
  (Herm0 n).map (frobeniusMatrixEquiv n).toLinearMap

def frobeniusHerm0Equiv (n : ℕ) : Herm0 n ≃L[ℝ] FrobHerm0 n :=
  (frobeniusMatrixEquiv n).submoduleMap (Herm0 n)

theorem norm_frobeniusMatrixEquiv (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖frobeniusMatrixEquiv n A‖ = WHMultiplicativity.schattenNorm 2 A := by
  rw [schatten_two_eq_sqrt, ← Real.sqrt_sq (norm_nonneg (frobeniusMatrixEquiv n A)),
    EuclideanSpace.norm_sq_eq]
  congr 1
  change (∑ ij : Fin n × Fin n, ‖A ij.1 ij.2‖ ^ 2) = _
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Orthonormal real coordinates of the traceless Hermitian Frobenius space. -/
noncomputable def gueCoordinates (n : ℕ) :
    (Fin (Module.finrank ℝ (FrobHerm0 n)) → ℝ) ≃L[ℝ] Herm0 n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) => ℝ)).symm.trans
    ((stdOrthonormalBasis ℝ (FrobHerm0 n)).repr.symm.toContinuousLinearEquiv.trans
      (frobeniusHerm0Equiv n).symm)

theorem schatten_two_gueCoordinates (n : ℕ)
    (x : Fin (Module.finrank ℝ (FrobHerm0 n)) → ℝ) :
    WHMultiplicativity.schattenNorm 2
      (gueCoordinates n x : Matrix (Fin n) (Fin n) ℂ) ^ 2 = ∑ i, x i ^ 2 := by
  rw [← norm_frobeniusMatrixEquiv]
  change ‖((frobeniusHerm0Equiv n) (gueCoordinates n x) : FrobHerm0 n)‖ ^ 2 = _
  simp only [gueCoordinates, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  change ‖(stdOrthonormalBasis ℝ (FrobHerm0 n)).repr.symm (WithLp.toLp 2 x)‖ ^ 2 = _
  rw [LinearIsometryEquiv.norm_map, EuclideanSpace.norm_sq_eq]
  simp

/-- The density-defined traceless GUE is exactly the orthonormal-coordinate Gaussian law. -/
theorem map_gaussian_gueCoordinates (n : ℕ) (hn : 0 < n) :
    (Measure.pi (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) =>
      gaussianReal 0 (2 / (n : ℝ≥0)))).map (gueCoordinates n) = tracelessGUE n := by
  have : SecondCountableTopology (Herm0 n) :=
    @TopologicalSpace.Subtype.secondCountableTopology (Fin n → Fin n → ℂ) _
      (fun X => X ∈ Herm0 n) inferInstance
  have hv : (2 / (n : ℝ≥0)) ≠ 0 := div_ne_zero (by norm_num) (by exact_mod_cast hn.ne')
  rw [map_pi_gaussian_eq_cond_quadratic (Measure.addHaar : Measure (Herm0 n))
    (gueCoordinates n)
    (fun X => WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) ^ 2)
    (schatten_two_gueCoordinates n) _ hv]
  unfold tracelessGUE tracelessGUEWeight
  congr 2
  funext X
  congr 2
  simp only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_natCast]
  field_simp
  ring

def gueStandardMap (n : ℕ) :
    (Fin (Module.finrank ℝ (FrobHerm0 n)) → ℝ) →L[ℝ] Herm0 n :=
  (gueCoordinates n).toContinuousLinearMap.comp
    ((Real.sqrt (2 / (n : ℝ))) • ContinuousLinearMap.id ℝ _)

theorem map_standardGaussian_gueStandardMap (n : ℕ) (hn : 0 < n) :
    (Measure.pi (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) => gaussianReal 0 1)).map
      (gueStandardMap n) = tracelessGUE n := by
  have hscale : (Measure.pi (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) => gaussianReal 0 1)).map
      (fun x => Real.sqrt (2 / (n : ℝ)) • x) =
      Measure.pi (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) => gaussianReal 0 (2 / (n : ℝ≥0))) := by
    change (Measure.pi (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) => gaussianReal 0 1)).map
      (fun x i => Real.sqrt (2 / (n : ℝ)) * x i) = _
    rw [Measure.pi_map_pi (f := fun _ z => Real.sqrt (2 / (n : ℝ)) * z)
      (fun _ => by fun_prop)]
    congr 1
    funext i
    rw [gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one]
    congr 1
    apply NNReal.eq
    simp only [NNReal.coe_mk, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_natCast]
    exact Real.sq_sqrt (by positivity)
  have hcomp : (gueStandardMap n : _ → _) =
      (gueCoordinates n) ∘ (fun x => Real.sqrt (2 / (n : ℝ)) • x) := rfl
  rw [hcomp, ← Measure.map_map (gueCoordinates n).continuous.measurable (by fun_prop), hscale]
  exact map_gaussian_gueCoordinates n hn

theorem schatten_two_gueStandardMap (n : ℕ)
    (x : Fin (Module.finrank ℝ (FrobHerm0 n)) → ℝ) :
    WHMultiplicativity.schattenNorm 2
      (gueStandardMap n x : Matrix (Fin n) (Fin n) ℂ) =
      Real.sqrt (2 / (n : ℝ)) * Real.sqrt (∑ i, x i ^ 2) := by
  have hsq := schatten_two_gueCoordinates n (Real.sqrt (2 / (n : ℝ)) • x)
  change WHMultiplicativity.schattenNorm 2 (gueStandardMap n x : Matrix (Fin n) (Fin n) ℂ) ^ 2 = _ at hsq
  have hnrm : 0 ≤ WHMultiplicativity.schattenNorm 2 (gueStandardMap n x : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← norm_frobeniusMatrixEquiv]
    exact norm_nonneg _
  rw [← Real.sqrt_sq hnrm, hsq]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.sqrt_nonneg _)]

end
end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5GaussianTail -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- Two Lipschitz Gaussian observables with a common mean bound have a
nonasymptotic upper tail with the union-bound factor two. -/
theorem gaussian_two_observable_tail {ι : Type*} [Fintype ι]
    (f g : (ι → ℝ) → ℝ) (L m t : ℝ) (hL : 0 < L) (ht : 0 ≤ t)
    (hf : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (hg : ∀ x y, |g x - g y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (hmf : (∫ x, f x ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) ≤ m)
    (hmg : (∫ x, g x ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) ≤ m) :
    (Measure.pi fun _ : ι => gaussianReal 0 1) {x | m + t < max (f x) (g x)} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  let μ : Measure (ι → ℝ) := Measure.pi fun _ : ι => gaussianReal 0 1
  have hf' := (GaussianMatrix.gaussian_concentration_vector f L hL hf (t / L)
    (div_nonneg ht hL.le)).2
  have hg' := (GaussianMatrix.gaussian_concentration_vector g L hL hg (t / L)
    (div_nonneg ht hL.le)).2
  have hcancel : L * (t / L) = t := by field_simp
  have hexp : -(t / L) ^ 2 / 2 = -t ^ 2 / (2 * L ^ 2) := by ring
  rw [hcancel, hexp] at hf' hg'
  have hsub : {x | m + t < max (f x) (g x)} ⊆
      {x | (∫ y, f y ∂μ) + t ≤ f x} ∪ {x | (∫ y, g y ∂μ) + t ≤ g x} := by
    intro x hx
    change m + t < max (f x) (g x) at hx
    rcases lt_max_iff.mp hx with h | h
    · apply Or.inl
      change (∫ y, f y ∂μ) + t ≤ f x
      exact (add_le_add hmf le_rfl).trans h.le
    · apply Or.inr
      change (∫ y, g y ∂μ) + t ≤ g x
      exact (add_le_add hmg le_rfl).trans h.le
  calc
    μ {x | m + t < max (f x) (g x)} ≤
        μ ({x | (∫ y, f y ∂μ) + t ≤ f x} ∪ {x | (∫ y, g y ∂μ) + t ≤ g x}) :=
      measure_mono hsub
    _ ≤ μ {x | (∫ y, f y ∂μ) + t ≤ f x} + μ {x | (∫ y, g y ∂μ) + t ≤ g x} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) +
        ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) := add_le_add hf' hg'
    _ = ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      congr 1
      ring

/-- Transport of the Gaussian two-observable bound through an exact model law. -/
theorem gaussian_mapped_two_observable_tail {ι Θ : Type*} [Fintype ι] [MeasurableSpace Θ]
    (P : Measure Θ) (F : (ι → ℝ) → Θ) (hF : Measurable F)
    (hlaw : Measure.map F (Measure.pi fun _ : ι => gaussianReal 0 1) = P)
    (d : Θ → ℝ) (hd : Measurable d) (f g : (ι → ℝ) → ℝ)
    (L m t : ℝ) (hL : 0 < L) (ht : 0 ≤ t)
    (hf : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (hg : ∀ x y, |g x - g y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2))
    (hmf : (∫ x, f x ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) ≤ m)
    (hmg : (∫ x, g x ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) ≤ m)
    (hobs : ∀ x, d (F x) ≤ max (f x) (g x)) :
    P {X | m + t < d X} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  rw [← hlaw, Measure.map_apply hF (measurableSet_lt measurable_const hd)]
  refine (measure_mono ?_).trans (gaussian_two_observable_tail f g L m t hL ht hf hg hmf hmg)
  intro x hx
  exact hx.trans_le (hobs x)

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5GUEConcentration -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace BosonicLearn.Prop5

noncomputable section

def gueRayleigh (n : ℕ) (x : Fin (Module.finrank ℝ (FrobHerm0 n)) → ℝ) : ℝ :=
  upperRayleigh (Matrix.toEuclideanCLM (𝕜 := ℂ)
    (gueStandardMap n x : Matrix (Fin n) (Fin n) ℂ))

theorem continuous_upperRayleigh {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    Continuous (upperRayleigh : (E →L[ℂ] E) → ℝ) := by
  apply (LipschitzWith.of_dist_le_mul (K := 1) ?_).continuous
  intro T S
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
    upperRayleigh_lipschitz T S

theorem continuous_gueRayleigh (n : ℕ) : Continuous (gueRayleigh n) := by
  apply continuous_upperRayleigh.comp
  exact ((LinearMap.continuous_of_finiteDimensional
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)).comp
      continuous_subtype_val).comp (gueStandardMap n).continuous

theorem gueRayleigh_lipschitz (n : ℕ)
    (x y : Fin (Module.finrank ℝ (FrobHerm0 n)) → ℝ) :
    |gueRayleigh n x - gueRayleigh n y| ≤
      Real.sqrt (2 / (n : ℝ)) * Real.sqrt (∑ i, (x i - y i) ^ 2) := by
  have h := matrix_upperRayleigh_lipschitz n
    (gueStandardMap n x : Matrix (Fin n) (Fin n) ℂ)
    (gueStandardMap n y : Matrix (Fin n) (Fin n) ℂ)
  change |gueRayleigh n x - gueRayleigh n y| ≤
    WHMultiplicativity.schattenNorm 2 ((gueStandardMap n x - gueStandardMap n y : Herm0 n) :
      Matrix (Fin n) (Fin n) ℂ) at h
  rw [← map_sub, schatten_two_gueStandardMap] at h
  exact h

theorem pi_standardGaussian_map_neg {ι : Type*} [Fintype ι] :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun x => -x) =
      Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  change (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun x i => -x i) = _
  rw [Measure.pi_map_pi (f := fun _ z => -z) (fun _ => by fun_prop)]
  simp_rw [gaussianReal_map_neg, neg_zero]

theorem integral_gueRayleigh_neg (n : ℕ) :
    (∫ x, gueRayleigh n (-x) ∂(Measure.pi fun _ => gaussianReal 0 1)) =
      ∫ x, gueRayleigh n x ∂(Measure.pi fun _ => gaussianReal 0 1) := by
  rw [← integral_map (by fun_prop) (continuous_gueRayleigh n).aestronglyMeasurable,
    pi_standardGaussian_map_neg]

/-- The sharp Gaussian operator tail follows from the expected Rayleigh maximum bound. -/
theorem gue_operator_tail_of_mean (n : ℕ) (hn : 0 < n) (m t : ℝ) (ht : 0 ≤ t)
    (hm : (∫ x, gueRayleigh n x ∂(Measure.pi fun _ => gaussianReal 0 1)) ≤ m) :
    tracelessGUE n {X | m + t <
      WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ)} ≤
        ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * t ^ 2 / 4)) := by
  have hL : 0 < Real.sqrt (2 / (n : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hd : Measurable (fun X : Herm0 n => WHMultiplicativity.schattenNorm ⊤
      (X : Matrix (Fin n) (Fin n) ℂ)) := by
    have hc : Continuous fun X : Herm0 n =>
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ := by
      apply Continuous.norm
      exact (LinearMap.continuous_of_finiteDimensional
        ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)).comp
          continuous_subtype_val
    simpa [WHMultiplicativity.schattenNorm] using hc.measurable
  have hg : ∀ x y, |gueRayleigh n (-x) - gueRayleigh n (-y)| ≤
      Real.sqrt (2 / (n : ℝ)) * Real.sqrt (∑ i, (x i - y i) ^ 2) := by
    intro x y
    convert gueRayleigh_lipschitz n (-x) (-y) using 1
    simp only [Pi.neg_apply]
    congr 3
    funext i
    ring
  have hobs : ∀ x, WHMultiplicativity.schattenNorm ⊤
      (gueStandardMap n x : Matrix (Fin n) (Fin n) ℂ) ≤
      max (gueRayleigh n x) (gueRayleigh n (-x)) := by
    intro x
    have hsym : (Matrix.toEuclideanCLM (𝕜 := ℂ)
      (gueStandardMap n x : Matrix (Fin n) (Fin n) ℂ)).IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr (gueStandardMap n x).property.1
    have h := norm_le_max_upperRayleigh _ hsym
    simpa [WHMultiplicativity.schattenNorm, gueRayleigh, map_neg,
      Submodule.coe_neg] using h
  have h := gaussian_mapped_two_observable_tail (tracelessGUE n) (gueStandardMap n)
    (gueStandardMap n).continuous.measurable (map_standardGaussian_gueStandardMap n hn)
    (fun X => WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ)) hd
    (gueRayleigh n) (fun x => gueRayleigh n (-x)) (Real.sqrt (2 / (n : ℝ))) m t hL ht
    (gueRayleigh_lipschitz n) hg hm (by rwa [integral_gueRayleigh_neg]) hobs
  convert h using 2
  congr 2
  rw [Real.sq_sqrt (by positivity)]
  field_simp
  ring

end
end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5GaussianProcess -/
section
open MeasureTheory ProbabilityTheory

noncomputable section
namespace BosonicLearn.Prop5

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [FiniteDimensional ℝ K] [MeasurableSpace K] [BorelSpace K]

/-- The canonical process of a standard Gaussian vector, indexed by arbitrary coefficient vectors. -/
theorem isGaussianProcess_inner_stdGaussian {T : Type*} (a : T → K) :
    IsGaussianProcess (fun t x => inner ℝ (a t) x) (stdGaussian K) := by
  constructor
  intro I
  exact IsGaussian.hasGaussianLaw_id.map
    (ContinuousLinearMap.pi (fun t : I => innerSL ℝ (a t)))

/-- Every canonical Gaussian coordinate has zero mean. -/
theorem integral_inner_stdGaussian (a : K) :
    (∫ x, inner ℝ a x ∂stdGaussian K) = 0 :=
  integral_strongDual_stdGaussian (innerSL ℝ a)

/-- The canonical Gaussian metric is precisely the Hilbert-space distance. -/
theorem integral_sq_inner_sub_stdGaussian (a b : K) :
    (∫ x, (inner ℝ a x - inner ℝ b x)^2 ∂stdGaussian K) = ‖a-b‖^2 := by
  have hm := integral_strongDual_stdGaussian (innerSL ℝ (a-b))
  have hv := variance_dual_stdGaussian (innerSL ℝ (a-b))
  rw [variance_of_integral_eq_zero (by fun_prop) hm, innerSL_apply_norm] at hv
  simpa only [innerSL_apply_apply, inner_sub_left] using hv

/-- The norm of a finite-dimensional standard Gaussian is square-integrable. -/
theorem memLp_norm_stdGaussian : MemLp (fun x : K => ‖x‖) 2 (stdGaussian K) :=
  IsGaussian.memLp_two_id.norm

/-- The total second moment of an isotropic standard Gaussian equals its real dimension. -/
theorem integral_norm_sq_stdGaussian :
    (∫ x : K, ‖x‖^2 ∂stdGaussian K) = (Module.finrank ℝ K : ℝ) := by
  let b := stdOrthonormalBasis ℝ K
  have heq : (fun x : K => ‖x‖^2) =
      (fun x => ∑ i : Fin (Module.finrank ℝ K), (inner ℝ (b i) x)^2) := by
    funext x
    exact (b.sum_sq_inner_right x).symm
  rw [heq, integral_finsetSum]
  · have hval : ∀ i : Fin (Module.finrank ℝ K),
        (∫ x : K, (inner ℝ (b i) x)^2 ∂stdGaussian K) = 1 := by
      intro i
      have h := integral_sq_inner_sub_stdGaussian (b i) (0 : K)
      simpa using h
    simp [hval]
  · intro i hi
    exact (IsGaussian.hasGaussianLaw_id.map (innerSL ℝ (b i))).memLp_two.integrable_sq

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5GUEExpectation -/
section
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal BigOperators

namespace BosonicLearn.Prop5
noncomputable section
set_option maxHeartbeats 1000000

/-- Gaussian comparison of finite-marginal expected suprema allows different probability spaces. -/
theorem processESup_comparison_two_spaces {Ω Ω' T : Type}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (X : T → Ω → ℝ) (Y : T → Ω' → ℝ)
    (hXG : IsGaussianProcess X μ) (hYG : IsGaussianProcess Y ν)
    (hXm : ∀ t, ∫ ω, X t ω ∂μ = 0) (hYm : ∀ t, ∫ ω, Y t ω ∂ν = 0)
    (hinc : ∀ t s, ∫ ω, (X t ω - X s ω)^2 ∂μ ≤ ∫ ω, (Y t ω - Y s ω)^2 ∂ν) :
    HighDimProb.RandomProcesses.processESup μ X ≤
      HighDimProb.RandomProcesses.processESup ν Y := by
  classical
  apply iSup_le
  intro s
  have : Nonempty s.1 := s.2.to_subtype
  have hmax (Z : T → ℝ) : s.1.sup' s.2 Z = ⨆ t : s.1, Z t := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun t ht => le_ciSup
        (Set.finite_range (fun u : s.1 => Z u)).bddAbove ⟨t, ht⟩)
    · exact ciSup_le (fun t => Finset.le_sup' Z t.property)
  have h := GaussianMatrix.sudakov_fernique (fun t : s.1 => X t) (fun t : s.1 => Y t)
    (hXG.hasGaussianLaw s.1) (hYG.hasGaussianLaw s.1)
    (fun t => hXm t) (fun t => hYm t) (fun t u => hinc t u)
  apply le_trans (b := ((∫ ω, s.1.sup' s.2 (fun t => Y t ω) ∂ν : ℝ) : EReal))
  · apply EReal.coe_le_coe_iff.mpr
    simpa only [hmax] using h
  · exact le_iSup (fun s : {s : Finset T // s.Nonempty} =>
      ((∫ ω, s.1.sup' s.2 (fun t => Y t ω) ∂ν : ℝ) : EReal)) s

/-- A continuous Gaussian process is bounded in mean by an integrable envelope of a
comparison process, even when the processes use different sample spaces. -/
theorem expected_sup_le_of_gaussian_comparison_two_spaces {Ω Ω' T : Type}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
    (μ : Measure Ω) (ν : Measure Ω') (X : T → Ω → ℝ) (Y : T → Ω' → ℝ)
    (hXG : IsGaussianProcess X μ) (hYG : IsGaussianProcess Y ν)
    (hXm : ∀ t, ∫ ω, X t ω ∂μ = 0) (hYm : ∀ t, ∫ ω, Y t ω ∂ν = 0)
    (hinc : ∀ t s, ∫ ω, (X t ω - X s ω)^2 ∂μ ≤ ∫ ω, (Y t ω - Y s ω)^2 ∂ν)
    (hcont : ∀ ω, Continuous (fun t => X t ω))
    (gX : Ω → ℝ) (hgX : Integrable gX μ) (hbX : ∀ t ω, ‖X t ω‖ ≤ gX ω)
    (gY : Ω' → ℝ) (hgY : Integrable gY ν) (hbY : ∀ t ω, Y t ω ≤ gY ω) :
    (∫ ω, (⨆ t, X t ω) ∂μ) ≤ ∫ ω, gY ω ∂ν := by
  apply EReal.coe_le_coe_iff.mp
  exact (integral_iSup_le_processESup μ X
    (fun t => (hXG.hasGaussianLaw_eval t).integrable.aestronglyMeasurable)
    hcont gX hgX hbX).trans
    ((processESup_comparison_two_spaces μ ν X Y hXG hYG hXm hYm hinc).trans
      (processESup_le_integral ν Y (fun t => (hYG.hasGaussianLaw_eval t).integrable) gY hgY hbY))

def gueHilbertOperator (n : ℕ) :
    FrobHerm0 n →L[ℝ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  (LinearMap.toContinuousLinearMap
    (((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap.restrictScalars ℝ).comp
      (Herm0 n).subtype)).comp
    ((Real.sqrt (2 / (n : ℝ))) • (frobeniusHerm0Equiv n).symm.toContinuousLinearMap)

def gueCoefficient (n : ℕ) : RayleighIndex (EuclideanSpace ℂ (Fin n)) → FrobHerm0 n :=
  Sum.elim (fun v => Real.sqrt (2 / (n : ℝ)) •
    (FrobHerm0 n).orthogonalProjectionOnto (projectorVector (v : EuclideanSpace ℂ (Fin n))))
    (fun _ => 0)

def gueComparisonCoefficient (n : ℕ) :
    RayleighIndex (EuclideanSpace ℂ (Fin n)) → EuclideanSpace ℂ (Fin n) :=
  Sum.elim (fun v => (2 / Real.sqrt n) • (v : EuclideanSpace ℂ (Fin n))) (fun _ => 0)

theorem real_inner_euclidean_eq_re {ι : Type*} [Fintype ι]
    (u v : EuclideanSpace ℂ ι) : inner ℝ u v = (inner ℂ u v).re := by
  simp only [PiLp.inner_apply, Complex.inner, RCLike.inner_apply, Complex.re_sum]

theorem indexedRayleigh_gueHilbertOperator (n : ℕ) (Z : FrobHerm0 n)
    (v : RayleighIndex (EuclideanSpace ℂ (Fin n))) :
    indexedRayleigh (gueHilbertOperator n Z) v = inner ℝ (gueCoefficient n v) Z := by
  cases v with
  | inr v => simp [indexedRayleigh, gueCoefficient]
  | inl v =>
    change (Matrix.toEuclideanCLM (𝕜 := ℂ)
      ((Real.sqrt (2 / (n : ℝ)) • (frobeniusHerm0Equiv n).symm Z : Herm0 n) :
        Matrix (Fin n) (Fin n) ℂ)).rayleighQuotient v = _
    rw [rayleigh_unit_eq_real_inner_projector _ _ (norm_eq_of_mem_sphere v)]
    rw [← real_inner_euclidean_eq_re]
    change inner ℝ (projectorVector (v : EuclideanSpace ℂ (Fin n)))
      (frobeniusMatrixEquiv n
        ((Real.sqrt (2 / (n : ℝ)) • (frobeniusHerm0Equiv n).symm Z : Herm0 n) :
          Matrix (Fin n) (Fin n) ℂ)) = _
    have heq : frobeniusMatrixEquiv n
        ((Real.sqrt (2 / (n : ℝ)) • (frobeniusHerm0Equiv n).symm Z : Herm0 n) :
          Matrix (Fin n) (Fin n) ℂ) = Real.sqrt (2 / (n : ℝ)) • (Z : EuclideanSpace ℂ (Fin n × Fin n)) := by
      change ((frobeniusHerm0Equiv n)
        (Real.sqrt (2 / (n : ℝ)) • (frobeniusHerm0Equiv n).symm Z) :
          EuclideanSpace ℂ (Fin n × Fin n)) = _
      rw [map_smul, ContinuousLinearEquiv.apply_symm_apply]
      rfl
    rw [heq]
    change inner ℝ (projectorVector (v : EuclideanSpace ℂ (Fin n)))
      (Real.sqrt (2 / (n : ℝ)) • (Z : EuclideanSpace ℂ (Fin n × Fin n))) =
      inner ℝ (Real.sqrt (2 / (n : ℝ)) • (FrobHerm0 n).orthogonalProjectionOnto
        (projectorVector (v : EuclideanSpace ℂ (Fin n)))) Z
    rw [real_inner_smul_left (F := FrobHerm0 n), real_inner_smul_right]
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]

theorem gue_scales (n : ℕ) (hn : 0 < n) :
    (Real.sqrt (2 / (n : ℝ))) ^ 2 * 2 = (2 / Real.sqrt (n : ℝ)) ^ 2 := by
  rw [Real.sq_sqrt (by positivity), div_pow, Real.sq_sqrt (by positivity)]
  field_simp

theorem gueCoefficient_increment (n : ℕ) (hn : 0 < n)
    (v w : RayleighIndex (EuclideanSpace ℂ (Fin n))) :
    ‖gueCoefficient n v - gueCoefficient n w‖ ^ 2 ≤
      ‖gueComparisonCoefficient n v - gueComparisonCoefficient n w‖ ^ 2 := by
  have hc : 0 ≤ Real.sqrt (2 / (n : ℝ)) := Real.sqrt_nonneg _
  have hd : 0 ≤ 2 / Real.sqrt (n : ℝ) := by positivity
  have hzero (u : Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1) :
      ‖gueCoefficient n (Sum.inl u)‖ ^ 2 ≤ ‖gueComparisonCoefficient n (Sum.inl u)‖ ^ 2 := by
    have hp := (FrobHerm0 n).norm_orthogonalProjectionOnto_apply_le (projectorVector (u : EuclideanSpace ℂ (Fin n)))
    have hp2 : ‖(FrobHerm0 n).orthogonalProjectionOnto (projectorVector (u : EuclideanSpace ℂ (Fin n)))‖ ^ 2 ≤ 1 := by
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hp 2
      rw [norm_projectorVector_sq, norm_eq_of_mem_sphere u] at hsq
      simpa using hsq
    change ‖Real.sqrt (2 / (n : ℝ)) • (FrobHerm0 n).orthogonalProjectionOnto (projectorVector (u : EuclideanSpace ℂ (Fin n)))‖ ^ 2 ≤
      ‖(2 / Real.sqrt (n : ℝ)) • (u : EuclideanSpace ℂ (Fin n))‖ ^ 2
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hc, abs_of_nonneg hd, mul_pow, norm_eq_of_mem_sphere u, mul_one]
    have hs := gue_scales n hn
    have hmul := mul_le_mul_of_nonneg_left hp2 (sq_nonneg (Real.sqrt (2 / (n : ℝ))))
    nlinarith [sq_nonneg (Real.sqrt (2 / (n : ℝ)))]
  cases v with
  | inr v =>
    cases w with
    | inr w => simp [gueCoefficient, gueComparisonCoefficient]
    | inl w => simpa [gueCoefficient, gueComparisonCoefficient] using hzero w
  | inl v =>
    cases w with
    | inr w => simpa [gueCoefficient, gueComparisonCoefficient] using hzero v
    | inl w =>
      have hp := (FrobHerm0 n).norm_orthogonalProjectionOnto_apply_le
        (projectorVector (v : EuclideanSpace ℂ (Fin n)) - projectorVector (w : EuclideanSpace ℂ (Fin n)))
      have hp2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
      have hi := unit_projector_increment_bound (ι := Fin n) (v : EuclideanSpace ℂ (Fin n)) (w : EuclideanSpace ℂ (Fin n))
        (norm_eq_of_mem_sphere v) (norm_eq_of_mem_sphere w)
      change ‖Real.sqrt (2 / (n : ℝ)) • (FrobHerm0 n).orthogonalProjectionOnto (projectorVector (v : EuclideanSpace ℂ (Fin n))) -
        Real.sqrt (2 / (n : ℝ)) • (FrobHerm0 n).orthogonalProjectionOnto (projectorVector (w : EuclideanSpace ℂ (Fin n)))‖ ^ 2 ≤
        ‖(2 / Real.sqrt (n : ℝ)) • (v : EuclideanSpace ℂ (Fin n)) -
          (2 / Real.sqrt (n : ℝ)) • (w : EuclideanSpace ℂ (Fin n))‖ ^ 2
      rw [← smul_sub, ← smul_sub, ← map_sub, norm_smul, norm_smul,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg hd,
        mul_pow, mul_pow]
      calc
        _ ≤ (Real.sqrt (2 / (n : ℝ))) ^ 2 *
            (2 * ‖(v : EuclideanSpace ℂ (Fin n)) - w‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hp2.trans hi) (sq_nonneg _)
        _ = _ := by rw [← mul_assoc, gue_scales n hn]

/-- Sudakov--Fernique bounds the mean largest GUE eigenvalue by the mean norm of a
standard complex Gaussian vector, with the sharp scaling. -/
theorem gueHilbert_mean_le_envelope (n : ℕ) (hn : 0 < n) :
    (∫ Z, upperRayleigh (gueHilbertOperator n Z) ∂stdGaussian (FrobHerm0 n)) ≤
      ∫ g : EuclideanSpace ℂ (Fin n), (2 / Real.sqrt n) * ‖g‖ ∂stdGaussian _ := by
  let X := fun v Z => inner ℝ (gueCoefficient n v) Z
  let Y := fun v g => inner ℝ (gueComparisonCoefficient n v) g
  have hcont : ∀ Z, Continuous (fun v => X v Z) := by
    intro Z
    convert continuous_indexedRayleigh (gueHilbertOperator n Z) using 1
    funext v
    exact (indexedRayleigh_gueHilbertOperator n Z v).symm
  have hgX : Integrable (fun Z => ‖gueHilbertOperator n Z‖) (stdGaussian (FrobHerm0 n)) :=
    (IsGaussian.hasGaussianLaw_id.map (gueHilbertOperator n)).integrable.norm
  have hgY : Integrable (fun g : EuclideanSpace ℂ (Fin n) => (2 / Real.sqrt n) * ‖g‖)
      (stdGaussian _) := IsGaussian.integrable_id.norm.const_mul _
  have h := expected_sup_le_of_gaussian_comparison_two_spaces
    (stdGaussian (FrobHerm0 n)) (stdGaussian (EuclideanSpace ℂ (Fin n))) X Y
    (isGaussianProcess_inner_stdGaussian (gueCoefficient n))
    (isGaussianProcess_inner_stdGaussian (gueComparisonCoefficient n))
    (fun v => integral_inner_stdGaussian (gueCoefficient n v))
    (fun v => integral_inner_stdGaussian (gueComparisonCoefficient n v))
    (fun v w => by
      change (∫ Z, (inner ℝ (gueCoefficient n v) Z - inner ℝ (gueCoefficient n w) Z)^2
        ∂stdGaussian (FrobHerm0 n)) ≤ _
      rw [integral_sq_inner_sub_stdGaussian (K := FrobHerm0 n),
        integral_sq_inner_sub_stdGaussian]
      exact gueCoefficient_increment n hn v w)
    hcont (fun Z => ‖gueHilbertOperator n Z‖) hgX
    (fun v Z => by
      change ‖inner ℝ (gueCoefficient n v) Z‖ ≤ _
      rw [← indexedRayleigh_gueHilbertOperator]
      exact indexedRayleigh_norm_le _ _)
    (fun g => (2 / Real.sqrt n) * ‖g‖) hgY (fun v g => by
      cases v with
      | inr v => simp [Y, gueComparisonCoefficient]; positivity
      | inl v =>
        change inner ℝ ((2 / Real.sqrt n) • (v : EuclideanSpace ℂ (Fin n))) g ≤ _
        rw [real_inner_smul_left]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [norm_eq_of_mem_sphere v, one_mul] using real_inner_le_norm (v : EuclideanSpace ℂ (Fin n)) g)
  simpa only [X, ← indexedRayleigh_gueHilbertOperator, iSup_indexedRayleigh] using h

theorem gueHilbert_mean_le (n : ℕ) (hn : 0 < n) :
    (∫ Z, upperRayleigh (gueHilbertOperator n Z) ∂stdGaussian (FrobHerm0 n)) ≤
      2 * Real.sqrt 2 := by
  apply (gueHilbert_mean_le_envelope n hn).trans
  apply comparison_envelope_mean_le (stdGaussian (EuclideanSpace ℂ (Fin n))) n hn id
    memLp_norm_stdGaussian
  change (∫ g : EuclideanSpace ℂ (Fin n), ‖g‖ ^ 2 ∂stdGaussian _) ≤ _
  rw [integral_norm_sq_stdGaussian]
  simp [finrank_real_of_complex]

theorem integral_gueRayleigh_eq_hilbert (n : ℕ) :
    (∫ x, gueRayleigh n x ∂(Measure.pi fun _ => gaussianReal 0 1)) =
      ∫ Z, upperRayleigh (gueHilbertOperator n Z) ∂stdGaussian (FrobHerm0 n) := by
  let b := stdOrthonormalBasis ℝ (FrobHerm0 n)
  have hmap : (Measure.pi (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) => gaussianReal 0 1)).map
      (fun x => b.repr.symm (WithLp.toLp 2 x)) = stdGaussian (FrobHerm0 n) := by
    rw [show (fun x => b.repr.symm (WithLp.toLp 2 x)) = b.repr.symm ∘ WithLp.toLp 2 from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), map_pi_eq_stdGaussian, stdGaussian_map]
  rw [← hmap, integral_map (by fun_prop)
    (show AEStronglyMeasurable (fun Z => upperRayleigh (gueHilbertOperator n Z)) _ from
      (continuous_upperRayleigh.comp (gueHilbertOperator n).continuous).aestronglyMeasurable)]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  change upperRayleigh (Matrix.toEuclideanCLM (𝕜 := ℂ)
    (gueCoordinates n (Real.sqrt (2 / (n : ℝ)) • x) : Matrix (Fin n) (Fin n) ℂ)) = _
  rw [map_smul]
  rfl

theorem gueRayleigh_mean_le (n : ℕ) (hn : 0 < n) :
    (∫ x, gueRayleigh n x ∂(Measure.pi fun _ => gaussianReal 0 1)) ≤ 2 * Real.sqrt 2 := by
  rw [integral_gueRayleigh_eq_hilbert]
  exact gueHilbert_mean_le n hn

/-- The unconditioned traceless-GUE concentration estimate follows from proved Gaussian
comparison and concentration, with all coordinate and density identifications checked. -/
theorem gue_operator_tail_proved (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t) :
    tracelessGUE n {X | 2 * Real.sqrt 2 + t <
      WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ)} ≤
      ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * t ^ 2 / 4)) :=
  gue_operator_tail_of_mean n hn (2 * Real.sqrt 2) t ht.le (gueRayleigh_mean_le n hn)

end
end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5Geometry -/
section
open scoped ENNReal Matrix ComplexOrder
open BosonicLearn
set_option maxHeartbeats 600000

noncomputable section
namespace Prop5Geometry

/-- The trace norm of a Hermitian matrix is attained on a unitary: `‖H‖₁ = Tr(H W)`. -/
private lemma schatten_one_herm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    ∃ W : Matrix (Fin n) (Fin n) ℂ, Wᴴ * W = 1 ∧
      WHMultiplicativity.schattenNorm 1 H = (H * W).trace.re := by
  obtain ⟨V, hVdef⟩ : ∃ V : Matrix (Fin n) (Fin n) ℂ,
      V = (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have hV1 : Vᴴ * V = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_star_mul_self _
  have hV2 : V * Vᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_mul_star_self _
  set x : Fin n → ℝ := hH.eigenvalues with hx
  have hspec : H = V * Matrix.diagonal (fun i => ((x i : ℝ) : ℂ)) * Vᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hVdef, ← Matrix.star_eq_conjTranspose]
    exact h
  have hcfc : cfc (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (Hᴴ * H) =
      V * Matrix.diagonal (fun i => ((|x i| : ℝ) : ℂ)) * Vᴴ := by
    rw [hH.eq]
    have hsa : IsSelfAdjoint H := hH.isSelfAdjoint
    have h1 : H * H = cfc (fun t : ℝ => t ^ 2) H := by
      rw [cfc_pow_id H 2, pow_two]
    have hc : Continuous (fun t : ℝ => t ^ ((1 : ℝ) / 2)) :=
      Real.continuous_rpow_const (by norm_num)
    rw [h1, ← cfc_comp' (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (fun t : ℝ => t ^ 2) H hc.continuousOn,
      hH.cfc_eq]
    unfold Matrix.IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply, ← hVdef, Matrix.star_eq_conjTranspose]
    have hd : (RCLike.ofReal ∘ (fun t : ℝ => (t ^ 2) ^ ((1 : ℝ) / 2)) ∘ hH.eigenvalues :
        Fin n → ℂ) = fun i => ((|x i| : ℝ) : ℂ) := by
      funext i
      simp only [Function.comp_apply]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
      rfl
    rw [hd]
  have hnorm : WHMultiplicativity.schattenNorm 1 H =
      (cfc (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (Hᴴ * H)).trace.re := by
    unfold WHMultiplicativity.schattenNorm
    rw [if_neg ENNReal.one_ne_top]
    simp only [ENNReal.toReal_one, div_one]
    rw [Real.rpow_one]
  set s : Fin n → ℝ := fun i => if 0 ≤ x i then 1 else -1 with hs
  have hss : ∀ i, s i * s i = 1 := by
    intro i
    simp only [hs]
    split_ifs <;> norm_num
  have hxs : ∀ i, x i * s i = |x i| := by
    intro i
    simp only [hs]
    split_ifs with h
    · rw [abs_of_nonneg h, mul_one]
    · rw [abs_of_neg (not_le.mp h)]; ring
  set W : Matrix (Fin n) (Fin n) ℂ := V * Matrix.diagonal (fun i => ((s i : ℝ) : ℂ)) * Vᴴ with hW
  have hWh : Wᴴ = W := by
    rw [hW, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
    congr 3
    funext i
    simp
  have hmul : ∀ d₁ d₂ : Fin n → ℂ, (V * Matrix.diagonal d₁ * Vᴴ) * (V * Matrix.diagonal d₂ * Vᴴ) =
      V * Matrix.diagonal (fun i => d₁ i * d₂ i) * Vᴴ := by
    intro d₁ d₂
    have h : (V * Matrix.diagonal d₁ * Vᴴ) * (V * Matrix.diagonal d₂ * Vᴴ) =
        V * (Matrix.diagonal d₁ * (Vᴴ * V) * Matrix.diagonal d₂) * Vᴴ := by
      simp only [Matrix.mul_assoc]
    rw [h, hV1, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
  refine ⟨W, ?_, ?_⟩
  · rw [hWh, hW, hmul]
    have h1 : (fun i => ((s i : ℝ) : ℂ) * ((s i : ℝ) : ℂ)) = fun _ : Fin n => (1 : ℂ) := by
      funext i
      rw [← Complex.ofReal_mul, hss i, Complex.ofReal_one]
    rw [h1, Matrix.diagonal_one, Matrix.mul_one, hV2]
  · rw [hnorm, hcfc]
    have h2 : (fun i => ((x i : ℝ) : ℂ) * ((s i : ℝ) : ℂ)) = fun i => ((|x i| : ℝ) : ℂ) := by
      funext i
      rw [← Complex.ofReal_mul, hxs i]
    conv_rhs => rw [hspec, hW, hmul, h2]

/-- Hölder-type bound: `|Tr(diag(e) P Q)| ≤ ∑ |eᵢ|` when `P Pᴴ ⪯ 1` and `Qᴴ Q ⪯ 1`. -/
private lemma holder {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (e : Fin n → ℝ)
    (hP : (1 - P * Pᴴ).PosSemidef) (hQ : (1 - Qᴴ * Q).PosSemidef) :
    |(Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) * (P * Q)).trace.re| ≤ ∑ i, |e i| := by
  have hProw : ∀ i, ∑ j, ‖P i j‖ ^ 2 ≤ 1 := by
    intro i
    have h := hP.diag_nonneg (i := i)
    have h2 : (1 - P * Pᴴ) i i = ((1 - ∑ j, ‖P i j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj']
    rw [h2] at h
    have := Complex.zero_le_real.mp h
    linarith
  have hQcol : ∀ i, ∑ j, ‖Q j i‖ ^ 2 ≤ 1 := by
    intro i
    have h := hQ.diag_nonneg (i := i)
    have h2 : (1 - Qᴴ * Q) i i = ((1 - ∑ j, ‖Q j i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul']
    rw [h2] at h
    have := Complex.zero_le_real.mp h
    linarith
  have htr : (Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) * (P * Q)).trace.re =
      ∑ i, e i * ∑ j, (P i j * Q j i).re := by
    unfold Matrix.trace
    simp only [Matrix.diag_apply, Matrix.diagonal_mul]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_apply, Complex.re_ofReal_mul, Complex.re_sum]
  rw [htr]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have hone : |∑ j, (P i j * Q j i).re| ≤ 1 := by
    calc |∑ j, (P i j * Q j i).re| ≤ ∑ j, |(P i j * Q j i).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, (‖P i j‖ ^ 2 + ‖Q j i‖ ^ 2) / 2 := Finset.sum_le_sum fun j _ => by
          have h1 : |(P i j * Q j i).re| ≤ ‖P i j‖ * ‖Q j i‖ := by
            rw [← norm_mul]
            exact Complex.abs_re_le_norm _
          nlinarith [sq_nonneg (‖P i j‖ - ‖Q j i‖)]
      _ = (∑ j, ‖P i j‖ ^ 2 + ∑ j, ‖Q j i‖ ^ 2) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
      _ ≤ 1 := by linarith [hProw i, hQcol i]
  calc |e i| * |∑ j, (P i j * Q j i).re| ≤ |e i| * 1 :=
        mul_le_mul_of_nonneg_left hone (abs_nonneg _)
    _ = |e i| := mul_one _


theorem schatten_one_herm_eq_sum {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    WHMultiplicativity.schattenNorm 1 H = ∑ i, |hH.eigenvalues i| := by
  obtain ⟨V, hVdef⟩ : ∃ V : Matrix (Fin n) (Fin n) ℂ,
      V = (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have hV1 : Vᴴ * V = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_star_mul_self _
  have hV2 : V * Vᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_mul_star_self _
  set x : Fin n → ℝ := hH.eigenvalues with hx
  have hspec : H = V * Matrix.diagonal (fun i => ((x i : ℝ) : ℂ)) * Vᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hVdef, ← Matrix.star_eq_conjTranspose]
    exact h
  have hcfc : cfc (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (Hᴴ * H) =
      V * Matrix.diagonal (fun i => ((|x i| : ℝ) : ℂ)) * Vᴴ := by
    rw [hH.eq]
    have hsa : IsSelfAdjoint H := hH.isSelfAdjoint
    have h1 : H * H = cfc (fun t : ℝ => t ^ 2) H := by
      rw [cfc_pow_id H 2, pow_two]
    have hc : Continuous (fun t : ℝ => t ^ ((1 : ℝ) / 2)) :=
      Real.continuous_rpow_const (by norm_num)
    rw [h1, ← cfc_comp' (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (fun t : ℝ => t ^ 2) H hc.continuousOn,
      hH.cfc_eq]
    unfold Matrix.IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply, ← hVdef, Matrix.star_eq_conjTranspose]
    have hd : (RCLike.ofReal ∘ (fun t : ℝ => (t ^ 2) ^ ((1 : ℝ) / 2)) ∘ hH.eigenvalues :
        Fin n → ℂ) = fun i => ((|x i| : ℝ) : ℂ) := by
      funext i
      simp only [Function.comp_apply]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
      rfl
    rw [hd]
  have hnorm : WHMultiplicativity.schattenNorm 1 H =
      (cfc (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (Hᴴ * H)).trace.re := by
    unfold WHMultiplicativity.schattenNorm
    rw [if_neg ENNReal.one_ne_top]
    simp only [ENNReal.toReal_one, div_one]
    rw [Real.rpow_one]
  rw [hnorm, hcfc, Matrix.trace_mul_cycle, hV1, Matrix.one_mul,
    Matrix.trace_diagonal, Complex.re_sum]
  simp [hx]

private lemma trace_mul_unitary_le {n : ℕ}
    (H W : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hW : Wᴴ * W = 1) :
    (H * W).trace.re ≤ WHMultiplicativity.schattenNorm 1 H := by
  let V : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary
  have hV1 : Vᴴ * V = 1 := by
    exact Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hV2 : V * Vᴴ = 1 := by
    exact Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hW2 : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  have hspec : H = V * Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Vᴴ := by
    simpa [V, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def] using hH.spectral_theorem
  have hp : (1 - (Vᴴ * W) * (Vᴴ * W)ᴴ).PosSemidef := by
    have heq : (Vᴴ * W) * (Vᴴ * W)ᴴ = 1 := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc (Vᴴ * W) * (Wᴴ * V) = Vᴴ * (W * Wᴴ) * V := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hW2, Matrix.mul_one, hV1]
    rw [heq, sub_self]; exact Matrix.PosSemidef.zero
  have hq : (1 - Vᴴ * V).PosSemidef := by
    rw [hV1, sub_self]; exact Matrix.PosSemidef.zero
  have hb := holder (Vᴴ * W) V hH.eigenvalues hp hq
  rw [schatten_one_herm_eq_sum H hH]
  calc (H * W).trace.re =
      (Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * ((Vᴴ * W) * V)).trace.re := by
        conv_lhs => rw [hspec]
        congr 1
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm V]
        simp only [Matrix.mul_assoc]
    _ ≤ |(Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * ((Vᴴ * W) * V)).trace.re| := le_abs_self _
    _ ≤ ∑ i, |hH.eigenvalues i| := hb

/-- Triangle inequality for the trace norm of Hermitian matrices. -/
theorem schatten_one_add_le {n : ℕ}
    (H K : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    WHMultiplicativity.schattenNorm 1 (H + K) ≤
      WHMultiplicativity.schattenNorm 1 H + WHMultiplicativity.schattenNorm 1 K := by
  obtain ⟨W, hW, hnorm⟩ := schatten_one_herm (H + K) (hH.add hK)
  rw [hnorm, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
  exact add_le_add (trace_mul_unitary_le H W hH hW) (trace_mul_unitary_le K W hK hW)

/-- The trace norm is unchanged by negating a matrix. -/
theorem schatten_one_neg {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 1 (-H) = WHMultiplicativity.schattenNorm 1 H := by
  simp [WHMultiplicativity.schattenNorm]

open scoped Matrix.Norms.L2Operator in
/-- The finite-dimensional trace norm is continuous. -/
theorem continuous_schatten_one (n : ℕ) :
    Continuous fun H : Matrix (Fin n) (Fin n) ℂ => WHMultiplicativity.schattenNorm 1 H := by
  have hmul : Continuous fun H : Matrix (Fin n) (Fin n) ℂ => Hᴴ * H :=
    continuous_id.matrix_conjTranspose.mul continuous_id
  have hcfc : Continuous fun H : Matrix (Fin n) (Fin n) ℂ =>
      cfc (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (Hᴴ * H) := by
    exact hmul.cfc_of_mem_nhdsSet (s := Set.univ) (fun t : ℝ => t ^ ((1 : ℝ) / 2))
      (by simp)
      (ha' := fun H => (Matrix.posSemidef_conjTranspose_mul_self H).isHermitian.isSelfAdjoint)
      (hf := (Real.continuous_rpow_const (by norm_num)).continuousOn)
  convert Complex.continuous_re.comp hcfc.matrix_trace using 1
  ext H
  simp [WHMultiplicativity.schattenNorm]

/-- Symmetry of the trace-norm distance on traceless Hermitian matrices. -/
theorem trace_distance_symm {n : ℕ} (X Y : Herm0 n) :
    WHMultiplicativity.schattenNorm 1 ((X - Y : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) =
      WHMultiplicativity.schattenNorm 1 ((Y - X : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) := by
  change WHMultiplicativity.schattenNorm 1 ((X : Matrix (Fin n) (Fin n) ℂ) -
    (Y : Matrix (Fin n) (Fin n) ℂ)) =
      WHMultiplicativity.schattenNorm 1 ((Y : Matrix (Fin n) (Fin n) ℂ) -
        (X : Matrix (Fin n) (Fin n) ℂ))
  rw [← neg_sub (Y : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ),
    schatten_one_neg]

/-- Triangle inequality in exactly the parameter space used by Proposition 5. -/
theorem trace_distance_triangle {n : ℕ} (X Y Z : Herm0 n) :
    WHMultiplicativity.schattenNorm 1 ((X - Z : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤
      WHMultiplicativity.schattenNorm 1 ((X - Y : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) +
      WHMultiplicativity.schattenNorm 1 ((Y - Z : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) := by
  have h := schatten_one_add_le
    ((X - Y : Herm0 n) : Matrix (Fin n) (Fin n) ℂ)
    ((Y - Z : Herm0 n) : Matrix (Fin n) (Fin n) ℂ)
    (X - Y).property.1 (Y - Z).property.1
  simpa only [Submodule.coe_sub, sub_add_sub_cancel] using h

/-- Two points in a trace ball of radius `r` have mutual distance at most `2r`. -/
theorem trace_ball_pair {n : ℕ} (X Y Z : Herm0 n) (r : ℝ)
    (hX : WHMultiplicativity.schattenNorm 1
      ((Y - X : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ r)
    (hZ : WHMultiplicativity.schattenNorm 1
      ((Y - Z : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ r) :
    WHMultiplicativity.schattenNorm 1
      ((Z - X : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ 2 * r := by
  have ht := trace_distance_triangle Z Y X
  rw [trace_distance_symm Z Y] at ht
  linarith

/-- Joint measurability of trace-norm distance. -/
theorem measurable_trace_distance (n : ℕ) :
    Measurable fun XY : Herm0 n × Herm0 n => WHMultiplicativity.schattenNorm 1
      ((XY.1 - XY.2 : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) := by
  have : SecondCountableTopology (Herm0 n) :=
    @TopologicalSpace.Subtype.secondCountableTopology (Fin n → Fin n → ℂ) _
      (fun X => X ∈ Herm0 n) inferInstance
  apply Continuous.measurable
  exact (continuous_schatten_one n).comp
    ((continuous_subtype_val.comp continuous_fst).sub
      (continuous_subtype_val.comp continuous_snd))

/-- The trace-distance relation at a fixed radius is a Borel set. -/
theorem measurableSet_trace_relation (n : ℕ) (r : ℝ) :
    MeasurableSet {XY : Herm0 n × Herm0 n | WHMultiplicativity.schattenNorm 1
      ((XY.1 - XY.2 : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ r} :=
  measurableSet_le (measurable_trace_distance n) measurable_const

/-- Trace balls are measurable, including for an arbitrary real radius. -/
theorem measurableSet_trace_ball {n : ℕ} (X : Herm0 n) (r : ℝ) :
    MeasurableSet {Y : Herm0 n | WHMultiplicativity.schattenNorm 1
      ((Y - X : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ r} := by
  have hc : Continuous fun Y : Herm0 n => WHMultiplicativity.schattenNorm 1
      ((Y - X : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) :=
    (continuous_schatten_one n).comp (continuous_subtype_val.sub continuous_const)
  exact (isClosed_le hc continuous_const).measurableSet

end Prop5Geometry

end
end

/- Local helper source: Solutions.Prop5TraceFrobenius -/
section
open scoped Matrix ComplexOrder ENNReal
open BosonicLearn

noncomputable section
namespace BosonicLearn.Prop5

/-- Each Hermitian eigenvalue is bounded by the Euclidean operator norm. -/
theorem abs_eigenvalue_le_operator_norm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (i : Fin n) :
    |hA.eigenvalues i| ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ := by
  let v := hA.eigenvectorBasis i
  let T := Matrix.toEuclideanCLM (𝕜 := ℂ) A
  have hv : ‖v‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have hd : star v.ofLp ⬝ᵥ (A *ᵥ v.ofLp) = inner ℂ v (T v) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM,
      dotProduct_comm]
  rw [hA.eigenvalues_eq]
  change |(star v.ofLp ⬝ᵥ (A *ᵥ v.ofLp)).re| ≤ _
  rw [hd]
  calc
    |(inner ℂ v (T v)).re| ≤ ‖inner ℂ v (T v)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖v‖ * ‖T v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖T‖ * ‖v‖) := mul_le_mul_of_nonneg_left (T.le_opNorm v) (norm_nonneg v)
    _ = ‖T‖ := by rw [hv]; ring

/-- Squared Schatten 2-norm is the trace of the Gram matrix. -/
theorem schatten_two_sq_eq_trace (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2 A ^ 2 = (Aᴴ * A).trace.re := by
  rw [schatten_two_eq_sqrt, Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg ‖A j i‖)]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.conj_mul', ← Complex.ofReal_pow]

/-- Squared Frobenius norm is the sum of squared Hermitian eigenvalues. -/
theorem schatten_two_sq_eq_eigenvalues {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    WHMultiplicativity.schattenNorm 2 A ^ 2 = ∑ i, (hA.eigenvalues i) ^ 2 := by
  have hsa : IsSelfAdjoint A := hA.isSelfAdjoint
  have hsq : A * A = cfc (fun t : ℝ => t ^ 2) A := by
    rw [cfc_pow_id A 2, pow_two]
  rw [schatten_two_sq_eq_trace, hA.eq, hsq, hA.cfc_eq]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal, Complex.re_sum]
  simp [← Complex.ofReal_pow]

/-- The Schatten interpolation bound needed to turn trace balls into Frobenius balls. -/
theorem schatten_two_sq_le_top_mul_one {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    WHMultiplicativity.schattenNorm 2 A ^ 2 ≤
      WHMultiplicativity.schattenNorm ⊤ A * WHMultiplicativity.schattenNorm 1 A := by
  rw [schatten_two_sq_eq_eigenvalues A hA, Prop5Geometry.schatten_one_herm_eq_sum A hA,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have he := abs_eigenvalue_le_operator_norm A hA i
  have hm := mul_le_mul_of_nonneg_right he (abs_nonneg (hA.eigenvalues i))
  change hA.eigenvalues i ^ 2 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ * |hA.eigenvalues i|
  nlinarith [sq_abs (hA.eigenvalues i)]

/-- Near a good center, trace radius `n*a` implies squared Frobenius radius `7*n*a`. -/
theorem trace_ball_frobenius_sq_bound {n : ℕ} (X X₀ : Herm0 n)
    (hX : X ∈ Gsupp n) (hX₀ : X₀ ∈ Ggood n) (a : ℝ)
    (ha : WHMultiplicativity.schattenNorm 1
      ((X - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ n * a) :
    WHMultiplicativity.schattenNorm 2
      ((X - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ^ 2 ≤ 7 * n * a := by
  have hop : WHMultiplicativity.schattenNorm ⊤
      ((X - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ 7 := by
    change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) ((X : Matrix (Fin n) (Fin n) ℂ) - (X₀ : Matrix (Fin n) (Fin n) ℂ))‖ ≤ _
    rw [map_sub]
    have h := norm_sub_le (Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ))
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (X₀ : Matrix (Fin n) (Fin n) ℂ))
    change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 4 at hX
    change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X₀ : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 3 at hX₀
    linarith
  have hn1 : 0 ≤ WHMultiplicativity.schattenNorm 1
      ((X - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Prop5Geometry.schatten_one_herm_eq_sum _ (X - X₀).property.1]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc
    _ ≤ WHMultiplicativity.schattenNorm ⊤
        ((X - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) *
      WHMultiplicativity.schattenNorm 1
        ((X - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) :=
      schatten_two_sq_le_top_mul_one _ (X - X₀).property.1
    _ ≤ 7 * WHMultiplicativity.schattenNorm 1
        ((X - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) :=
      mul_le_mul_of_nonneg_right hop hn1
    _ ≤ 7 * (n * a) := mul_le_mul_of_nonneg_left ha (by norm_num)
    _ = _ := by ring

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop1PriorSmallBall -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section
namespace BosonicLearn.Prop5

/-- The unnormalized Gaussian density is bounded above by Haar density one. -/
theorem gueWeight_le_haar (n : ℕ) :
    gueWeight n ≤ (Measure.addHaar : Measure (Herm0 n)) := by
  unfold gueWeight tracelessGUEWeight
  conv_rhs => rw [← withDensity_one (μ := (Measure.addHaar : Measure (Herm0 n)))]
  apply withDensity_mono
  filter_upwards [] with X
  apply ENNReal.ofReal_le_one.mpr
  apply Real.exp_le_one_iff.mpr
  have hn : (0 : ℝ) ≤ n / 4 := by positivity
  nlinarith [sq_nonneg (WHMultiplicativity.schattenNorm 2
    (X : Matrix (Fin n) (Fin n) ℂ))]

/-- Frobenius-ball volume in the original Haar measure, via Gaussian scaling. -/
theorem frobenius_ball_volume (n : ℕ) (X₀ : Herm0 n) (a : ℝ) (ha : 0 < a) :
    (Measure.addHaar : Measure (Herm0 n))
      {X | WHMultiplicativity.schattenNorm 2
        ((X - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ^ 2 ≤ 7 * n * a} ≤
      ENNReal.ofReal (Real.exp (7 * (n : ℝ)^2 / 4)) *
        ENNReal.ofReal ((Real.sqrt a) ^ Module.finrank ℝ (Herm0 n)) *
          gueWeight n Set.univ := by
  let : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → ℂ))
  let : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedSpace ℝ (Fin n → Fin n → ℂ))
  let L : Herm0 n →L[ℝ] FrobHerm0 n := (frobeniusHerm0Equiv n).toContinuousLinearMap
  have hL (X : Herm0 n) : ‖L X‖ =
      WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) :=
    norm_frobeniusMatrixEquiv n X
  have h := gaussian_small_ball_volume_linear
    (Measure.addHaar : Measure (Herm0 n)) L X₀ (n / 4) (Real.sqrt a) (7 * n * a)
      (by positivity) (Real.sqrt_pos.mpr ha)
  simp_rw [hL] at h
  have hexp : (n / 4 : ℝ) * (7 * n * a) / Real.sqrt a ^ 2 = 7 * n^2 / 4 := by
    rw [Real.sq_sqrt ha.le]
    field_simp
  rw [hexp] at h
  unfold gueWeight tracelessGUEWeight
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact h

/-- A trace ball around a good center is exponentially small in dimension.
This avoids Schatten-ball volume comparisons and all Gaussian normalization constants. -/
theorem gueWeight_trace_ball_bound (n : ℕ) (X₀ : Herm0 n) (hX₀ : X₀ ∈ Ggood n)
    (a : ℝ) (ha : 0 < a) :
    gueWeight n (herm0Ball 1 X₀ (n * a) ∩ Gsupp n) ≤
      ENNReal.ofReal (Real.exp (7 * (n : ℝ)^2 / 4)) *
        ENNReal.ofReal ((Real.sqrt a) ^ Module.finrank ℝ (Herm0 n)) *
          gueWeight n Set.univ := by
  calc
    _ ≤ (Measure.addHaar : Measure (Herm0 n))
        (herm0Ball 1 X₀ (n * a) ∩ Gsupp n) := gueWeight_le_haar n _
    _ ≤ (Measure.addHaar : Measure (Herm0 n))
        {X | WHMultiplicativity.schattenNorm 2
          ((X - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ^ 2 ≤ 7 * n * a} := by
      apply measure_mono
      intro X hX
      exact trace_ball_frobenius_sq_bound X X₀ hX.2 hX₀ a hX.1
    _ ≤ _ := frobenius_ball_volume n X₀ a ha

/-- At least half of the unconditioned Gaussian mass has operator norm at most three. -/
theorem gue_good_mass_half (n : ℕ) (hn : 1024 ≤ n) :
    (1 / 2 : ℝ≥0∞) ≤ tracelessGUE n (Ggood n) := by
  let : IsProbabilityMeasure (tracelessGUE n) := gue_probability n (by omega)
  have hG : MeasurableSet (Ggood n) := by
    have hc : Continuous (fun X : Herm0 n =>
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖) := by
      apply Continuous.norm
      exact (LinearMap.continuous_of_finiteDimensional
        ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)).comp
          continuous_subtype_val
    exact measurableSet_le hc.measurable measurable_const
  have hthreshold : 2 * Real.sqrt 2 + (1 / 8 : ℝ) ≤ 3 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hp := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have htail : tracelessGUE n (Ggood n)ᶜ ≤ (1 / 2 : ℝ≥0∞) := by
    have hset : (Ggood n)ᶜ ⊆ {X : Herm0 n | 2 * Real.sqrt 2 + (1 / 8 : ℝ) <
        WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ)} := by
      intro X hX
      exact hthreshold.trans_lt (lt_of_not_ge hX)
    calc
      _ ≤ tracelessGUE n {X | 2 * Real.sqrt 2 + (1 / 8 : ℝ) <
          WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ)} :=
        measure_mono hset
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (1 / 8 : ℝ)^2 / 4)) :=
        gue_operator_tail_proved n (by omega) (1 / 8) (by norm_num)
      _ ≤ 1 / 2 := by
        have hnreal : (1024 : ℝ) ≤ n := by exact_mod_cast hn
        have he : 4 ≤ Real.exp ((n : ℝ) / 256) := by
          have hh := Real.add_one_le_exp ((n : ℝ) / 256)
          linarith
        have hmul := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(n : ℝ) / 256)).le
        have hprod : Real.exp ((n : ℝ) / 256) * Real.exp (-(n : ℝ) / 256) = 1 := by
          rw [← Real.exp_add]
          convert Real.exp_zero using 2 <;> ring
        rw [hprod] at hmul
        have hr : 2 * Real.exp (-(n : ℝ) * (1 / 8 : ℝ)^2 / 4) ≤ 1 / 2 := by
          convert (show 2 * Real.exp (-(n : ℝ) / 256) ≤ 1 / 2 by linarith) using 2
          congr 1
          ring
        simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
          ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hr
  apply ENNReal.le_of_add_le_add_right (a := (1 / 2 : ℝ≥0∞)) (by norm_num)
  calc
    (1 / 2 : ℝ≥0∞) + 1 / 2 = 1 := ENNReal.add_halves 1
    _ = tracelessGUE n (Ggood n) + tracelessGUE n (Ggood n)ᶜ := by
      rw [measure_add_measure_compl hG, measure_univ]
    _ ≤ tracelessGUE n (Ggood n) + 1 / 2 := by gcongr

/-- The Gaussian partition function is controlled by the volume of the good operator ball. -/
theorem gue_partition_le_twice_good_volume (n : ℕ) (hn : 1024 ≤ n) :
    gueWeight n Set.univ ≤ 2 * (Measure.addHaar : Measure (Herm0 n)) (Ggood n) := by
  have hhalf := gue_good_mass_half n hn
  change (1 / 2 : ℝ≥0∞) ≤ cond (gueWeight n) Set.univ (Ggood n) at hhalf
  rw [cond_apply MeasurableSet.univ, Set.univ_inter] at hhalf
  have h := mul_le_mul_right hhalf (gueWeight n Set.univ)
  rw [← mul_assoc, ENNReal.mul_inv_cancel (ne_of_gt (gueWeight_pos n))
    (gueWeight_finite n (by omega)), one_mul] at h
  have hh := mul_le_mul_right h (2 : ℝ≥0∞)
  have hcancel : (2 : ℝ≥0∞) * (gueWeight n Set.univ * (1 / 2)) = gueWeight n Set.univ := by
    rw [mul_left_comm, one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
  rw [hcancel] at hh
  exact hh.trans (mul_le_mul le_rfl (gueWeight_le_haar n (Ggood n)) (zero_le) (zero_le))

/-- Scaling an operator ball exactly rescales its Haar volume. -/
theorem operator_ball_volume_scaling (n : ℕ) (b : ℝ) (hb : 0 < b) :
    (Measure.addHaar : Measure (Herm0 n)) (Ggood n) =
      ENNReal.ofReal ((3 / b) ^ Module.finrank ℝ (Herm0 n)) *
        (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b) := by
  let : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → ℂ))
  let : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedSpace ℝ (Fin n → Fin n → ℂ))
  let L : Herm0 n →L[ℝ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    LinearMap.toContinuousLinearMap
      (((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap.restrictScalars ℝ).comp
        (Herm0 n).subtype)
  have h := linear_ball_volume (Measure.addHaar : Measure (Herm0 n)) L (3 / b) b (by positivity)
  have hrad : 3 / b * b = 3 := by field_simp
  rw [hrad] at h
  simpa [L, herm0Ball, Ggood, WHMultiplicativity.schattenNorm] using h

/-- The partition function is controlled by the Haar volume of any positive operator ball. -/
theorem gue_partition_le_operator_ball_volume (n : ℕ) (hn : 1024 ≤ n)
    (b : ℝ) (hb : 0 < b) :
    gueWeight n Set.univ ≤
      2 * ENNReal.ofReal ((3 / b) ^ Module.finrank ℝ (Herm0 n)) *
        (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b) := by
  have h := gue_partition_le_twice_good_volume n hn
  rw [operator_ball_volume_scaling n b hb, ← mul_assoc] at h
  exact h

/-- The Gaussian weight has a uniform density lower bound on its cutoff support. -/
theorem gue_density_lower_on_support (n : ℕ) (X : Herm0 n) (hX : X ∈ Gsupp n) :
    Real.exp (-4 * (n : ℝ)^2) ≤
      Real.exp (-(n / 4 : ℝ) * WHMultiplicativity.schattenNorm 2
        (X : Matrix (Fin n) (Fin n) ℂ)^2) := by
  have hs : WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ)^2 ≤
      16 * (n : ℝ) := by
    rw [schatten_two_sq_eq_eigenvalues _ X.property.1]
    calc
      _ ≤ ∑ _ : Fin n, (16 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have h := abs_eigenvalue_le_operator_norm (X : Matrix (Fin n) (Fin n) ℂ)
          X.property.1 i
        have hh : |X.property.1.eigenvalues i| ≤ 4 := h.trans hX
        nlinarith [sq_abs (X.property.1.eigenvalues i), abs_nonneg (X.property.1.eigenvalues i)]
      _ = 16 * (n : ℝ) := by simp; ring
  apply Real.exp_le_exp.mpr
  have hn : (0 : ℝ) ≤ n / 4 := by positivity
  have hm := mul_le_mul_of_nonneg_left hs hn
  nlinarith

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5Dimension -/
section
/-! Coarse dimension bounds for traceless Hermitian matrices.  The lower bound
uses the off-diagonal rectangular block and does not require an explicit basis
of the whole traceless Hermitian space. -/

namespace BosonicLearn.Prop5

open Module

/-- Embed a rectangular complex matrix as a traceless Hermitian off-diagonal
block. This is linear over the reals. -/
noncomputable def offDiagonalHerm0 (m l : ℕ) :
    Matrix (Fin m) (Fin l) ℂ →ₗ[ℝ] Herm0 (m + l) where
  toFun A := ⟨(Matrix.fromBlocks 0 A A.conjTranspose 0).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm, by
    refine ⟨(Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero rfl
      Matrix.isHermitian_zero).submatrix _, ?_⟩
    apply Finset.sum_eq_zero
    intro i hi
    change Matrix.fromBlocks 0 A A.conjTranspose 0
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm i) = 0
    cases finSumFinEquiv.symm i <;> rfl⟩
  map_add' A B := by
    apply Subtype.ext
    ext i j
    change Matrix.fromBlocks 0 (A + B) (A + B).conjTranspose 0
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) =
        Matrix.fromBlocks 0 A A.conjTranspose 0
          (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) +
        Matrix.fromBlocks 0 B B.conjTranspose 0
          (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
    cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;>
      simp [Matrix.fromBlocks, Matrix.conjTranspose_apply]
  map_smul' c A := by
    apply Subtype.ext
    ext i j
    change Matrix.fromBlocks 0 (c • A) (c • A).conjTranspose 0
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) =
        c • Matrix.fromBlocks 0 A A.conjTranspose 0
          (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
    cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;>
      simp [Matrix.fromBlocks, Matrix.conjTranspose_apply]

theorem offDiagonalHerm0_injective (m l : ℕ) :
    Function.Injective (offDiagonalHerm0 m l) := by
  intro A B h
  ext i j
  have h' := congrArg (fun X : Herm0 (m + l) =>
    (X : Matrix (Fin (m+l)) (Fin (m+l)) ℂ)
      (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))) h
  simpa [offDiagonalHerm0, Matrix.submatrix] using h'

/-- Each complex off-diagonal rectangular entry gives two independent real
coordinates in the traceless Hermitian space. -/
theorem herm0_finrank_rectangular (m l : ℕ) :
    2 * m * l ≤ finrank ℝ (Herm0 (m + l)) := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (offDiagonalHerm0_injective m l)
  simpa [Module.finrank_matrix, Complex.finrank_real_complex, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using h

/-- The ambient complex matrix space gives a coarse dimension upper bound. -/
theorem herm0_finrank_upper (n : ℕ) :
    finrank ℝ (Herm0 n) ≤ 2 * n ^ 2 := by
  have h := (Herm0 n).finrank_le
  simpa [Module.finrank_matrix, Complex.finrank_real_complex, pow_two,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

/-- A quadratic lower bound sufficient for the Gaussian volume comparison. -/
theorem herm0_finrank_lower {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ 2 / 4 ≤ (finrank ℝ (Herm0 n) : ℝ) := by
  have hm : n / 2 + (n - n / 2) = n := by omega
  have hrect := herm0_finrank_rectangular (n / 2) (n - n / 2)
  rw [hm] at hrect
  have hmBound : n ≤ 4 * (n / 2) := by omega
  have hlBound : n ≤ 2 * (n - n / 2) := by omega
  have hmReal : (n : ℝ) / 4 ≤ (n / 2 : ℕ) := by
    have : (n : ℝ) ≤ 4 * (n / 2 : ℕ) := by exact_mod_cast hmBound
    linarith
  have hlReal : (n : ℝ) / 2 ≤ (n - n / 2 : ℕ) := by
    have : (n : ℝ) ≤ 2 * (n - n / 2 : ℕ) := by exact_mod_cast hlBound
    linarith
  calc
    (n : ℝ) ^ 2 / 4 = 2 * ((n : ℝ) / 4) * ((n : ℝ) / 2) := by ring
    _ ≤ 2 * (n / 2 : ℕ) * (n - n / 2 : ℕ) := by gcongr
    _ ≤ (finrank ℝ (Herm0 n) : ℝ) := by exact_mod_cast hrect

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop1VolumeRatio -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- A sufficiently small fixed trace radius overwhelms all fixed volume distortions. -/
theorem small_scale_exponential_bound (n d : ℕ) (hn : 2 ≤ n)
    (hd : (n : ℝ)^2 / 4 ≤ (d : ℝ))
    (κ b a : ℝ) (hκ : 0 < κ) (hb : 0 < b) (ha : 0 < a)
    (hsmall : a ≤ (κ * b / 3 * Real.exp (-40))^2) :
    Real.exp (7 * (n : ℝ)^2 / 4) * (Real.sqrt a)^d * (2 * (3 / b)^d) ≤
      Real.exp (-8 * (n : ℝ)^2) * κ^d := by
  have hr : Real.sqrt a ≤ κ * b / 3 * Real.exp (-40) := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity, hsmall⟩
  have hbase : Real.sqrt a * (3 / b) ≤ κ * Real.exp (-40) := by
    have h := mul_le_mul_of_nonneg_right hr (show 0 ≤ 3 / b by positivity)
    calc
      _ ≤ (κ * b / 3 * Real.exp (-40)) * (3 / b) := h
      _ = _ := by field_simp [hb.ne']
  have hpow := pow_le_pow_left₀ (show 0 ≤ Real.sqrt a * (3 / b) by positivity) hbase d
  rw [mul_pow, mul_pow, ← Real.exp_nat_mul] at hpow
  have he2 : 2 ≤ Real.exp ((n : ℝ)^2 / 4) := by
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have he := Real.add_one_le_exp ((n : ℝ)^2 / 4)
    nlinarith
  have hexp : Real.exp (7 * (n : ℝ)^2 / 4) * 2 * Real.exp ((d : ℝ) * (-40)) ≤
      Real.exp (-8 * (n : ℝ)^2) := by
    calc
      _ ≤ Real.exp (7 * (n : ℝ)^2 / 4) * Real.exp ((n : ℝ)^2 / 4) *
          Real.exp ((d : ℝ) * (-40)) := by gcongr
      _ = Real.exp (2 * (n : ℝ)^2 - 40 * d) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  calc
    _ = (Real.exp (7 * (n : ℝ)^2 / 4) * 2) * ((Real.sqrt a)^d * (3 / b)^d) := by ring
    _ ≤ (Real.exp (7 * (n : ℝ)^2 / 4) * 2) * (κ^d * Real.exp ((d : ℝ) * (-40))) := by
      gcongr
    _ = (Real.exp (7 * (n : ℝ)^2 / 4) * 2 * Real.exp ((d : ℝ) * (-40))) * κ^d := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hexp (pow_nonneg hκ.le _)

/-- A quantitative trace-ball/operator-ball comparison obtained only from Gaussian
scaling, the GUE tail, and the dimension of the traceless Hermitian space. -/
theorem trace_weight_le_scaled_operator_volume (n : ℕ) (hn : 1024 ≤ n)
    (X₀ : Herm0 n) (hX₀ : X₀ ∈ Ggood n)
    (κ b a : ℝ) (hκ : 0 < κ) (hb : 0 < b) (ha : 0 < a)
    (hsmall : a ≤ (κ * b / 3 * Real.exp (-40))^2) :
    gueWeight n (herm0Ball 1 X₀ (n * a) ∩ Gsupp n) ≤
      ENNReal.ofReal (Real.exp (-8 * (n : ℝ)^2)) *
        ENNReal.ofReal (κ ^ Module.finrank ℝ (Herm0 n)) *
          (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b) := by
  let d := Module.finrank ℝ (Herm0 n)
  have hr := small_scale_exponential_bound n d (by omega)
    (herm0_finrank_lower (by omega)) κ b a hκ hb ha hsmall
  calc
    _ ≤ ENNReal.ofReal (Real.exp (7 * (n : ℝ)^2 / 4)) *
        ENNReal.ofReal ((Real.sqrt a)^d) * gueWeight n Set.univ :=
      gueWeight_trace_ball_bound n X₀ hX₀ a ha
    _ ≤ ENNReal.ofReal (Real.exp (7 * (n : ℝ)^2 / 4)) *
        ENNReal.ofReal ((Real.sqrt a)^d) *
          (2 * ENNReal.ofReal ((3 / b)^d) *
            (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) := by
      gcongr
      exact gue_partition_le_operator_ball_volume n hn b hb
    _ = ENNReal.ofReal (Real.exp (7 * (n : ℝ)^2 / 4) * (Real.sqrt a)^d * (2 * (3 / b)^d)) *
          (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by norm_num)]
      norm_num
      ring
    _ ≤ ENNReal.ofReal (Real.exp (-8 * (n : ℝ)^2) * κ^d) *
          (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b) := by
      gcongr
    _ = _ := by rw [ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5PhotonMoment -/
section
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder
open BosonicLearn
noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 1000000

/-! ### Sectors, cyclicity and unitary diagonalization (as in `gammaFock_trace_psd`) -/

/-- The photon-number sector `N`: occupation vectors of total `N`. -/
private def sec (n N : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range (N + 1)).filter (fun w => ∑ i, w i = N)

private lemma mem_sec {n N : ℕ} (w : Fin n → ℕ) : w ∈ sec n N ↔ ∑ i, w i = N := by
  unfold sec
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun k => ?_, h⟩⟩
  rw [Finset.mem_range, ← h]
  have h2 : w k ≤ ∑ i, w i :=
    Finset.single_le_sum (f := fun i => w i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  omega

private lemma gammaFock_mul_sec {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) :
    gammaFock (A * B) u v = ∑ w ∈ sec n (∑ i, u i), gammaFock A u w * gammaFock B w v :=
  gammaFock_mul A B u v

/-- Cyclicity of the trace of `Γ` on a photon-number sector. -/
private lemma sector_trace_comm {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (N : ℕ) :
    ∑ u ∈ sec n N, gammaFock (A * B) u u = ∑ u ∈ sec n N, gammaFock (B * A) u u := by
  have h1 : ∀ (A B : Matrix (Fin n) (Fin n) ℂ), ∑ u ∈ sec n N, gammaFock (A * B) u u =
      ∑ u ∈ sec n N, ∑ w ∈ sec n N, gammaFock A u w * gammaFock B w u := by
    intro A B
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [gammaFock_mul_sec, (mem_sec u).mp hu]
  rw [h1 A B, h1 B A, Finset.sum_comm]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => mul_comm _ _

/-- Partial sums of a non-negative family are bounded by the sum of another non-negative family with the same
sector sums. -/
private lemma sum_le_of_sector {n : ℕ} (f g : (Fin n → ℕ) → ℝ) (hf : ∀ u, 0 ≤ f u)
    (hg : ∀ u, 0 ≤ g u) (h : ∀ N, ∑ u ∈ sec n N, f u = ∑ u ∈ sec n N, g u) {a : ℝ}
    (hga : HasSum g a) (s : Finset (Fin n → ℕ)) : ∑ u ∈ s, f u ≤ a := by
  set M := s.sup (fun u => ∑ i, u i) with hM
  have hdisj : ((Finset.range (M + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint (sec n) := by
    intro N _ N' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro u hu hu'
    exact hne (((mem_sec u).mp hu).symm.trans ((mem_sec u).mp hu'))
  have hsub : s ⊆ (Finset.range (M + 1)).biUnion (sec n) := by
    intro u hu
    rw [Finset.mem_biUnion]
    refine ⟨∑ i, u i, ?_, (mem_sec u).mpr rfl⟩
    rw [Finset.mem_range]
    have : ∑ i, u i ≤ M := Finset.le_sup (f := fun u : Fin n → ℕ => ∑ i, u i) hu
    omega
  calc ∑ u ∈ s, f u ≤ ∑ u ∈ (Finset.range (M + 1)).biUnion (sec n), f u :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun u _ _ => hf u
    _ = ∑ N ∈ Finset.range (M + 1), ∑ u ∈ sec n N, f u := Finset.sum_biUnion hdisj
    _ = ∑ N ∈ Finset.range (M + 1), ∑ u ∈ sec n N, g u := Finset.sum_congr rfl fun N _ => h N
    _ = ∑ u ∈ (Finset.range (M + 1)).biUnion (sec n), g u := (Finset.sum_biUnion hdisj).symm
    _ ≤ a := sum_le_hasSum _ (fun u _ => hg u) hga

/-- Two non-negative families with the same sector sums have the same sum. -/
private lemma hasSum_of_sector {n : ℕ} (f g : (Fin n → ℕ) → ℝ) (hf : ∀ u, 0 ≤ f u)
    (hg : ∀ u, 0 ≤ g u) (h : ∀ N, ∑ u ∈ sec n N, f u = ∑ u ∈ sec n N, g u) {a : ℝ}
    (hga : HasSum g a) : HasSum f a := by
  have hsum : Summable f := summable_of_sum_le hf (sum_le_of_sector f g hf hg h hga)
  have h1 : ∑' u, f u ≤ a := hasSum_le_of_sum_le hsum.hasSum (sum_le_of_sector f g hf hg h hga)
  have h2 : a ≤ ∑' u, f u :=
    hasSum_le_of_sum_le hga (sum_le_of_sector g f hg hf (fun N => (h N).symm) hsum.hasSum)
  have h3 : ∑' u, f u = a := le_antisymm h1 h2
  rw [← h3]
  exact hsum.hasSum

private lemma conj_one_sub {n : ℕ} (U D : Matrix (Fin n) (Fin n) ℂ) (hU1 : Uᴴ * U = 1) :
    Uᴴ * (1 - U * D * Uᴴ) * U = 1 - D := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU1]
  have h : Uᴴ * (U * D * Uᴴ) * U = (Uᴴ * U) * D * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
  rw [h, hU1, Matrix.one_mul, Matrix.mul_one]

private lemma one_sub_conj {n : ℕ} (U D : Matrix (Fin n) (Fin n) ℂ) (hU2 : U * Uᴴ = 1) :
    1 - U * D * Uᴴ = U * (1 - D) * Uᴴ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU2]

private lemma one_sub_diagonal {n : ℕ} (d : Fin n → ℝ) :
    (1 : Matrix (Fin n) (Fin n) ℂ) - Matrix.diagonal (fun i => (d i : ℂ)) =
      Matrix.diagonal (fun i => ((1 - d i : ℝ) : ℂ)) := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  congr 1
  funext i
  simp

/-- Unitary diagonalization `R = U diag(d) Uᴴ` with `0 ≤ dᵢ < 1`. -/
private lemma spectral_data {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      R = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ ∧ (∀ i, 0 ≤ d i) ∧ (∀ i, d i < 1) := by
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix (Fin n) (Fin n) ℂ,
      U = (hR.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have hU1 : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hUdef]
    exact Unitary.coe_star_mul_self _
  have hU2 : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hUdef]
    exact Unitary.coe_mul_star_self _
  have hspec : R = U * Matrix.diagonal (fun i => ((hR.1.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have h := hR.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hUdef, ← Matrix.star_eq_conjTranspose]
    exact h
  refine ⟨U, hR.1.eigenvalues, hU1, hU2, hspec, hR.eigenvalues_nonneg, ?_⟩
  have hD := conj_one_sub U (Matrix.diagonal (fun i => ((hR.1.eigenvalues i : ℝ) : ℂ))) hU1
  rw [← hspec, one_sub_diagonal] at hD
  have hpd : (Uᴴ * (1 - R) * U).PosDef :=
    hR1.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit
      (IsUnit.of_mul_eq_one _ hU2))
  rw [hD, Matrix.posDef_diagonal_iff] at hpd
  intro i
  have h := hpd i
  rw [Complex.zero_lt_real] at h
  linarith

private lemma gammaFock_diag_real {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (u : Fin n → ℕ) : (gammaFock R u u).im = 0 ∧ 0 ≤ (gammaFock R u u).re := by
  have h := gammaFock_posSemidef R hR {u} (fun _ => 1)
  simpa using h

/-! ### Diagonal entries of `Γ(diag c)` and products of series (as in `gammaFock_trace`) -/

/-- The index set of `gammaFock`: matrices `M ∈ ℕ^{n×n}` with row sums `u` and column sums `v`. -/
private def gS {n : ℕ} (u v : Fin n → ℕ) : Finset (Fin n → Fin n → ℕ) :=
  (Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin n => Finset.range (u i + 1)).filter
    (fun M => (∀ i, ∑ j, M i j = u i) ∧ ∀ j, ∑ i, M i j = v j)

/-- The box constraint is automatic. -/
private lemma mem_gS {n : ℕ} (u v : Fin n → ℕ) (M : Fin n → Fin n → ℕ) :
    M ∈ gS u v ↔ (∀ i, ∑ j, M i j = u i) ∧ ∀ j, ∑ i, M i j = v j := by
  unfold gS
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i j => ?_, h⟩
    have h1 : M i j ≤ ∑ j, M i j :=
      Finset.single_le_sum (f := fun j => M i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [h.1 i] at h1
    omega

/-- The combinatorial sum in `gammaFock`. -/
private def gSum {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) : ℂ :=
  ∑ M ∈ gS u v, ∏ i, ∏ j, R i j ^ (M i j) / (Nat.factorial (M i j) : ℂ)

private lemma gammaFock_eq {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) :
    gammaFock R u v =
      (Real.sqrt ((∏ i, (Nat.factorial (u i) : ℝ)) * ∏ j, (Nat.factorial (v j) : ℝ)) : ℂ) *
        gSum R u v := rfl

/-- For diagonal `R`, an off-diagonal nonzero entry of `M` kills the term. -/
private lemma term_diagonal_eq_zero {n : ℕ} (c : Fin n → ℂ) (M : Fin n → Fin n → ℕ) (i j : Fin n)
    (hij : i ≠ j) (h : M i j ≠ 0) :
    ∏ i, ∏ j, (Matrix.diagonal c) i j ^ (M i j) / (Nat.factorial (M i j) : ℂ) = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
  rw [Matrix.diagonal_apply_ne c hij, zero_pow h, zero_div]

/-- A matrix with vanishing off-diagonal entries and row sums `u` is `diag u`. -/
private lemma diag_of_offdiag_zero {n : ℕ} (u : Fin n → ℕ) (M : Fin n → Fin n → ℕ)
    (hrow : ∀ i, ∑ j, M i j = u i) (hoff : ∀ i j, i ≠ j → M i j = 0) (i : Fin n) :
    M i i = u i := by
  rw [← hrow i]
  exact (Finset.sum_eq_single i (fun j _ hji => hoff i j (Ne.symm hji))
    (fun h => absurd (Finset.mem_univ i) h)).symm

private lemma gSum_diagonal_self {n : ℕ} (c : Fin n → ℂ) (u : Fin n → ℕ) :
    gSum (Matrix.diagonal c) u u = ∏ i, (c i ^ u i / (Nat.factorial (u i) : ℂ)) := by
  unfold gSum
  rw [Finset.sum_eq_single (fun i j => if i = j then u i else 0)]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · intro M hM hne
    rw [mem_gS] at hM
    by_cases hoff : ∀ i j, i ≠ j → M i j = 0
    · exfalso
      apply hne
      funext i j
      by_cases hij : i = j
      · subst hij
        simp [diag_of_offdiag_zero u M hM.1 hoff i]
      · simp [hij, hoff i j hij]
    · push Not at hoff
      obtain ⟨i, j, hij, hne'⟩ := hoff
      exact term_diagonal_eq_zero c M i j hij hne'
  · intro h
    exfalso
    apply h
    rw [mem_gS]
    constructor
    · intro i
      simp
    · intro j
      simp

/-- Diagonal entries of `Γ(diag c)`. -/
theorem gammaFock_diagonal_self {n : ℕ} (c : Fin n → ℂ) (u : Fin n → ℕ) :
    gammaFock (Matrix.diagonal c) u u = ∏ i, c i ^ u i := by
  rw [gammaFock_eq, gSum_diagonal_self]
  have hpos : (0 : ℝ) ≤ ∏ i, (Nat.factorial (u i) : ℝ) :=
    Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
  rw [Real.sqrt_mul_self hpos]
  push_cast
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : ((Nat.factorial (u i) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

/-- A finite product of nonnegative convergent series is the series over `ℕⁿ` of the products. -/
private lemma hasSum_pi_prod_of_nonneg (n : ℕ) : ∀ (f : Fin n → ℕ → ℝ) (a : Fin n → ℝ),
    (∀ i k, 0 ≤ f i k) → (∀ i, HasSum (f i) (a i)) →
    HasSum (fun u : Fin n → ℕ => ∏ i, f i (u i)) (∏ i, a i) := by
  induction n with
  | zero =>
    intro f a _ _
    simp
  | succ n ih =>
    intro f a hf0 hf
    have ih' := ih (fun i => f i.succ) (fun i => a i.succ)
      (fun i k => hf0 i.succ k) (fun i => hf i.succ)
    have hsum : Summable (fun p : ℕ × (Fin n → ℕ) => f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i)) :=
      Summable.mul_of_nonneg (f := f 0) (g := fun u : Fin n → ℕ => ∏ i : Fin n, f i.succ (u i))
        (hf 0).summable ih'.summable (fun k => hf0 0 k)
        (fun u => Finset.prod_nonneg fun i _ => hf0 i.succ (u i))
    have hmul : HasSum (fun p : ℕ × (Fin n → ℕ) => f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i))
        (a 0 * ∏ i : Fin n, a i.succ) :=
      HasSum.mul (f := f 0) (g := fun u : Fin n → ℕ => ∏ i : Fin n, f i.succ (u i)) (hf 0) ih' hsum
    rw [Fin.prod_univ_succ]
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).hasSum_iff]
    refine hmul.congr_fun fun p => ?_
    simp [Fin.prod_univ_succ, Fin.consEquiv]

theorem gammaFock_diagonal_re {n : ℕ} (d : Fin n → ℝ) (u : Fin n → ℕ) :
    (gammaFock (Matrix.diagonal fun i => (d i : ℂ)) u u).re = ∏ i, d i ^ u i := by
  simp only [gammaFock_diagonal_self, ← Complex.ofReal_pow, ← Complex.ofReal_prod,
    Complex.ofReal_re]


/-- The second moment series of an unnormalized geometric distribution. -/
theorem hasSum_sq_mul_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun k : ℕ => (k : ℝ) ^ 2 * r ^ k) (r * (1 + r) / (1 - r) ^ 3) := by
  have hr : ‖r‖ < 1 := by simpa [Real.norm_of_nonneg hr0] using hr1
  have hne : 1 - r ≠ 0 := by linarith
  have hc := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hr).mul_left 2
  have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hr).mul_left 3
  have h0 := (hasSum_geometric_of_lt_one hr0 hr1).mul_left 2
  have hcval (k : ℕ) : 2 * (((k + 2).choose 2 : ℕ) : ℝ) =
      (k : ℝ) ^ 2 + 3 * k + 2 := by
    have hnat : 2 * (k + 2).choose 2 = (k + 2) * (k + 1) := by
      rw [Nat.choose_two_right]
      have heven := Nat.even_mul_pred_self (k + 2)
      simpa [Nat.add_sub_cancel] using (Nat.mul_div_cancel' heven.two_dvd)
    have hcast := congrArg (fun m : ℕ => (m : ℝ)) hnat
    push_cast at hcast
    nlinarith
  have h := (hc.sub h1).sub h0
  have hval : 2 * (1 / (1 - r) ^ (2 + 1)) - 3 * (r / (1 - r) ^ 2) -
      2 * (1 - r)⁻¹ = r * (1 + r) / (1 - r) ^ 3 := by
    field_simp
    ring
  rw [hval] at h
  refine h.congr_fun fun k => ?_
  have hh := hcval k
  linear_combination -r ^ k * hh

/-- Mean and second moment of the geometric law on `0,1,…`. -/
theorem geometric_moments {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun k : ℕ => (1 - r) * r ^ k) 1 ∧
    HasSum (fun k : ℕ => (k : ℝ) * ((1 - r) * r ^ k)) (r / (1 - r)) ∧
    HasSum (fun k : ℕ => (k : ℝ) ^ 2 * ((1 - r) * r ^ k))
      (r / (1 - r) + 2 * (r / (1 - r)) ^ 2) := by
  have hne : 1 - r ≠ 0 := by linarith
  have hr : ‖r‖ < 1 := by simpa [Real.norm_of_nonneg hr0] using hr1
  constructor
  · have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (1 - r)
    rwa [mul_inv_cancel₀ hne] at h
  constructor
  · have h := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hr).mul_left (1 - r)
    have hv : (1 - r) * (r / (1 - r) ^ 2) = r / (1 - r) := by field_simp
    rw [hv] at h
    exact h.congr_fun fun k => by ring
  · have h := (hasSum_sq_mul_geometric hr0 hr1).mul_left (1 - r)
    have hv : (1 - r) * (r * (1 + r) / (1 - r) ^ 3) =
        r / (1 - r) + 2 * (r / (1 - r)) ^ 2 := by field_simp; ring
    rw [hv] at h
    exact h.congr_fun fun k => by ring

private lemma hasSum_pair_nonneg {A B : Type} {f : A → ℝ} {g : B → ℝ} {a b : ℝ}
    (hf : HasSum f a) (hg : HasSum g b) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    HasSum (fun p : A × B => f p.1 * g p.2) (a * b) :=
  hf.mul hg (hf.summable.mul_of_nonneg hg.summable hf0 hg0)

/-- First and second moments add in the usual way for independent discrete coordinates. -/
theorem independent_sum_moments (n : ℕ) :
    ∀ (p : Fin n → ℕ → ℝ) (m v : Fin n → ℝ),
      (∀ i k, 0 ≤ p i k) →
      (∀ i, HasSum (p i) 1) →
      (∀ i, HasSum (fun k : ℕ => (k : ℝ) * p i k) (m i)) →
      (∀ i, HasSum (fun k : ℕ => (k : ℝ) ^ 2 * p i k) (v i + (m i) ^ 2)) →
      HasSum (fun u : Fin n → ℕ => ∏ i, p i (u i)) 1 ∧
      HasSum (fun u : Fin n → ℕ => (∑ i, (u i : ℝ)) * ∏ i, p i (u i)) (∑ i, m i) ∧
      HasSum (fun u : Fin n → ℕ => (∑ i, (u i : ℝ)) ^ 2 * ∏ i, p i (u i))
        ((∑ i, v i) + (∑ i, m i) ^ 2) := by
  induction n with
  | zero =>
    intro p m v _ _ _ _
    simp
  | succ n ih =>
    intro p m v hp h0 h1 h2
    obtain ⟨hP, hM, hS⟩ := ih (fun i => p i.succ) (fun i => m i.succ) (fun i => v i.succ)
      (fun i k => hp i.succ k) (fun i => h0 i.succ)
      (fun i => h1 i.succ) (fun i => h2 i.succ)
    have hp0 : ∀ u : Fin n → ℕ, 0 ≤ ∏ i, p i.succ (u i) :=
      fun u => Finset.prod_nonneg fun i _ => hp i.succ (u i)
    have hm0 : ∀ u : Fin n → ℕ, 0 ≤ (∑ i, (u i : ℝ)) * ∏ i, p i.succ (u i) :=
      fun u => mul_nonneg (Finset.sum_nonneg fun i _ => Nat.cast_nonneg _) (hp0 u)
    have hs0 : ∀ u : Fin n → ℕ, 0 ≤ (∑ i, (u i : ℝ)) ^ 2 * ∏ i, p i.succ (u i) :=
      fun u => mul_nonneg (sq_nonneg _) (hp0 u)
    have hk1 : ∀ k : ℕ, 0 ≤ (k : ℝ) * p 0 k := fun k => mul_nonneg (Nat.cast_nonneg _) (hp 0 k)
    have hk2 : ∀ k : ℕ, 0 ≤ (k : ℝ) ^ 2 * p 0 k := fun k => mul_nonneg (sq_nonneg _) (hp 0 k)
    constructor
    · have h := hasSum_pair_nonneg (h0 0) hP (hp 0) hp0
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).hasSum_iff]
      convert h using 1
      · ext u
        simp [Fin.consEquiv, Fin.prod_univ_succ]
      · norm_num
    constructor
    · have h := (hasSum_pair_nonneg (h1 0) hP hk1 hp0).add
        (hasSum_pair_nonneg (h0 0) hM (hp 0) hm0)
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).hasSum_iff]
      convert h using 1
      · ext u
        simp [Fin.consEquiv, Fin.prod_univ_succ, Fin.sum_univ_succ]
        ring
      · simp [Fin.sum_univ_succ]
    · have h := ((hasSum_pair_nonneg (h2 0) hP hk2 hp0).add
        ((hasSum_pair_nonneg (h1 0) hM hk1 hm0).mul_left 2)).add
          (hasSum_pair_nonneg (h0 0) hS (hp 0) hs0)
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).hasSum_iff]
      convert h using 1
      · ext u
        simp [Fin.consEquiv, Fin.prod_univ_succ, Fin.sum_univ_succ]
        ring
      · simp only [Fin.sum_univ_succ]
        ring

/-- The second moment of a sum of independent geometric occupations. -/
theorem geometric_sum_second_moment {n : ℕ} (d : Fin n → ℝ)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i < 1) :
    HasSum (fun u : Fin n → ℕ => (∑ i, (u i : ℝ)) ^ 2 *
      ∏ i, ((1 - d i) * d i ^ u i))
      ((∑ i, (d i / (1 - d i) + (d i / (1 - d i)) ^ 2)) +
        (∑ i, d i / (1 - d i)) ^ 2) := by
  apply (independent_sum_moments n
    (fun i k => (1 - d i) * d i ^ k)
    (fun i => d i / (1 - d i))
    (fun i => d i / (1 - d i) + (d i / (1 - d i)) ^ 2)
    (fun i k => mul_nonneg (by linarith [hd1 i]) (pow_nonneg (hd0 i) k))
    (fun i => (geometric_moments (hd0 i) (hd1 i)).1)
    (fun i => (geometric_moments (hd0 i) (hd1 i)).2.1)
    (fun i => ?_)).2.2
  convert (geometric_moments (hd0 i) (hd1 i)).2.2 using 1
  ring

/-- The actual diagonal Born weights have the same total photon moments as the eigenmode geometries. -/
theorem hasSum_photon_second_moment {n : ℕ} (R U : Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → ℝ) (hR : R.PosSemidef) (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (hspec : R = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i < 1) :
    HasSum (fun u : Occupation (Fin n) => (∑ i, (u i : ℝ)) ^ 2 * (fugacityCoeff R u u).re)
      ((∑ i, (d i / (1 - d i) + (d i / (1 - d i)) ^ 2)) +
        (∑ i, d i / (1 - d i)) ^ 2) := by
  have hdet : (1 - R).det = ((∏ i, (1 - d i) : ℝ) : ℂ) := by
    rw [hspec, one_sub_conj U _ hU2, one_sub_diagonal, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_diagonal, mul_right_comm, ← Matrix.det_mul, hU2, Matrix.det_one, one_mul,
      Complex.ofReal_prod]
  have hpos : 0 < ∏ i, (1 - d i) := Finset.prod_pos fun i _ => by linarith [hd1 i]
  have hx : ∀ u, (fugacityCoeff R u u).re = (∏ i, (1 - d i)) * (gammaFock R u u).re := by
    intro u
    unfold fugacityCoeff
    rw [Matrix.smul_apply, smul_eq_mul, hdet, Complex.re_ofReal_mul]
  have hx0 : ∀ u, 0 ≤ (fugacityCoeff R u u).re := fun u => by
    rw [hx]
    exact mul_nonneg hpos.le (gammaFock_diag_real R hR u).2
  have hsec0 : ∀ N, ∑ u ∈ sec n N, (gammaFock R u u).re =
      ∑ u ∈ sec n N, ∏ i, d i ^ u i := by
    intro N
    have h := sector_trace_comm (U * Matrix.diagonal (fun i => (d i : ℂ))) Uᴴ N
    rw [← hspec, ← Matrix.mul_assoc, hU1, Matrix.one_mul] at h
    rw [← Complex.re_sum, h, Complex.re_sum]
    exact Finset.sum_congr rfl fun u _ => gammaFock_diagonal_re d u
  apply hasSum_of_sector
    (fun u : Fin n → ℕ => (∑ i, (u i : ℝ)) ^ 2 * (fugacityCoeff R u u).re)
    (fun u : Fin n → ℕ => (∑ i, (u i : ℝ)) ^ 2 * ∏ i, ((1 - d i) * d i ^ u i))
    (fun u => mul_nonneg (sq_nonneg _) (hx0 u))
    (fun u => mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun i _ =>
      mul_nonneg (by linarith [hd1 i]) (pow_nonneg (hd0 i) _)))
    ?_ (geometric_sum_second_moment d hd0 hd1)
  intro N
  have hc : ∀ x : (Fin n → ℕ) → ℝ,
      ∑ u ∈ sec n N, (∑ i, (u i : ℝ)) ^ 2 * ((∏ i, (1 - d i)) * x u) =
        ((N : ℝ) ^ 2 * ∏ i, (1 - d i)) * ∑ u ∈ sec n N, x u := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [← Nat.cast_sum, (mem_sec u).mp hu]
    ring
  simp_rw [hx, Finset.prod_mul_distrib]
  rw [hc, hc, hsec0 N]

private lemma diagonal_upper_bound {n : ℕ} (R U : Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → ℝ) (b : ℝ) (hU1 : Uᴴ * U = 1)
    (hspec : R = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ)
    (hb : ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - R).PosSemidef) :
    ∀ i, d i ≤ b := by
  have h := hb.conjTranspose_mul_mul_same U
  have heq : Uᴴ * ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - R) * U =
      Matrix.diagonal (fun i => ((b - d i : ℝ) : ℂ)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hU1]
    have heq' : Uᴴ * R * U = Matrix.diagonal (fun i => (d i : ℂ)) := by
      rw [hspec]
      calc Uᴴ * (U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) * U =
          (Uᴴ * U) * Matrix.diagonal (fun i => (d i : ℂ)) * (Uᴴ * U) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU1, Matrix.one_mul, Matrix.mul_one]
    rw [heq', ← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    congr 1
    ext i
    simp
  rw [heq, Matrix.posSemidef_diagonal_iff] at h
  intro i
  have hi := Complex.zero_le_real.mp (h i)
  linarith

/-- The scalar estimate used in Eq. (92), with room in its numerical constant. -/
theorem occupation_moment_bound {n : ℕ} (ν : ℝ) (hn : 1 ≤ n)
    (hν : 1 / (n : ℝ) ≤ ν) (hν1 : ν ≤ 1) (m : Fin n → ℝ)
    (hm0 : ∀ i, 0 ≤ m i) (hm1 : ∀ i, m i ≤ 2 * ν) :
    (∑ i, (m i + (m i) ^ 2)) + (∑ i, m i) ^ 2 ≤ 12 * ν ^ 2 * n ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hν0 : 0 < ν := (one_div_pos.mpr hn0).trans_le hν
  have hnν : 1 ≤ ν * n := (div_le_iff₀ hn0).mp hν
  have hm_sq : ∀ i, (m i) ^ 2 ≤ 4 * ν ^ 2 := by
    intro i
    nlinarith [hm0 i, hm1 i]
  have hv : ∑ i, (m i + (m i) ^ 2) ≤ 6 * ν * n := by
    calc ∑ i, (m i + (m i) ^ 2) ≤ ∑ _i : Fin n, (2 * ν + 4 * ν ^ 2) :=
        Finset.sum_le_sum fun i _ => add_le_add (hm1 i) (hm_sq i)
      _ = (2 * ν + 4 * ν ^ 2) * n := by simp; ring
      _ ≤ 6 * ν * n := by
        apply mul_le_mul_of_nonneg_right _ hn0.le
        nlinarith
  have hsum0 : 0 ≤ ∑ i, m i := Finset.sum_nonneg fun i _ => hm0 i
  have hsum1 : ∑ i, m i ≤ 2 * ν * n := by
    calc ∑ i, m i ≤ ∑ _i : Fin n, 2 * ν := Finset.sum_le_sum fun i _ => hm1 i
      _ = _ := by simp; ring
  have hsquare : (∑ i, m i) ^ 2 ≤ 4 * ν ^ 2 * n ^ 2 := by
    nlinarith
  have hlarge : ν * n ≤ ν ^ 2 * n ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnν) (mul_nonneg hν0.le hn0.le)]
  nlinarith [sq_nonneg (ν * n)]

/-- A spectral upper bound implies the required second moment bound for actual photon counting. -/
theorem photon_second_moment_le_of_spectral_bound {n : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef) (hR1 : (1 - R).PosDef)
    (ν : ℝ) (hn : 1 ≤ n) (hν : 1 / (n : ℝ) ≤ ν) (hν1 : ν ≤ 1)
    (hupper : (((2 * ν / (1 + 2 * ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - R).PosSemidef) :
    ∑' u : Occupation (Fin n), ENNReal.ofReal ((∑ i, (u i : ℝ)) ^ 2) *
      ENNReal.ofReal (fugacityCoeff R u u).re ≤ ENNReal.ofReal (12 * ν ^ 2 * n ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hν0 : 0 < ν := (one_div_pos.mpr hn0).trans_le hν
  obtain ⟨U, d, hU1, hU2, hspec, hd0, hd1⟩ := spectral_data R hR hR1
  have hdu := diagonal_upper_bound R U d (2 * ν / (1 + 2 * ν)) hU1 hspec hupper
  have hm0 : ∀ i, 0 ≤ d i / (1 - d i) := fun i => div_nonneg (hd0 i) (by linarith [hd1 i])
  have hmu : ∀ i, d i / (1 - d i) ≤ 2 * ν := by
    intro i
    apply (div_le_iff₀ (by linarith [hd1 i])).mpr
    have h := (le_div_iff₀ (by positivity : 0 < 1 + 2 * ν)).mp (hdu i)
    nlinarith
  have hsum := hasSum_photon_second_moment R U d hR hU1 hU2 hspec hd0 hd1
  have hdet : (1 - R).det = ((∏ i, (1 - d i) : ℝ) : ℂ) := by
    rw [hspec, one_sub_conj U _ hU2, one_sub_diagonal, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_diagonal, mul_right_comm, ← Matrix.det_mul, hU2, Matrix.det_one, one_mul,
      Complex.ofReal_prod]
  have hx0 : ∀ u, 0 ≤ (fugacityCoeff R u u).re := by
    intro u
    unfold fugacityCoeff
    rw [Matrix.smul_apply, smul_eq_mul, hdet, Complex.re_ofReal_mul]
    exact mul_nonneg (Finset.prod_nonneg fun i _ => by linarith [hd1 i])
      (gammaFock_diag_real R hR u).2
  have htotal : (∑' u : Occupation (Fin n), ENNReal.ofReal ((∑ i, (u i : ℝ)) ^ 2) *
      ENNReal.ofReal (fugacityCoeff R u u).re) =
      ENNReal.ofReal ((∑ i, (d i / (1 - d i) + (d i / (1 - d i)) ^ 2)) +
        (∑ i, d i / (1 - d i)) ^ 2) := by
    rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg
      (fun u => mul_nonneg (sq_nonneg _) (hx0 u)) hsum.summable]
    exact tsum_congr fun u => (ENNReal.ofReal_mul (sq_nonneg _)).symm
  rw [htotal]
  exact ENNReal.ofReal_le_ofReal (occupation_moment_bound ν hn hν hν1 _ hm0 hmu)

theorem opnorm_form {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian) (c : ℝ)
    (h : WHMultiplicativity.schattenNorm ⊤ X ≤ c) :
    (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - X).PosSemidef ∧
      (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X).PosSemidef := by
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖ ≤ c := by
    simpa [WHMultiplicativity.schattenNorm] using h
  have key : ∀ v : Fin n → ℂ, |(star v ⬝ᵥ (X *ᵥ v)).re| ≤ c * ∑ i, ‖v i‖ ^ 2 := by
    intro v
    set w : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v with hw
    have h1 : inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) X w) = star v ⬝ᵥ (X *ᵥ v) := by
      rw [hw, Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    have h2 : ‖inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) X w)‖ ≤ c * ‖w‖ ^ 2 := by
      calc ‖inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) X w)‖
          ≤ ‖w‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X w‖ := norm_inner_le_norm _ _
        _ ≤ ‖w‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖ * ‖w‖) :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ ‖w‖ * (c * ‖w‖) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)) (norm_nonneg _)
        _ = c * ‖w‖ ^ 2 := by ring
    have h3 : ‖w‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
    rw [h1, h3] at h2
    exact (Complex.abs_re_le_norm _).trans h2
  have hsq : ∀ v : Fin n → ℂ, star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    simp only [dotProduct, Pi.star_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  have him : ∀ v : Fin n → ℂ, (star v ⬝ᵥ (X *ᵥ v)).im = 0 := fun v =>
    hX.im_star_dotProduct_mulVec_self v
  have hc1 : (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  constructor
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hc1.sub hX) fun v => ?_
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      hsq, Complex.nonneg_iff]
    have hk := abs_le.mp (key v)
    constructor
    · simp only [Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      linarith [hk.2]
    · rw [Complex.sub_im, him v, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_im, sub_zero]
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hc1.add hX) fun v => ?_
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      hsq, Complex.nonneg_iff]
    have hk := abs_le.mp (key v)
    constructor
    · simp only [Complex.add_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      linarith [hk.1]
    · rw [Complex.add_im, him v, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_im, add_zero]


/-- Fugacity matrices in the hard family have eigenvalues at most `2ν/(1+2ν)`. -/
theorem family_spectral_bounds {n : ℕ} (ν ξ : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 32) (X : Herm0 n) (hX : X ∈ Gsupp n) :
    (fugacityFamily ν ξ X).PosSemidef ∧ (1 - fugacityFamily ν ξ X).PosDef ∧
    ((((2 * ν / (1 + 2 * ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) -
      fugacityFamily ν ξ X).PosSemidef := by
  have hXh : (X : Matrix (Fin n) (Fin n) ℂ).IsHermitian := X.2.1
  have hop : WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ) ≤ 4 := hX
  obtain ⟨hminus, hplus⟩ := opnorm_form (X : Matrix (Fin n) (Fin n) ℂ) hXh 4 hop
  have h14 : 0 < 1 - 4 * ξ := by linarith
  have h14' : 1 - 4 * ξ ≠ 0 := h14.ne'
  have h1ν : 1 + ν ≠ 0 := by positivity
  set r : ℝ := ν / ((1 - 4 * ξ) * (1 + ν)) with hr
  have hrpos : 0 < r := by positivity
  have hrt : r * (1 - 4 * ξ) = ν / (1 + ν) := by
    rw [hr]
    field_simp
  have hRdef : fugacityFamily ν ξ X =
      ((r : ℝ) : ℂ) • (1 + ((ξ : ℝ) : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)) := rfl
  have e1 : fugacityFamily ν ξ X - ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
      ((r * ξ : ℝ) : ℂ) • (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (X : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hRdef, ← hrt]
    ext a b
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hRν : (fugacityFamily ν ξ X -
      ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
    rw [e1]
    exact hplus.smul (Complex.zero_le_real.mpr (by positivity))
  have hRpsd : (fugacityFamily ν ξ X).PosSemidef := by
    have e : fugacityFamily ν ξ X = (fugacityFamily ν ξ X -
        ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) +
        ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [sub_add_cancel]
    rw [e]
    exact hRν.add (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by positivity)))
  let b : ℝ := 2 * ν / (1 + 2 * ν)
  have hb1 : b < 1 := by
    dsimp [b]
    apply (div_lt_one (by positivity)).mpr
    linarith
  have hr_bound : r * (1 + 4 * ξ) ≤ b := by
    rw [hr, div_mul_eq_mul_div]
    dsimp [b]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hξν : ξ * ν ≤ ξ := by nlinarith
    have hsmall : 0 ≤ 1 - 12 * ξ - 16 * ξ * ν := by nlinarith
    nlinarith [mul_nonneg hν0.le hsmall]
  have heq : (b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - fugacityFamily ν ξ X =
      ((b - r * (1 + 4 * ξ) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        ((r * ξ : ℝ) : ℂ) • (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
          (X : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hRdef]
    ext a b
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hu : ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - fugacityFamily ν ξ X).PosSemidef := by
    rw [heq]
    exact (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hr_bound))).add
      (hminus.smul (Complex.zero_le_real.mpr (by positivity)))
  have hp : (1 - fugacityFamily ν ξ X).PosDef := by
    have he : 1 - fugacityFamily ν ξ X =
        ((1 - b : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
          ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - fugacityFamily ν ξ X) := by
      push_cast
      module
    rw [he]
    exact (Matrix.PosDef.one.smul (by exact_mod_cast (sub_pos.mpr hb1))).add_posSemidef hu
  exact ⟨hRpsd, hp, hu⟩

/-- Eq. (92): the actual total photon count in the hard family has second moment at most `12ν²n²`. -/
theorem fugacity_count_second_moment {n : ℕ} (ν ξ : ℝ) (hn : 1 ≤ n)
    (hν : 1 / (n : ℝ) ≤ ν) (hν1 : ν ≤ 1) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (X : Herm0 n) (hX : X ∈ Gsupp n) :
    ∑' u : Occupation (Fin n), ENNReal.ofReal ((∑ i, (u i : ℝ)) ^ 2) *
      ENNReal.ofReal (fugacityCoeff (fugacityFamily ν ξ X) u u).re ≤
        ENNReal.ofReal (12 * ν ^ 2 * n ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hν0 : 0 < ν := (one_div_pos.mpr hn0).trans_le hν
  obtain ⟨hR, hR1, hu⟩ := family_spectral_bounds ν ξ hν0 hν1 hξ hξ32 X hX
  exact photon_second_moment_le_of_spectral_bound _ hR hR1 ν hn hν hν1 hu


/-- Regrouping nonnegative second-moment weights by a count statistic. -/
theorem count_second_moment_regroup {I : Type} (c : I → ℕ) (p : I → ℝ≥0∞) :
    (∑' k : ℕ, ENNReal.ofReal ((k : ℝ) ^ 2) *
      ∑' u : I, if c u = k then p u else 0) =
      ∑' u : I, ENNReal.ofReal ((c u : ℝ) ^ 2) * p u := by
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun u => ?_
  rw [tsum_eq_single (c u)]
  · simp
  · intro k hk
    simp [Ne.symm hk]

/-- Eq. (92) expressed using the distribution of the scalar total photon count. -/
theorem fugacity_count_distribution_second_moment {n : ℕ} (ν ξ : ℝ) (hn : 1 ≤ n)
    (hν : 1 / (n : ℝ) ≤ ν) (hν1 : ν ≤ 1) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (X : Herm0 n) (hX : X ∈ Gsupp n) :
    ∑' k : ℕ, ENNReal.ofReal ((k : ℝ) ^ 2) *
      (∑' u : Occupation (Fin n), if ∑ i, u i = k then
        ENNReal.ofReal (fugacityCoeff (fugacityFamily ν ξ X) u u).re else 0) ≤
          ENNReal.ofReal (12 * ν ^ 2 * n ^ 2) := by
  rw [count_second_moment_regroup]
  simp only [Nat.cast_sum]
  exact fugacity_count_second_moment ν ξ hn hν hν1 hξ hξ32 X hX

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5PhiSupport -/
section
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 800000

theorem matrix_entry_le_operator_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖A i j‖ ≤ ‖A‖ := by
  let e := EuclideanSpace.basisFun (Fin n) ℂ
  have hi : ‖e i‖ = 1 := e.orthonormal.norm_eq_one i
  have hj : ‖e j‖ = 1 := e.orthonormal.norm_eq_one j
  have h := norm_inner_le_norm (𝕜 := ℂ) (e i) (Matrix.toEuclideanCLM (𝕜 := ℂ) A (e j))
  have he : inner ℂ (e i) (Matrix.toEuclideanCLM (𝕜 := ℂ) A (e j)) = A i j := by
    rw [EuclideanSpace.basisFun_inner]
    simp [e, EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct]
  rw [he, hi, one_mul] at h
  have hb := (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm (e j)
  rw [hj, mul_one] at hb
  exact h.trans hb

theorem matrix_trace_le_operator_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.trace‖ ≤ n * ‖A‖ := by
  calc
    ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin n, ‖A‖ := Finset.sum_le_sum fun i _ => matrix_entry_le_operator_norm A i i
    _ = n * ‖A‖ := by simp

/-- The local relative parametrization stays in the prior support throughout
the full parameter range used by the hard family. Only support is asserted;
the derivative/Jacobian claims of Lemma 8 are not needed here. -/
theorem PhiMap_mem_Gsupp {n : ℕ} (hn : 1 ≤ n) (X : Herm0 n) (hX : X ∈ Ggood n)
    (ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (Z : Herm0 n) (hZ : Z ∈ herm0Ball ⊤ 0 (1 / 10)) :
    PhiMap X ξ Z ∈ Gsupp n := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  letI : NeZero n := ⟨by omega⟩
  have hXnorm : ‖(X : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 3 := hX
  have hZnorm : ‖(Z : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 / 10 := by
    change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (Z : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 / 10
    simpa [herm0Ball, WHMultiplicativity.schattenNorm] using hZ
  let S : Matrix (Fin n) (Fin n) ℂ := 1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)
  let d : ℂ := 1 + (ξ : ℂ) ^ 2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
  let T : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt S * (Z : Matrix (Fin n) (Fin n) ℂ) * CFC.sqrt S
  let e : ℂ := (ξ : ℂ) * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
  have hSp : S.PosSemidef := by
    have hx := (opnorm_form (X : Matrix (Fin n) (Fin n) ℂ) X.property.1 3 hX).2
    have he : S = ((1 - 3 * ξ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (ξ : ℂ) • ((3 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X) := by
      dsimp [S]
      push_cast
      module
    rw [he]
    exact (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by linarith))).add
      (hx.smul (Complex.zero_le_real.mpr hξ.le))
  have hsqrt : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S hSp.nonneg
  have hSnorm : ‖S‖ ≤ 1 + 3 * ξ := by
    calc ‖S‖ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ + ‖(ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)‖ := norm_add_le _ _
      _ = 1 + ξ * ‖(X : Matrix (Fin n) (Fin n) ℂ)‖ := by
        rw [norm_one, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ]
      _ ≤ 1 + 3 * ξ := by nlinarith only [hXnorm, hξ]
  have hTnorm : ‖T‖ ≤ (1 + 3 * ξ) / 10 := by
    calc ‖T‖ ≤ ‖CFC.sqrt S‖ * ‖(Z : Matrix (Fin n) (Fin n) ℂ)‖ * ‖CFC.sqrt S‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖CFC.sqrt S‖ * (1 / 10) * ‖CFC.sqrt S‖ := by gcongr
      _ = ‖S‖ / 10 := by rw [CFC.norm_sqrt S hSp.nonneg]; nlinarith [Real.sq_sqrt (norm_nonneg S)]
      _ ≤ (1 + 3 * ξ) / 10 := by linarith
  have htr : ‖((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace‖ ≤ n * (3 / 10) := by
    refine (matrix_trace_le_operator_norm _).trans ?_
    have hm := norm_mul_le (X : Matrix (Fin n) (Fin n) ℂ) (Z : Matrix (Fin n) (Fin n) ℂ)
    have hab : ‖(X : Matrix (Fin n) (Fin n) ℂ)‖ * ‖(Z : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 3 * (1 / 10) := by gcongr
    nlinarith only [hm, hab, hn0]
  have henorm : ‖e‖ ≤ 3 * ξ / 10 := by
    dsimp [e]
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ,
      Complex.norm_natCast]
    apply (div_le_iff₀ hn0).mpr
    nlinarith only [htr, hξ, hn0]
  have hdform : d = 1 + (ξ : ℂ) * e := by dsimp [d, e]; ring
  have hdnorm : 1 - 3 * ξ ^ 2 / 10 ≤ ‖d‖ := by
    have heq : 1 - d = -(ξ : ℂ) * e := by rw [hdform]; ring
    have hrev := norm_sub_norm_le (1 : ℂ) d
    rw [norm_one, heq, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ] at hrev
    nlinarith only [hrev, henorm, hξ]
  have hdpos : 0 < ‖d‖ := by nlinarith only [hdnorm, hξ, hξ32]
  have hd0 : d ≠ 0 := norm_pos_iff.mp hdpos
  have hnum : ‖(X : Matrix (Fin n) (Fin n) ℂ) + T - e • (1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 4 * ‖d‖ := by
    have hnorm : ‖(X : Matrix (Fin n) (Fin n) ℂ) + T - e • (1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤
        ‖(X : Matrix (Fin n) (Fin n) ℂ) + T‖ + ‖e • (1 : Matrix (Fin n) (Fin n) ℂ)‖ := norm_sub_le _ _
    have hsum : ‖(X : Matrix (Fin n) (Fin n) ℂ) + T‖ ≤
        ‖(X : Matrix (Fin n) (Fin n) ℂ)‖ + ‖T‖ := norm_add_le _ _
    rw [norm_smul, norm_one, mul_one] at hnorm
    nlinarith only [hnorm, hsum, hXnorm, hTnorm, henorm, hdnorm, hξ, hξ32]
  have hformula : (ξ⁻¹ : ℂ) •
      (d⁻¹ • (CFC.sqrt S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * CFC.sqrt S) - 1) =
      d⁻¹ • ((X : Matrix (Fin n) (Fin n) ℂ) + T - e • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    have hprod : CFC.sqrt S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * CFC.sqrt S = S + (ξ : ℂ) • T := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
        hsqrt, T]
    rw [hprod]
    ext i j
    simp only [S, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    rw [hdform]
    push_cast
    have hden : 1 + (ξ : ℂ) * e ≠ 0 := by simpa only [hdform] using hd0
    have hξc : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
    field_simp [hden, hξc]
    <;> ring
  unfold PhiMap
  dsimp only
  split_ifs with h
  · change ‖(ξ⁻¹ : ℂ) •
        (d⁻¹ • (CFC.sqrt S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * CFC.sqrt S) - 1)‖ ≤ 4
    rw [hformula, norm_smul, norm_inv, mul_comm, ← div_eq_mul_inv]
    exact (div_le_iff₀ hdpos).mpr hnum
  · simp [Gsupp, WHMultiplicativity.schattenNorm]

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5PhiMeasurable -/
section
open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace BosonicLearn.Prop5

/-- The totalized relative-perturbation map is Borel measurable. The
matrix square root is constant because the base point is fixed. -/
theorem measurable_PhiMap {n : ℕ} (X₀ : Herm0 n) (ξ : ℝ) :
    Measurable (PhiMap X₀ ξ) := by
  classical
  letI : MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := borel _
  letI : BorelSpace (Matrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩
  let S : Matrix (Fin n) (Fin n) ℂ := 1 + (ξ : ℂ) • (X₀ : Matrix (Fin n) (Fin n) ℂ)
  let M : Herm0 n → Matrix (Fin n) (Fin n) ℂ := fun Z =>
    (ξ⁻¹ : ℂ) • (((1 + (ξ : ℂ) ^ 2 *
      ((X₀ : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n)⁻¹) •
      (CFC.sqrt S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * CFC.sqrt S) - 1)
  have hM : Measurable M := by
    dsimp [M]
    fun_prop
  have hs : MeasurableSet {Z : Herm0 n | M Z ∈ Herm0 n} :=
    (Herm0_isClosed n).measurableSet.preimage hM
  have hf : Measurable (fun Z : {Z : Herm0 n | M Z ∈ Herm0 n} =>
      (⟨M Z, Z.property⟩ : Herm0 n)) := by
    change @Measurable _ _ _ (borel _) _
    rw [borel_comap]
    exact (hM.comp measurable_subtype_coe).subtype_mk
  unfold PhiMap
  change Measurable (fun Z => if h : M Z ∈ Herm0 n then (⟨M Z, h⟩ : Herm0 n) else 0)
  exact hf.dite (measurable_const : Measurable
    (fun _ : ({Z : Herm0 n | M Z ∈ Herm0 n}ᶜ : Set (Herm0 n)) => (0 : Herm0 n))) hs

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5FamilyEntries -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix BigOperators

namespace BosonicLearn.Prop5
noncomputable section

theorem continuous_fugacityCoeff_entry_family_entries {n : ℕ} (u v : Occupation (Fin n)) :
    Continuous (fun R : Matrix (Fin n) (Fin n) ℂ => fugacityCoeff R u v) := by
  classical
  unfold fugacityCoeff gammaFock
  fun_prop

theorem continuous_family_entry_family_entries {n : ℕ} (ν ξ : ℝ) (u v : Occupation (Fin n)) :
    Continuous (fun X : Herm0 n => fugacityCoeff (fugacityFamily ν ξ X) u v) := by
  apply (continuous_fugacityCoeff_entry_family_entries u v).comp
  unfold fugacityFamily
  fun_prop

theorem isCompact_Gsupp (n : ℕ) : IsCompact (Gsupp n) := by
  let : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → ℂ))
  let : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedSpace ℝ (Fin n → Fin n → ℂ))
  have hc : Continuous fun X : Herm0 n =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ := by
    apply Continuous.norm
    exact (LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)).comp
        continuous_subtype_val
  apply Metric.isCompact_of_isClosed_isBounded
  · simpa [Gsupp, WHMultiplicativity.schattenNorm] using isClosed_le hc continuous_const
  · apply isBounded_iff_forall_norm_le.mpr
    refine ⟨4, ?_⟩
    intro X hX
    change ‖fun i j => (X : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ 4
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro j
    exact (matrix_entry_le_operator_norm (X : Matrix (Fin n) (Fin n) ℂ) i j).trans hX

theorem finite_cond_measure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Set Ω) : IsFiniteMeasure (cond μ s) := by
  constructor
  calc
    (cond μ s) Set.univ = (μ s)⁻¹ * μ s := by
      simp [ProbabilityTheory.cond, Measure.smul_apply]
    _ ≤ 1 := ENNReal.inv_mul_le_one _
    _ < ⊤ := by norm_num

theorem measurableSet_operator_ball (n : ℕ) (b : ℝ) :
    MeasurableSet (herm0Ball ⊤ (0 : Herm0 n) b) := by
  have hc : Continuous fun X : Herm0 n =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ := by
    apply Continuous.norm
    exact (LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)).comp
        continuous_subtype_val
  simpa [herm0Ball, WHMultiplicativity.schattenNorm] using
    measurableSet_le hc.measurable measurable_const

/-- Every finite tensor entry of the perturbed fugacity family is integrable under
the uniform perturbation measure. Polynomial continuity and compact prior support
give a bound, so no differentiability or explicit entry estimate is required. -/
theorem integrable_family_Phi_product_entry {ι : Type*} [Fintype ι]
    (n : ℕ) (hn : 1 ≤ n) (ν ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (X₀ : Herm0 n) (hX₀ : X₀ ∈ Ggood n) (b : ℝ) (hb10 : b ≤ 1 / 10)
    (u v : ι → Occupation (Fin n)) :
    Integrable (fun Z => ∏ t, fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z)) (u t) (v t))
      (cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) := by
  have := finite_cond_measure (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)
  let f := fun X : Herm0 n => ∏ t, fugacityCoeff (fugacityFamily ν ξ X) (u t) (v t)
  have hf : Continuous f := continuous_finsetProd _ fun t _ => continuous_family_entry_family_entries ν ξ (u t) (v t)
  obtain ⟨C, hC⟩ := (isCompact_Gsupp n).exists_bound_of_continuousOn hf.continuousOn
  apply Integrable.of_bound ((hf.measurable.comp (measurable_PhiMap X₀ ξ)).aestronglyMeasurable) C
  apply ae_cond_of_forall_mem (measurableSet_operator_ball n b)
  intro Z hZ
  apply hC
  apply PhiMap_mem_Gsupp hn X₀ hX₀ ξ hξ hξ32 Z
  exact le_trans hZ hb10

end
end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop1Comparison -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section
namespace BosonicLearn.Prop5

/-- Positive operator balls have positive, finite Haar volume. -/
theorem operator_ball_volume_pos_finite (n : ℕ) (hn : 1024 ≤ n)
    (b : ℝ) (hb : 0 < b) (hb4 : b ≤ 4) :
    0 < (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b) ∧
      (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b) < ⊤ := by
  constructor
  · by_contra h
    have hz : (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b) = 0 :=
      le_antisymm (not_lt.mp h) zero_le
    have hpart := gue_partition_le_operator_ball_volume n hn b hb
    rw [hz, mul_zero] at hpart
    exact (ne_of_gt (gueWeight_pos n)) (le_antisymm hpart zero_le)
  · apply lt_of_le_of_lt (measure_mono ?_) (isCompact_Gsupp n).measure_lt_top
    intro X hX
    have hx : WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ) ≤ b := by
      simpa [herm0Ball] using hX
    exact hx.trans hb4

/-- The cutoff Gaussian partition is positive and finite in the range needed here. -/
theorem gue_support_mass_pos_finite (n : ℕ) (hn : 1024 ≤ n) :
    0 < gueWeight n (Gsupp n) ∧ gueWeight n (Gsupp n) < ⊤ := by
  constructor
  · by_contra h
    have hzero : gueWeight n (Gsupp n) = 0 := le_antisymm (not_lt.mp h) zero_le
    have hgzero : gueWeight n (Ggood n) = 0 := by
      apply le_antisymm ?_ zero_le
      calc
        _ ≤ gueWeight n (Gsupp n) := measure_mono fun X hX => hX.trans (by norm_num : (3 : ℝ) ≤ 4)
        _ = 0 := hzero
    have hhalf := gue_good_mass_half n hn
    change (1 / 2 : ℝ≥0∞) ≤ cond (gueWeight n) Set.univ (Ggood n) at hhalf
    rw [cond_apply MeasurableSet.univ, Set.univ_inter, hgzero, mul_zero] at hhalf
    norm_num at hhalf
  · exact lt_of_le_of_lt (measure_mono (Set.subset_univ _))
      (lt_top_iff_ne_top.mpr (gueWeight_finite n (by omega)))

/-- The prior density is uniformly bounded below throughout the cutoff support. -/
theorem gue_restrict_density_lower (n : ℕ) :
    ENNReal.ofReal (Real.exp (-4 * (n : ℝ)^2)) •
      (Measure.addHaar : Measure (Herm0 n)).restrict (Gsupp n) ≤
        (gueWeight n).restrict (Gsupp n) := by
  have hG : MeasurableSet (Gsupp n) := (isCompact_Gsupp n).isClosed.measurableSet
  unfold gueWeight tracelessGUEWeight
  rw [restrict_withDensity hG, ← withDensity_const]
  apply withDensity_mono
  filter_upwards [ae_restrict_mem hG] with X hX
  exact ENNReal.ofReal_le_ofReal (gue_density_lower_on_support n X hX)

/-- Restricting the lower density to any subset of the support needs no regularity
of that subset. -/
theorem gue_restrict_density_lower_subset (n : ℕ) (S : Set (Herm0 n)) (hS : S ⊆ Gsupp n) :
    ENNReal.ofReal (Real.exp (-4 * (n : ℝ)^2)) •
      (Measure.addHaar : Measure (Herm0 n)).restrict S ≤ (gueWeight n).restrict S := by
  have h := Measure.restrict_mono (s := S) (s' := S) Set.Subset.rfl (gue_restrict_density_lower n)
  simpa only [Measure.restrict_smul, Measure.restrict_restrict_of_subset hS] using h

/-- Gaussian volume comparison turns any fixed lower Haar distortion into the
likelihood-independent comparison required by Proposition 1. -/
theorem prior_comparison_of_haar_domination (n : ℕ) (hn : 1024 ≤ n)
    (X₀ : Herm0 n) (hX₀ : X₀ ∈ Ggood n)
    (κ b a : ℝ) (hκ : 0 < κ) (hb : 0 < b) (hb4 : b ≤ 4) (ha : 0 < a)
    (hsmall : a ≤ (κ * b / 3 * Real.exp (-40))^2)
    (f : Herm0 n → Herm0 n)
    (himage : f '' herm0Ball ⊤ 0 b ⊆ Gsupp n)
    (hdist : ENNReal.ofReal (κ ^ Module.finrank ℝ (Herm0 n)) •
        ((Measure.addHaar : Measure (Herm0 n)).restrict (herm0Ball ⊤ 0 b)).map f ≤
      (Measure.addHaar : Measure (Herm0 n)).restrict (f '' herm0Ball ⊤ 0 b)) :
    ∃ d : ℝ≥0∞, 0 < d ∧ d < ⊤ ∧
      priorMu n (herm0Ball 1 X₀ (n * a)) ≤
        ENNReal.ofReal (Real.exp (-2 * (n : ℝ)^2)) * d ∧
      d • (cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)).map f ≤
        (priorMu n).restrict (f '' herm0Ball ⊤ 0 b) := by
  let z := gueWeight n (Gsupp n)
  let c := ENNReal.ofReal (Real.exp (-4 * (n : ℝ)^2))
  let k := ENNReal.ofReal (κ ^ Module.finrank ℝ (Herm0 n))
  let v := (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)
  let d := z⁻¹ * c * k * v
  have hz : 0 < z ∧ z < ⊤ := gue_support_mass_pos_finite n hn
  have hv : 0 < v ∧ v < ⊤ := operator_ball_volume_pos_finite n hn b hb hb4
  have hc : 0 < c := ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hk : 0 < k := ENNReal.ofReal_pos.mpr (pow_pos hκ _)
  have hzi : 0 < z⁻¹ := ENNReal.inv_pos.mpr hz.2.ne
  have hzifin : z⁻¹ < ⊤ := lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hz.1.ne')
  have hdpos : 0 < d :=
    ENNReal.mul_pos (ENNReal.mul_pos (ENNReal.mul_pos hzi.ne' hc.ne').ne' hk.ne').ne' hv.1.ne'
  have hdfin : d < ⊤ := by
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top hzifin ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top) hv.2
  have hG : MeasurableSet (Gsupp n) := (isCompact_Gsupp n).isClosed.measurableSet
  have hprior : priorMu n = z⁻¹ • (gueWeight n).restrict (Gsupp n) := by
    rw [priorMu_eq_cond_gueWeight]
    rfl
  refine ⟨d, hdpos, hdfin, ?_, ?_⟩
  · rw [hprior, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' hG]
    have hvol := trace_weight_le_scaled_operator_volume n hn X₀ hX₀ κ b a hκ hb ha hsmall
    have hexp : ENNReal.ofReal (Real.exp (-8 * (n : ℝ)^2)) ≤
        ENNReal.ofReal (Real.exp (-2 * (n : ℝ)^2)) * c := by
      dsimp only [c]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (n : ℝ)]
    calc
      _ ≤ z⁻¹ * (ENNReal.ofReal (Real.exp (-8 * (n : ℝ)^2)) * k * v) :=
        mul_le_mul_right hvol _
      _ ≤ z⁻¹ * ((ENNReal.ofReal (Real.exp (-2 * (n : ℝ)^2)) * c) * k * v) := by gcongr
      _ = _ := by dsimp only [d]; ring
  · have hlower := gue_restrict_density_lower_subset n (f '' herm0Ball ⊤ 0 b) himage
    have hcancel : d * v⁻¹ = z⁻¹ * c * k := by
      dsimp only [d]
      rw [mul_assoc, ENNReal.mul_inv_cancel hv.1.ne' hv.2.ne, mul_one]
    calc
      _ = (z⁻¹ * c) • (k • ((Measure.addHaar : Measure (Herm0 n)).restrict
          (herm0Ball ⊤ 0 b)).map f) := by
        unfold ProbabilityTheory.cond
        rw [Measure.map_smul, smul_smul]
        change (d * v⁻¹) • _ = _
        rw [hcancel, smul_smul]
      _ ≤ (z⁻¹ * c) • (Measure.addHaar : Measure (Herm0 n)).restrict
          (f '' herm0Ball ⊤ 0 b) := smul_le_smul_left _ hdist
      _ = z⁻¹ • (c • (Measure.addHaar : Measure (Herm0 n)).restrict
          (f '' herm0Ball ⊤ 0 b)) := by rw [smul_smul]
      _ ≤ z⁻¹ • (gueWeight n).restrict (f '' herm0Ball ⊤ 0 b) := smul_le_smul_left _ hlower
      _ = _ := by rw [hprior, Measure.restrict_smul, Measure.restrict_restrict_of_subset himage]

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop1FromDomination -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- The exact Proposition 1 statement follows from the geometric prior comparison,
uniformly over every normalized measurable likelihood model. -/
theorem proposition_1_of_uniform_haar_domination
    (hgeometry : ∀ b : ℝ, 0 < b → b ≤ 1 / 10 →
      ∃ κ : ℝ, 0 < κ ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ < 1 / 32 ∧
        ∀ n : ℕ, 1024 ≤ n → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ → ∀ X₀ ∈ Ggood n,
          ENNReal.ofReal (κ ^ Module.finrank ℝ (Herm0 n)) •
            ((Measure.addHaar : Measure (Herm0 n)).restrict (herm0Ball ⊤ 0 b)).map (PhiMap X₀ ξ) ≤
              (Measure.addHaar : Measure (Herm0 n)).restrict (PhiMap X₀ ξ '' herm0Ball ⊤ 0 b)) :
    ∀ b : ℝ, 0 < b → b ≤ 1 / 10 →
      ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ < 1 / 32 ∧ ∃ n₁ : ℕ,
        ∀ a : ℝ, 0 < a → a ≤ a₀ → ∀ n : ℕ, n₁ ≤ n → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ → ∀ X₀ ∈ Ggood n,
        ∀ (Ω : Type) [MeasurableSpace Ω] (ref : Measure Ω) [SigmaFinite ref]
          (p : Herm0 n → Ω → ℝ≥0∞), Measurable (Function.uncurry p) →
          (∀ X, IsProbabilityMeasure (ref.withDensity (p X))) →
          ENNReal.ofReal (1 - Real.exp (-(n : ℝ) ^ 2)) ≤ (ref.withDensity (p X₀))
            {x | (∫⁻ X in herm0Ball 1 X₀ (n * a), p X x ∂(priorMu n)) *
                  (∫⁻ Z, p (PhiMap X₀ ξ Z) x ∂(cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)))
                ≤ ENNReal.ofReal (Real.exp (-(c * (n : ℝ) ^ 2))) * p X₀ x *
                  ∫⁻ X in PhiMap X₀ ξ '' herm0Ball ⊤ 0 b, p X x ∂(priorMu n)} := by
  intro b hb hb10
  obtain ⟨κ, hκ, ξ₀, hξ₀, hξ32, hgeom⟩ := hgeometry b hb hb10
  refine ⟨(κ * b / 3 * Real.exp (-40))^2, by positivity, 1, by norm_num,
    ξ₀, hξ₀, hξ32, 1024, ?_⟩
  intro a ha haa n hn ξ hξ hξξ X₀ hX₀ Ω _ ref _ p hp hnorm
  have himage : PhiMap X₀ ξ '' herm0Ball ⊤ 0 b ⊆ Gsupp n := by
    rintro X ⟨Z, hZ, rfl⟩
    exact PhiMap_mem_Gsupp (by omega) X₀ hX₀ ξ hξ (hξξ.trans_lt hξ32) Z (hZ.trans hb10)
  obtain ⟨d, hd0, hdt, hmass, hdom⟩ := prior_comparison_of_haar_domination
    n hn X₀ hX₀ κ b a hκ hb (by linarith) ha haa (PhiMap X₀ ξ) himage
      (hgeom n hn ξ hξ hξξ X₀ hX₀)
  have : IsFiniteMeasure (priorMu n) := by
    rw [priorMu_eq_cond_gueWeight]
    exact finite_cond_measure _ _
  rw [ENNReal.ofReal_sub 1 (Real.exp_pos _).le, ENNReal.ofReal_one]
  apply likelihood_ratio_event_of_measure_domination (priorMu n)
    (cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) ref p hp hnorm
    X₀ (herm0Ball 1 X₀ (n * a)) (PhiMap X₀ ξ '' herm0Ball ⊤ 0 b)
    (PhiMap X₀ ξ) (measurable_PhiMap X₀ ξ)
    (ENNReal.ofReal (Real.exp (-(1 * (n : ℝ)^2)))) d
    (ENNReal.ofReal (Real.exp (-(n : ℝ)^2)))
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) ENNReal.ofReal_ne_top
    hd0.ne' hdt.ne _ hdom
  convert hmass using 1
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 3
  ring

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop1Phi -/
section
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 800000

theorem selfAdjoint_norm_le_of_order_bounds {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (a : A) (ha : IsSelfAdjoint a) (c : ℝ)
    (hc : 0 ≤ c) (hl : algebraMap ℝ A (-c) ≤ a) (hu : a ≤ algebraMap ℝ A c) :
    ‖a‖ ≤ c := by
  nontriviality A using by simpa [Subsingleton.elim a 0] using hc
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum ha with h | h
  · exact (le_algebraMap_iff_spectrum_le ha).mp hu _ h
  · have := (algebraMap_le_iff_le_spectrum ha).mp hl _ h
    linarith

/-- A small spectral interval for the square root of the hard family. -/
theorem family_sqrt_bounds {n : ℕ} (X : Herm0 n) (hX : X ∈ Ggood n)
    (ξ : ℝ) (hξ : 0 < ξ) (hξ64 : ξ ≤ 1 / 64) :
    let S : Matrix (Fin n) (Fin n) ℂ := 1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)
    S.PosSemidef ∧ ‖CFC.sqrt S - 1‖ ≤ 1 / 10 := by
  classical
  let S : Matrix (Fin n) (Fin n) ℂ := 1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)
  have hx := opnorm_form (X : Matrix (Fin n) (Fin n) ℂ) X.property.1 3 hX
  have hlo : ((9 / 10 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ 2 ≤ S := by
    apply sub_nonneg.mp
    have he : S - ((9 / 10 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ 2 =
        ((19 / 100 - 3 * ξ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
          (ξ : ℂ) • ((3 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X) := by
      simp only [S, smul_pow, one_pow]
      ext i j
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
      simp only [Complex.real_smul]
      push_cast
      ring
    rw [he]
    exact ((Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by linarith))).add
      (hx.2.smul (Complex.zero_le_real.mpr hξ.le))).nonneg
  have hhi : S ≤ ((11 / 10 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ 2 := by
    apply sub_nonneg.mp
    have he : ((11 / 10 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ 2 - S =
        ((21 / 100 - 3 * ξ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
          (ξ : ℂ) • ((3 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - X) := by
      simp only [S, smul_pow, one_pow]
      ext i j
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
      simp only [Complex.real_smul]
      push_cast
      ring
    rw [he]
    exact ((Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by linarith))).add
      (hx.1.smul (Complex.zero_le_real.mpr hξ.le))).nonneg
  have hpos (c : ℝ) (hc : 0 ≤ c) : 0 ≤ c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have he : c • (1 : Matrix (Fin n) (Fin n) ℂ) = (c : ℂ) • 1 := by
      ext i j
      simp [Complex.real_smul]
    rw [he]
    exact (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hc)).nonneg
  have hRlo := CFC.sqrt_le_sqrt _ _ hlo
  have hRhi := CFC.sqrt_le_sqrt _ _ hhi
  rw [CFC.sqrt_sq _ (hpos _ (by norm_num))] at hRlo
  rw [CFC.sqrt_sq _ (hpos _ (by norm_num))] at hRhi
  have hbase : 0 ≤ ((9 / 10 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ 2 := by
    simpa only [smul_pow, one_pow] using hpos ((9 / 10 : ℝ)^2) (sq_nonneg _)
  refine ⟨Matrix.nonneg_iff_posSemidef.mp (hbase.trans hlo), ?_⟩
  apply selfAdjoint_norm_le_of_order_bounds _ ((IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg S)).sub (IsSelfAdjoint.one _))
    (1 / 10) (by norm_num)
  · rw [Algebra.algebraMap_eq_smul_one]
    calc (-(1 / 10 : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℂ) = (9 / 10 : ℝ) • 1 - 1 := by module
         _ ≤ CFC.sqrt S - 1 := sub_le_sub_right hRlo _
  · rw [Algebra.algebraMap_eq_smul_one]
    calc CFC.sqrt S - 1 ≤ (11 / 10 : ℝ) • 1 - 1 := sub_le_sub_right hRhi _
         _ = (1 / 10 : ℝ) • 1 := by module

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop1PhiFormula -/
section
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 800000

/-- The trace pairing of two Hermitian matrices is real. -/
theorem hermitian_trace_mul_selfAdjoint {n : ℕ} (X Z : Herm0 n) :
    IsSelfAdjoint (((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace) := by
  change star (((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace) = _
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, X.property.1, Z.property.1,
    Matrix.trace_mul_comm]

/-- The rational formula defining the relative parametrization is actually in
`Herm0`; thus its totalized fallback branch does not occur on the physical domain. -/
theorem PhiMap_formula_of_posSemidef {n : ℕ} (hn : 1 ≤ n)
    (X : Herm0 n) (ξ : ℝ) (hξ : ξ ≠ 0) (Z : Herm0 n)
    (hS : (1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)).PosSemidef)
    (hd : 1 + (ξ : ℂ)^2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n ≠ 0) :
    let S : Matrix (Fin n) (Fin n) ℂ := 1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)
    let d : ℂ := 1 + (ξ : ℂ)^2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
    let e : ℂ := (ξ : ℂ) * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
    (PhiMap X ξ Z : Matrix (Fin n) (Fin n) ℂ) =
      d⁻¹ • ((X : Matrix (Fin n) (Fin n) ℂ) +
        CFC.sqrt S * (Z : Matrix (Fin n) (Fin n) ℂ) * CFC.sqrt S -
        e • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  classical
  let S : Matrix (Fin n) (Fin n) ℂ := 1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)
  let d : ℂ := 1 + (ξ : ℂ)^2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
  let e : ℂ := (ξ : ℂ) * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
  let T : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt S * (Z : Matrix (Fin n) (Fin n) ℂ) * CFC.sqrt S
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hξc : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ
  have hsqrt : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hsqrtHerm : (CFC.sqrt S).IsHermitian := (CFC.sqrt_nonneg S).isSelfAdjoint
  have hTHerm : T.IsHermitian := by
    dsimp [T]
    simpa only [hsqrtHerm.eq] using
      Matrix.isHermitian_mul_mul_conjTranspose (CFC.sqrt S) Z.property.1
  have htrace := hermitian_trace_mul_selfAdjoint X Z
  have heHerm : IsSelfAdjoint e := by
    change star e = e
    simp [e, star_mul, star_div₀, htrace.star_eq, mul_comm]
  have hdHerm : IsSelfAdjoint d⁻¹ := by
    change star d⁻¹ = d⁻¹
    simp [d, star_add, star_mul, star_pow, star_div₀, htrace.star_eq, mul_comm]
  have hdform : d = 1 + (ξ : ℂ) * e := by dsimp [d, e]; ring
  have hTtrace : T.trace = (ξ : ℂ) * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace := by
    dsimp [T]
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hsqrt]
    simp [S, Matrix.add_mul, Matrix.trace_add, Matrix.trace_smul,
      Z.property.2]
  have hnumHerm : ((X : Matrix (Fin n) (Fin n) ℂ) + T -
      e • (1 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian :=
    (X.property.1.add hTHerm).sub (Matrix.isHermitian_one.smul heHerm)
  have hnumTrace : ((X : Matrix (Fin n) (Fin n) ℂ) + T -
      e • (1 : Matrix (Fin n) (Fin n) ℂ)).trace = 0 := by
    simp only [Matrix.trace_sub, Matrix.trace_add, X.property.2, zero_add, hTtrace,
      Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    dsimp [e]
    field_simp
    ring
  have hformula : (ξ⁻¹ : ℂ) •
      (d⁻¹ • (CFC.sqrt S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * CFC.sqrt S) - 1) =
      d⁻¹ • ((X : Matrix (Fin n) (Fin n) ℂ) + T - e • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    have hprod : CFC.sqrt S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * CFC.sqrt S = S + (ξ : ℂ) • T := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul,
        Matrix.smul_mul, hsqrt, T]
    rw [hprod]
    ext i j
    simp only [S, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    rw [hdform]
    have hden : 1 + (ξ : ℂ) * e ≠ 0 := by simpa only [← hdform] using hd
    field_simp [hden, hξc]
    ring
  have hmem : (ξ⁻¹ : ℂ) •
      (d⁻¹ • (CFC.sqrt S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * CFC.sqrt S) - 1)
      ∈ Herm0 n := by
    rw [hformula]
    exact ⟨hnumHerm.smul hdHerm, by rw [Matrix.trace_smul, hnumTrace, smul_zero]⟩
  change (PhiMap X ξ Z : Matrix (Fin n) (Fin n) ℂ) = _
  unfold PhiMap
  dsimp only
  rw [dif_pos hmem]
  exact hformula

/-- Bounds on the real scalar denominator of the relative parametrization. -/
theorem PhiMap_denominator_bounds {n : ℕ} (hn : 1 ≤ n)
    (X : Herm0 n) (hX : X ∈ Ggood n) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (Z : Herm0 n) (hZ : ‖(Z : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 / 10) :
    let d : ℂ := 1 + (ξ : ℂ)^2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
    IsSelfAdjoint d ∧ 1 - 3 * ξ^2 / 10 ≤ ‖d‖ ∧ ‖d‖ ≤ 1 + 3 * ξ^2 / 10 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hXnorm : ‖(X : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 3 := hX
  have htr : ‖((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace‖ ≤ n * (3 / 10) := by
    refine (matrix_trace_le_operator_norm _).trans ?_
    have hm := norm_mul_le (X : Matrix (Fin n) (Fin n) ℂ) (Z : Matrix (Fin n) (Fin n) ℂ)
    have hab : ‖(X : Matrix (Fin n) (Fin n) ℂ)‖ * ‖(Z : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 3 * (1 / 10) := by gcongr
    nlinarith only [hm, hab, hn0]
  let d : ℂ := 1 + (ξ : ℂ)^2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
  have htrace := hermitian_trace_mul_selfAdjoint X Z
  have hdReal : IsSelfAdjoint d := by
    change star d = d
    simp [d, star_add, star_mul, star_pow, star_div₀, htrace.star_eq, mul_comm]
  have hpert : ‖d - 1‖ ≤ 3 * ξ^2 / 10 := by
    dsimp [d]
    rw [add_sub_cancel_left, norm_div, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hξ, Complex.norm_natCast]
    apply (div_le_iff₀ hn0).mpr
    nlinarith only [htr, sq_nonneg ξ, hn0]
  refine ⟨hdReal, ?_, ?_⟩
  · have hrev := norm_sub_norm_le (1 : ℂ) d
    rw [norm_one, norm_sub_rev] at hrev
    linarith
  · have hnorm := norm_add_le (d - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at hnorm
    linarith

/-- The physical parameters ensure the exact rational formula for `PhiMap`. -/
theorem PhiMap_formula {n : ℕ} (hn : 1 ≤ n)
    (X : Herm0 n) (hX : X ∈ Ggood n) (ξ : ℝ) (hξ : 0 < ξ) (hξ64 : ξ ≤ 1 / 64)
    (Z : Herm0 n) (hZ : ‖(Z : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 / 10) :
    let S : Matrix (Fin n) (Fin n) ℂ := 1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)
    let d : ℂ := 1 + (ξ : ℂ)^2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
    let e : ℂ := (ξ : ℂ) * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
    (PhiMap X ξ Z : Matrix (Fin n) (Fin n) ℂ) =
      d⁻¹ • ((X : Matrix (Fin n) (Fin n) ℂ) +
        CFC.sqrt S * (Z : Matrix (Fin n) (Fin n) ℂ) * CFC.sqrt S -
        e • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  have hSp : (1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
    have hx := (opnorm_form (X : Matrix (Fin n) (Fin n) ℂ) X.property.1 3 hX).2
    have he : 1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ) =
        ((1 - 3 * ξ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (ξ : ℂ) • ((3 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X) := by
      push_cast
      module
    rw [he]
    exact (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by linarith))).add
      (hx.smul (Complex.zero_le_real.mpr hξ.le))
  have hdlo := (PhiMap_denominator_bounds hn X hX ξ hξ.le Z hZ).2.1
  have hd0 : 1 + (ξ : ℂ)^2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n ≠ 0 := by
    apply norm_pos_iff.mp
    nlinarith only [hdlo, hξ, hξ64]
  exact PhiMap_formula_of_posSemidef hn X ξ hξ.ne' Z hSp hd0

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop1HaarDistortion -/
section
/-! Haar-volume distortion from a lower Lipschitz bound on a subset. -/

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- A lower Lipschitz bound on a subset bounds the Haar volume of its preimages.
No regularity of the subset or of its image is needed. -/
theorem haar_preimage_inter_le_of_antilipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} {s : Set E} {K : NNReal}
    (hf : AntilipschitzWith K (fun x : s => f x)) (t : Set E) :
    μ (f ⁻¹' t ∩ s) ≤ (K : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ) * μ (t ∩ f '' s) := by
  let d : ℝ := Module.finrank ℝ E
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hH := hf.hausdorffMeasure_preimage_le hd (t ∩ f '' s)
  have hset : Subtype.val '' ((fun x : s => f x) ⁻¹' (t ∩ f '' s)) =
      f ⁻¹' t ∩ s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy.1, y.2⟩
    · rintro ⟨hx, hs⟩
      exact ⟨⟨x, hs⟩, ⟨hx, ⟨x, hs, rfl⟩⟩, rfl⟩
  rw [← (isometry_subtype_coe (s := s)).hausdorffMeasure_image (Or.inl hd), hset] at hH
  have hhaar : μ = (μ.addHaarScalarFactor (hausdorffMeasure d) : ℝ≥0∞) •
      hausdorffMeasure d := Measure.isAddLeftInvariant_eq_smul μ (hausdorffMeasure d)
  rw [hhaar]
  simp only [Measure.smul_apply, smul_eq_mul]
  calc
    _ ≤ (μ.addHaarScalarFactor (hausdorffMeasure d) : ℝ≥0∞) *
        ((K : ℝ≥0∞) ^ d * hausdorffMeasure d (t ∩ f '' s)) := by
      exact mul_le_mul_right hH _
    _ = _ := by simp [d, mul_left_comm]

/-- The pushforward of Haar measure restricted to an inverse-Lipschitz set is
bounded by Haar measure on its image, with the dimension-dependent factor. -/
theorem haar_map_restrict_le_of_antilipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} {s : Set E} {K : NNReal}
    (hK : 0 < K) (hf : Measurable f)
    (hanti : AntilipschitzWith K (fun x : s => f x)) :
    (K : ℝ≥0∞) ^ (-(Module.finrank ℝ E : ℝ)) • (μ.restrict s).map f ≤
      μ.restrict (f '' s) := by
  apply Measure.le_iff.mpr
  intro t ht
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hf ht,
    Measure.restrict_apply (hf ht), Measure.restrict_apply ht, ENNReal.rpow_neg]
  apply (ENNReal.inv_mul_le_iff ?_ ?_).mpr
  · exact haar_preimage_inter_le_of_antilipschitz μ hanti t
  · simp [hK.ne']
  · simp

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop1PhiDistortion -/
section
open MeasureTheory
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ENNReal

noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 1000000

/-- Cancellation of the affine numerator gives a useful exact difference
identity for the relative parametrization. -/
theorem PhiMap_difference_identity {n : ℕ} (hn : 1 ≤ n)
    (X : Herm0 n) (hX : X ∈ Ggood n) (ξ : ℝ) (hξ : 0 < ξ) (hξ64 : ξ ≤ 1 / 64)
    (Z W : Herm0 n) (hZ : ‖(Z : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 / 10)
    (hW : ‖(W : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 / 10) :
    let S : Matrix (Fin n) (Fin n) ℂ := 1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)
    let d : ℂ := 1 + (ξ : ℂ)^2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
    let e : ℂ := (ξ : ℂ) * ((X : Matrix (Fin n) (Fin n) ℂ) * (Z - W)).trace / n
    d • ((PhiMap X ξ Z : Matrix (Fin n) (Fin n) ℂ) - PhiMap X ξ W) =
      CFC.sqrt S * ((Z : Matrix (Fin n) (Fin n) ℂ) - W) * CFC.sqrt S -
        e • (1 + (ξ : ℂ) • (PhiMap X ξ W : Matrix (Fin n) (Fin n) ℂ)) := by
  let R := CFC.sqrt (1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ))
  let d (Y : Herm0 n) : ℂ := 1 + (ξ : ℂ)^2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Y).trace / n
  let e (Y : Herm0 n) : ℂ := (ξ : ℂ) * ((X : Matrix (Fin n) (Fin n) ℂ) * Y).trace / n
  have hd0 (Y : Herm0 n) (hY : ‖(Y : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 / 10) : d Y ≠ 0 := by
    apply norm_pos_iff.mp
    have hlo := (PhiMap_denominator_bounds hn X hX ξ hξ.le Y hY).2.1
    change 0 < ‖d Y‖
    change 1 - 3 * ξ ^ 2 / 10 ≤ ‖d Y‖ at hlo
    nlinarith only [hlo, hξ, hξ64]
  have hmul (Y : Herm0 n) (hY : ‖(Y : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 / 10) :
      d Y • (PhiMap X ξ Y : Matrix (Fin n) (Fin n) ℂ) =
        X + R * (Y : Matrix (Fin n) (Fin n) ℂ) * R - e Y • 1 := by
    rw [PhiMap_formula hn X hX ξ hξ hξ64 Y hY]
    change d Y • ((d Y)⁻¹ • _) = _
    rw [smul_smul, mul_inv_cancel₀ (hd0 Y hY), one_smul]
  have he : e Z - e W = e (Z - W) := by
    simp only [e, Submodule.coe_sub, Matrix.mul_sub, Matrix.trace_sub]
    ring
  have hd : d Z - d W = (ξ : ℂ) * e (Z - W) := by
    simp only [d, e, Submodule.coe_sub, Matrix.mul_sub, Matrix.trace_sub]
    ring
  change d Z • ((PhiMap X ξ Z : Matrix (Fin n) (Fin n) ℂ) - PhiMap X ξ W) = _
  calc
    _ = d Z • (PhiMap X ξ Z : Matrix (Fin n) (Fin n) ℂ) -
          d W • (PhiMap X ξ W : Matrix (Fin n) (Fin n) ℂ) -
          (d Z - d W) • (PhiMap X ξ W : Matrix (Fin n) (Fin n) ℂ) := by module
    _ = R * ((Z : Matrix (Fin n) (Fin n) ℂ) - W) * R -
          e (Z - W) • (1 + (ξ : ℂ) • (PhiMap X ξ W : Matrix (Fin n) (Fin n) ℂ)) := by
      rw [hmul Z hZ, hmul W hW, hd, ← he]
      simp only [Matrix.mul_sub, Matrix.sub_mul]
      module

/-- The physical relative parametrization does not collapse distances on its
local operator-norm ball. The coarse constant four is sufficient for volume bounds. -/
theorem PhiMap_lower_lipschitz {n : ℕ} (hn : 1 ≤ n)
    (X : Herm0 n) (hX : X ∈ Ggood n) (ξ : ℝ) (hξ : 0 < ξ) (hξ64 : ξ ≤ 1 / 64)
    (Z W : Herm0 n) (hZ : ‖(Z : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 / 10)
    (hW : ‖(W : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 / 10) :
    ‖(Z : Matrix (Fin n) (Fin n) ℂ) - W‖ ≤
      4 * ‖(PhiMap X ξ Z : Matrix (Fin n) (Fin n) ℂ) - PhiMap X ξ W‖ := by
  classical
  let : NeZero n := ⟨by omega⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  let R := CFC.sqrt (1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ))
  let Δ : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ) - W
  let P : Matrix (Fin n) (Fin n) ℂ := (PhiMap X ξ Z : Matrix (Fin n) (Fin n) ℂ) - PhiMap X ξ W
  let d : ℂ := 1 + (ξ : ℂ)^2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
  let e : ℂ := (ξ : ℂ) * ((X : Matrix (Fin n) (Fin n) ℂ) * Δ).trace / n
  have hRclose : ‖R - 1‖ ≤ 1 / 10 := (family_sqrt_bounds X hX ξ hξ hξ64).2
  have hRnorm : ‖R‖ ≤ 11 / 10 := by
    have h := norm_add_le (R - 1) (1 : Matrix (Fin n) (Fin n) ℂ)
    rw [sub_add_cancel, norm_one] at h
    linarith
  have hRsandwich : ‖R * Δ * R - Δ‖ ≤ (21 / 100) * ‖Δ‖ := by
    have heq : R * Δ * R - Δ = (R - 1) * Δ * R + Δ * (R - 1) := by noncomm_ring
    rw [heq]
    calc
      _ ≤ ‖(R - 1) * Δ * R‖ + ‖Δ * (R - 1)‖ := norm_add_le _ _
      _ ≤ ‖R - 1‖ * ‖Δ‖ * ‖R‖ + ‖Δ‖ * ‖R - 1‖ := by
        exact add_le_add
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
          (norm_mul_le _ _)
      _ ≤ (1 / 10) * ‖Δ‖ * (11 / 10) + ‖Δ‖ * (1 / 10) := by gcongr
      _ = (21 / 100) * ‖Δ‖ := by ring
  have hXnorm : ‖(X : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 3 := hX
  have htr : ‖((X : Matrix (Fin n) (Fin n) ℂ) * Δ).trace‖ ≤ n * (3 * ‖Δ‖) := by
    refine (matrix_trace_le_operator_norm _).trans ?_
    calc
      _ ≤ n * (‖(X : Matrix (Fin n) (Fin n) ℂ)‖ * ‖Δ‖) := by
        gcongr
        exact norm_mul_le _ _
      _ ≤ n * (3 * ‖Δ‖) := by gcongr
  have henorm : ‖e‖ ≤ 3 * ξ * ‖Δ‖ := by
    dsimp only [e]
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ,
      Complex.norm_natCast]
    apply (div_le_iff₀ hn0).mpr
    nlinarith only [htr, hξ, hn0]
  have hWball : W ∈ herm0Ball ⊤ 0 (1 / 10) := by
    change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (W : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 / 10 at hW
    simpa [herm0Ball, WHMultiplicativity.schattenNorm] using hW
  have hPWnorm : ‖(PhiMap X ξ W : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 4 :=
    PhiMap_mem_Gsupp hn X hX ξ hξ (by linarith) W hWball
  have hQnorm : ‖(1 : Matrix (Fin n) (Fin n) ℂ) +
      (ξ : ℂ) • (PhiMap X ξ W : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 2 := by
    have h := norm_add_le (1 : Matrix (Fin n) (Fin n) ℂ)
      ((ξ : ℂ) • (PhiMap X ξ W : Matrix (Fin n) (Fin n) ℂ))
    rw [norm_one, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ] at h
    nlinarith only [h, hPWnorm, hξ, hξ64]
  have hscalar : ‖e • ((1 : Matrix (Fin n) (Fin n) ℂ) +
      (ξ : ℂ) • (PhiMap X ξ W : Matrix (Fin n) (Fin n) ℂ))‖ ≤ (3 / 32) * ‖Δ‖ := by
    rw [norm_smul]
    calc
      _ ≤ (3 * ξ * ‖Δ‖) * 2 := by gcongr
      _ ≤ (3 / 32) * ‖Δ‖ := by nlinarith [norm_nonneg Δ]
  have hid : d • P = R * Δ * R - e • ((1 : Matrix (Fin n) (Fin n) ℂ) +
      (ξ : ℂ) • (PhiMap X ξ W : Matrix (Fin n) (Fin n) ℂ)) :=
    PhiMap_difference_identity hn X hX ξ hξ hξ64 Z W hZ hW
  have herror : ‖d • P - Δ‖ ≤ (1 / 2) * ‖Δ‖ := by
    rw [hid]
    have heq : R * Δ * R - e • ((1 : Matrix (Fin n) (Fin n) ℂ) +
        (ξ : ℂ) • (PhiMap X ξ W : Matrix (Fin n) (Fin n) ℂ)) - Δ =
        (R * Δ * R - Δ) - e • ((1 : Matrix (Fin n) (Fin n) ℂ) +
        (ξ : ℂ) • (PhiMap X ξ W : Matrix (Fin n) (Fin n) ℂ)) := by module
    rw [heq]
    have h := norm_sub_le (R * Δ * R - Δ)
      (e • ((1 : Matrix (Fin n) (Fin n) ℂ) +
        (ξ : ℂ) • (PhiMap X ξ W : Matrix (Fin n) (Fin n) ℂ)))
    nlinarith only [h, hRsandwich, hscalar, norm_nonneg Δ]
  have hdNorm : ‖d‖ ≤ 2 := by
    have h := (PhiMap_denominator_bounds hn X hX ξ hξ.le Z hZ).2.2
    change ‖d‖ ≤ 1 + 3 * ξ ^ 2 / 10 at h
    nlinarith only [h, hξ, hξ64]
  have hdP : ‖d • P‖ ≤ 2 * ‖P‖ := by
    rw [norm_smul]
    gcongr
  have hreverse := norm_sub_norm_le Δ (d • P)
  rw [norm_sub_rev Δ (d • P)] at hreverse
  change ‖Δ‖ ≤ 4 * ‖P‖
  linarith

/-- Inverse Lipschitz control on every smaller local operator-norm ball. -/
theorem PhiMap_antilipschitz {n : ℕ} (hn : 1 ≤ n)
    (X : Herm0 n) (hX : X ∈ Ggood n) (ξ : ℝ) (hξ : 0 < ξ) (hξ64 : ξ ≤ 1 / 64)
    (b : ℝ) (hb : b ≤ 1 / 10) :
    AntilipschitzWith 4 (fun Z : herm0Ball (n := n) ⊤ 0 b => PhiMap X ξ Z.1) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro Z W
  have hnorm (Y : herm0Ball (n := n) ⊤ 0 b) :
      ‖(Y.1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 / 10 := by
    apply le_trans ?_ hb
    change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (Y.1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ b
    simpa [herm0Ball, WHMultiplicativity.schattenNorm] using Y.property
  have h := PhiMap_lower_lipschitz hn X hX ξ hξ hξ64 Z.1 W.1 (hnorm Z) (hnorm W)
  simpa only [Subtype.dist_eq, dist_eq_norm, NNReal.coe_ofNat,
    ← Submodule.coe_sub, Submodule.norm_coe] using h

/-- A uniform volume lower bound for the relative parametrization. It uses only
an inverse Lipschitz estimate, avoiding differentiability or Jacobian machinery. -/
theorem PhiMap_haar_distortion {n : ℕ} (hn : 1 ≤ n)
    (μ : Measure (Herm0 n)) [μ.IsAddHaarMeasure]
    (X : Herm0 n) (hX : X ∈ Ggood n) (ξ : ℝ) (hξ : 0 < ξ) (hξ64 : ξ ≤ 1 / 64)
    (b : ℝ) (hb : b ≤ 1 / 10) :
    (4 : ℝ≥0∞) ^ (-(Module.finrank ℝ (Herm0 n) : ℝ)) •
      (μ.restrict (herm0Ball ⊤ 0 b)).map (PhiMap X ξ) ≤
        μ.restrict (PhiMap X ξ '' herm0Ball ⊤ 0 b) := by
  exact haar_map_restrict_le_of_antilipschitz μ (by norm_num : (0 : NNReal) < 4)
    (measurable_PhiMap X ξ) (PhiMap_antilipschitz hn X hX ξ hξ hξ64 b hb)

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop1Direct -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

/-- Direct proof of Proposition 1 by Gaussian scaling and inverse-Lipschitz volume distortion. -/
theorem proposition_1_proved :
    ∀ b : ℝ, 0 < b → b ≤ 1 / 10 →
      ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ < 1 / 32 ∧ ∃ n₁ : ℕ,
        ∀ a : ℝ, 0 < a → a ≤ a₀ → ∀ n : ℕ, n₁ ≤ n → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ → ∀ X₀ ∈ Ggood n,
        ∀ (Ω : Type) [MeasurableSpace Ω] (ref : Measure Ω) [SigmaFinite ref]
          (p : Herm0 n → Ω → ℝ≥0∞), Measurable (Function.uncurry p) →
          (∀ X, IsProbabilityMeasure (ref.withDensity (p X))) →
          ENNReal.ofReal (1 - Real.exp (-(n : ℝ) ^ 2)) ≤ (ref.withDensity (p X₀))
            {x | (∫⁻ X in herm0Ball 1 X₀ (n * a), p X x ∂(priorMu n)) *
                  (∫⁻ Z, p (PhiMap X₀ ξ Z) x ∂(cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)))
                ≤ ENNReal.ofReal (Real.exp (-(c * (n : ℝ) ^ 2))) * p X₀ x *
                  ∫⁻ X in PhiMap X₀ ξ '' herm0Ball ⊤ 0 b, p X x ∂(priorMu n)}  := by
  apply proposition_1_of_uniform_haar_domination
  intro b hb hb10
  refine ⟨1 / 4, by norm_num, 1 / 64, by norm_num, by norm_num, ?_⟩
  intro n hn ξ hξ hξ64 X₀ hX₀
  have h := PhiMap_haar_distortion (by omega : 1 ≤ n)
    (Measure.addHaar : Measure (Herm0 n)) X₀ hX₀ ξ hξ hξ64 b hb10
  have hc : ENNReal.ofReal ((1 / 4 : ℝ) ^ Module.finrank ℝ (Herm0 n)) =
      (4 : ℝ≥0∞) ^ (-(Module.finrank ℝ (Herm0 n) : ℝ)) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_natCast, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
    rw [ENNReal.inv_pow]
  rw [hc]
  exact h

end BosonicLearn.Prop5

end

open BosonicLearn MeasureTheory ProbabilityTheory
open scoped ENNReal
theorem solution :
    ∀ b : ℝ, 0 < b → b ≤ 1 / 10 →
      ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ < 1 / 32 ∧ ∃ n₁ : ℕ,
        ∀ a : ℝ, 0 < a → a ≤ a₀ → ∀ n : ℕ, n₁ ≤ n → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ → ∀ X₀ ∈ Ggood n,
        ∀ (Ω : Type) [MeasurableSpace Ω] (ref : Measure Ω) [SigmaFinite ref]
          (p : Herm0 n → Ω → ℝ≥0∞), Measurable (Function.uncurry p) →
          (∀ X, IsProbabilityMeasure (ref.withDensity (p X))) →
          ENNReal.ofReal (1 - Real.exp (-(n : ℝ) ^ 2)) ≤ (ref.withDensity (p X₀))
            {x | (∫⁻ X in herm0Ball 1 X₀ (n * a), p X x ∂(priorMu n)) *
                  (∫⁻ Z, p (PhiMap X₀ ξ Z) x ∂(cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)))
                ≤ ENNReal.ofReal (Real.exp (-(c * (n : ℝ) ^ 2))) * p X₀ x *
                  ∫⁻ X in PhiMap X₀ ξ '' herm0Ball ⊤ 0 b, p X x ∂(priorMu n)} := BosonicLearn.Prop5.proposition_1_proved
