-- Prove2me | solution 1 for DedekindZeta.mixedMulHaar_map_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:34:46.274912+00:00
-- url     : https://prove2.me/submissions/f7885edd-1ad9-413f-ba26-5fa966c62cf1

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_mixedEmbedding_norm_inv
import Theorems.Thm_DedekindZeta_volume_pi_complex_map_inv
import Theorems.Thm_DedekindZeta_map_inv_volume_real
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
variable {K : Type*} [Field K] [NumberField K]
noncomputable section
set_option maxHeartbeats 1000000
namespace DedekindZeta
theorem _root_.solution :
    Measure.map (fun x : mixedEmbedding.mixedSpace K => x⁻¹) (mixedMulHaar K)
      = mixedMulHaar K := by
  classical
  have hinv : Measurable (fun x : mixedEmbedding.mixedSpace K => x⁻¹) :=
    measurable_fst.inv.prodMk measurable_snd.inv
  -- The multiplicative-Haar density constant `c = (2/π)^{r₂}` and the additive
  -- density `D(x) = c·|N(x)|⁻¹` against which `mixedMulHaar = volume.withDensity D`.
  set c : ℝ := (2 / Real.pi) ^ nrComplexPlaces K with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  set D : mixedEmbedding.mixedSpace K → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (c * (mixedEmbedding.norm x)⁻¹) with hD
  have hDmeas : Measurable D :=
    (((mixedEmbedding.continuous_norm K).measurable.inv).const_mul c).ennreal_ofReal
  -- Per-factor inversion-Jacobian densities (from the two child lemmas).
  set Dr : ({w : InfinitePlace K // IsReal w} → ℝ) → ℝ≥0∞ :=
    fun a => ∏ w, ENNReal.ofReal (‖a w‖ ^ 2)⁻¹ with hDr
  set Dc : ({w : InfinitePlace K // IsComplex w} → ℂ) → ℝ≥0∞ :=
    fun b => ∏ w, ENNReal.ofReal (‖b w‖ ^ 4)⁻¹ with hDc
  have hDrmeas : Measurable Dr := by
    rw [hDr]; exact Finset.measurable_prod _ fun w _ => by fun_prop
  have hDcmeas : Measurable Dc := by
    rw [hDc]; exact Finset.measurable_prod _ fun w _ => by fun_prop
  have hJmeas : Measurable (fun z : mixedEmbedding.mixedSpace K => Dr z.1 * Dc z.2) :=
    (hDrmeas.comp measurable_fst).mul (hDcmeas.comp measurable_snd)
  -- `mixedMulHaar = volume.withDensity D` (definitional).
  have hμ : mixedMulHaar K = volume.withDensity D := rfl
  -- The componentwise factor inversions are measurable.
  have hfr : Measurable (fun a : {w : InfinitePlace K // IsReal w} → ℝ => fun w => (a w)⁻¹) := by
    fun_prop
  have hfc : Measurable
      (fun b : {w : InfinitePlace K // IsComplex w} → ℂ => fun w => (b w)⁻¹) := by fun_prop
  -- **Full inversion Jacobian on the additive volume** (Step 1): combine the two
  -- per-factor Jacobians through the product measure `volume = volume.prod volume`.
  have hJac : Measure.map (fun x : mixedEmbedding.mixedSpace K => x⁻¹) volume
      = volume.withDensity (fun z => Dr z.1 * Dc z.2) := by
    have hpm := Measure.map_prod_map
      (volume : Measure ({w : InfinitePlace K // IsReal w} → ℝ))
      (volume : Measure ({w : InfinitePlace K // IsComplex w} → ℂ)) hfr hfc
    rw [map_inv_volume_real, volume_pi_complex_map_inv,
      prod_withDensity hDrmeas hDcmeas] at hpm
    rw [show (fun x : mixedEmbedding.mixedSpace K => x⁻¹)
        = Prod.map (fun a : {w : InfinitePlace K // IsReal w} → ℝ => fun w => (a w)⁻¹)
            (fun b : {w : InfinitePlace K // IsComplex w} → ℂ => fun w => (b w)⁻¹) from rfl,
      Measure.volume_eq_prod]
    exact hpm.symm
  -- Change-of-variables principle along inversion for the additive volume.
  have hcov : ∀ φ : mixedEmbedding.mixedSpace K → ℝ≥0∞, Measurable φ →
      ∫⁻ a, φ a⁻¹ ∂(volume : Measure (mixedEmbedding.mixedSpace K))
        = ∫⁻ a, (Dr a.1 * Dc a.2) * φ a ∂volume := by
    intro φ hφ
    rw [← lintegral_map hφ hinv, hJac,
      lintegral_withDensity_eq_lintegral_mul _ hJmeas hφ]
    simp only [Pi.mul_apply]
  -- Norm in factored form: `N(x) = (∏_{real} |x_w|)·(∏_{complex} |z_w|²)`.
  have hval : ∀ x : mixedEmbedding.mixedSpace K,
      (∏ w : {w : InfinitePlace K // IsReal w}, (‖x.1 w‖ ^ 2)⁻¹)
        * (∏ w : {w : InfinitePlace K // IsComplex w}, (‖x.2 w‖ ^ 4)⁻¹)
        = ((mixedEmbedding.norm x) ^ 2)⁻¹ := by
    intro x
    have hreal : (∏ w : {w : InfinitePlace K // IsReal w},
          (normAtPlace w.1 x) ^ (mult w.1))
        = ∏ w : {w : InfinitePlace K // IsReal w}, ‖x.1 w‖ :=
      Finset.prod_congr rfl fun w _ => by
        rw [mult_isReal, pow_one, normAtPlace_apply_of_isReal w.prop]
    have hcpx : (∏ w : {w : InfinitePlace K // IsComplex w},
          (normAtPlace w.1 x) ^ (mult w.1))
        = ∏ w : {w : InfinitePlace K // IsComplex w}, ‖x.2 w‖ ^ 2 :=
      Finset.prod_congr rfl fun w _ => by
        rw [mult_isComplex, normAtPlace_apply_of_isComplex w.prop]
    have hn : mixedEmbedding.norm x
        = (∏ w : {w : InfinitePlace K // IsReal w}, ‖x.1 w‖)
          * (∏ w : {w : InfinitePlace K // IsComplex w}, ‖x.2 w‖ ^ 2) := by
      rw [mixedEmbedding.norm_apply, InfinitePlace.prod_eq_prod_mul_prod, hreal, hcpx]
    rw [hn, mul_pow, mul_inv, ← Finset.prod_pow, ← Finset.prod_pow,
      ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [show ((‖x.2 w‖ : ℝ) ^ 2) ^ 2 = ‖x.2 w‖ ^ 4 from by ring]
  -- **Pointwise Jacobian identity** (Step 2): `D(x⁻¹)·J(x) = D(x)` everywhere.
  have hpt : ∀ a : mixedEmbedding.mixedSpace K,
      D a⁻¹ * (Dr a.1 * Dc a.2) = D a := by
    intro a
    have h1 : D a⁻¹ = ENNReal.ofReal (c * mixedEmbedding.norm a) := by
      show ENNReal.ofReal (c * (mixedEmbedding.norm a⁻¹)⁻¹) = _
      rw [mixedEmbedding_norm_inv, inv_inv]
    have h2 : Dr a.1 * Dc a.2 = ENNReal.ofReal ((mixedEmbedding.norm a ^ 2)⁻¹) := by
      simp only [hDr, hDc]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ => by positivity),
        ← ENNReal.ofReal_prod_of_nonneg (fun w _ => by positivity),
        ← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => by positivity), hval a]
    rw [h1, h2,
      ← ENNReal.ofReal_mul (mul_nonneg hc0 (mixedEmbedding.norm_nonneg a))]
    show ENNReal.ofReal _ = ENNReal.ofReal (c * (mixedEmbedding.norm a)⁻¹)
    congr 1
    rw [mul_assoc]
    congr 1
    rcases eq_or_ne (mixedEmbedding.norm a) 0 with h | h
    · simp [h]
    · field_simp
  -- **Assembly** (Step 3): test both measures against an arbitrary measurable `g`.
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  have hginv : Measurable (fun a : mixedEmbedding.mixedSpace K => g a⁻¹) :=
    hg.comp hinv
  rw [hμ, lintegral_map hg hinv,
    lintegral_withDensity_eq_lintegral_mul _ hDmeas hginv,
    lintegral_withDensity_eq_lintegral_mul _ hDmeas hg]
  simp only [Pi.mul_apply]
  -- Goal: `∫⁻ a, D a * g a⁻¹ = ∫⁻ a, D a * g a`.
  have hφg : Measurable (fun a : mixedEmbedding.mixedSpace K => D a⁻¹ * g a) :=
    (hDmeas.comp hinv).mul hg
  calc ∫⁻ a, D a * g a⁻¹ ∂(volume : Measure (mixedEmbedding.mixedSpace K))
      = ∫⁻ a, (fun y => D y⁻¹ * g y) a⁻¹ ∂volume := by
        refine lintegral_congr fun a => ?_; simp only [inv_inv]
    _ = ∫⁻ a, (Dr a.1 * Dc a.2) * (D a⁻¹ * g a) ∂volume :=
        hcov (fun a => D a⁻¹ * g a) hφg
    _ = ∫⁻ a, D a * g a ∂volume := by
        refine lintegral_congr fun a => ?_
        rw [← mul_assoc, mul_comm (Dr a.1 * Dc a.2) (D a⁻¹), hpt a]
end DedekindZeta
