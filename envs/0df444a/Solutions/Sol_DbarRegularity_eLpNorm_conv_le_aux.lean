-- Prove2me | solution 1 for DbarRegularity.eLpNorm_conv_le_aux
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T15:25:51.720647+00:00
-- url     : https://prove2.me/submissions/36cc46fe-9e57-4c20-83f0-292d2d2ef046

import Mathlib.Analysis.Fourier.LpSpace
import Theorems.Thm_DbarRegularity_fourierTransformL2_ae_eq_fourier
import Theorems.Thm_DbarRegularity_aestronglyMeasurable_integral_mul_sub
import Theorems.Thm_DbarRegularity_eLpNorm_integral_mul_sub_le
import Theorems.Thm_DbarRegularity_eLpNorm_fourier_two_eq
import Theorems.Thm_DbarRegularity_integrable_mul_sub_of_memLp_two
import Theorems.Thm_DbarRegularity_enorm_fourier_le
import Mathlib.Analysis.Fourier.Convolution



namespace DbarRegularity

open MeasureTheory FourierTransform Filter Topology
open scoped ENNReal NNReal Convolution

/-- The `L²` bound for `f ∈ L¹ ∩ L²`, up to an error controlled by a compactly supported
continuous approximation `K'` of `K`. -/
theorem eLpNorm_conv_le_aux {d : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℂ) (hK : MemLp K 2 volume) (B : ℝ)
    (hB : ∀ᵐ ξ, ‖Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin d)) ℂ (hK.toLp K) ξ‖ ≤ B)
    (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (K' : EuclideanSpace ℝ (Fin d) → ℂ) (hK'c : Continuous K') (hK's : HasCompactSupport K')
    (hK'2 : MemLp K' 2 volume) :
    eLpNorm (fun x => ∫ y, K (x - y) * f y) 2 volume ≤
      ENNReal.ofReal B * eLpNorm f 2 volume +
        2 * (eLpNorm (K - K') 2 volume * eLpNorm f 1 volume) := by
  have hK'1 : Integrable K' volume := hK'c.integrable_of_hasCompactSupport hK's
  set T' : EuclideanSpace ℝ (Fin d) → ℂ := fun x => ∫ y, K' (x - y) * f y with hT'
  set T'' : EuclideanSpace ℝ (Fin d) → ℂ := fun x => ∫ y, (K - K') (x - y) * f y with hT''
  have hsplit : (fun x => ∫ y, K (x - y) * f y) = T' + T'' := by
    funext x
    simp only [hT', hT'', Pi.add_apply, Pi.sub_apply]
    rw [← integral_add (integrable_mul_sub_of_memLp_two hK'2 hf2 x)
      ((integrable_mul_sub_of_memLp_two hK hf2 x).sub
        (integrable_mul_sub_of_memLp_two hK'2 hf2 x) |>.congr (ae_of_all _ fun y => by
          simp [sub_mul]))]
    congr 1; funext y; ring
  have hT'm : AEStronglyMeasurable T' volume :=
    aestronglyMeasurable_integral_mul_sub K' f hK'2.1 hf1.1
  have hT''m : AEStronglyMeasurable T'' volume :=
    aestronglyMeasurable_integral_mul_sub (K - K') f (hK.1.sub hK'2.1) hf1.1
  have hT''b : eLpNorm T'' 2 volume ≤ eLpNorm (K - K') 2 volume * eLpNorm f 1 volume :=
    eLpNorm_integral_mul_sub_le (K - K') f (hK.1.sub hK'2.1) hf1.1
  -- `T'` is the convolution `f ⋆ K'`
  have hconv : T' = f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] K' := by
    funext x
    simp only [hT', convolution_def, ContinuousLinearMap.mul_apply']
    congr 1; funext y; ring
  have hT'1 : Integrable T' volume := by
    rw [hconv]; exact hf1.integrable_convolution _ hK'1
  have hT'2 : MemLp T' 2 volume := by
    refine ⟨hT'm, lt_of_le_of_lt (eLpNorm_integral_mul_sub_le K' f hK'2.1 hf1.1) ?_⟩
    exact ENNReal.mul_lt_top hK'2.2 (memLp_one_iff_integrable.2 hf1).2
  have hFT' : 𝓕 T' = fun ξ => 𝓕 f ξ * 𝓕 K' ξ := by
    funext ξ; rw [hconv]; exact Real.fourier_mul_convolution_eq hf1 hK'1 ξ
  -- the `L²` Fourier transforms of `K` and `K'`
  set FK : EuclideanSpace ℝ (Fin d) → ℂ :=
    (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin d)) ℂ (hK.toLp K) :
      EuclideanSpace ℝ (Fin d) → ℂ) with hFK
  have hK'ae := fourierTransformL2_ae_eq_fourier K' hK'1 hK'2
  have hdiff : eLpNorm (𝓕 K' - FK) 2 volume ≤ eLpNorm (K - K') 2 volume := by
    have h1 : (𝓕 K' - FK) =ᵐ[volume] (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin d)) ℂ
        (hK'2.toLp K' - hK.toLp K) : EuclideanSpace ℝ (Fin d) → ℂ) := by
      rw [map_sub]
      filter_upwards [hK'ae, Lp.coeFn_sub (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin d)) ℂ
        (hK'2.toLp K')) (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin d)) ℂ (hK.toLp K))]
        with ξ h1 h2
      rw [h2, Pi.sub_apply, Pi.sub_apply, h1]
    rw [eLpNorm_congr_ae h1, ← Lp.enorm_def, enorm_eq_nnnorm, LinearIsometryEquiv.nnnorm_map,
      ← enorm_eq_nnnorm, Lp.enorm_def, eLpNorm_sub_comm]
    refine le_of_eq (eLpNorm_congr_ae ?_)
    filter_upwards [Lp.coeFn_sub (hK'2.toLp K') (hK.toLp K), hK'2.coeFn_toLp, hK.coeFn_toLp]
      with ξ h1 h2 h3
    rw [h1, Pi.sub_apply, Pi.sub_apply, h2, h3]
  have hFT'b : eLpNorm (𝓕 T') 2 volume ≤ ENNReal.ofReal B * eLpNorm f 2 volume +
      eLpNorm (K - K') 2 volume * eLpNorm f 1 volume := by
    have hsplit2 : 𝓕 T' = (fun ξ => 𝓕 f ξ * FK ξ) + (fun ξ => 𝓕 f ξ * (𝓕 K' - FK) ξ) := by
      rw [hFT']; funext ξ; simp only [Pi.add_apply, Pi.sub_apply]; ring
    have hFfm : AEStronglyMeasurable (𝓕 f) volume :=
      (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner
        hf1).aestronglyMeasurable
    have hFKm : AEStronglyMeasurable FK volume := (Lp.aestronglyMeasurable _)
    have hK'm : AEStronglyMeasurable (𝓕 K') volume :=
      (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner
        hK'1).aestronglyMeasurable
    rw [hsplit2]
    refine (eLpNorm_add_le (hFfm.mul hFKm) (hFfm.mul (hK'm.sub hFKm)) one_le_two).trans ?_
    gcongr
    · calc eLpNorm (fun ξ => 𝓕 f ξ * FK ξ) 2 volume
          ≤ ENNReal.ofReal B * eLpNorm (𝓕 f) 2 volume := by
            refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' 2 hFfm ?_
            filter_upwards [hB] with ξ hξ
            rw [enorm_mul, mul_comm, ← ofReal_norm_eq_enorm (FK ξ)]
            gcongr
        _ = ENNReal.ofReal B * eLpNorm f 2 volume := by rw [eLpNorm_fourier_two_eq f hf1 hf2]
    · calc eLpNorm (fun ξ => 𝓕 f ξ * (𝓕 K' - FK) ξ) 2 volume
          ≤ eLpNorm f 1 volume * eLpNorm (𝓕 K' - FK) 2 volume := by
            refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' 2 (hK'm.sub hFKm) ?_
            filter_upwards with ξ
            rw [enorm_mul]
            gcongr
            exact enorm_fourier_le f hf1 ξ
        _ ≤ eLpNorm f 1 volume * eLpNorm (K - K') 2 volume := by gcongr
        _ = _ := mul_comm _ _
  rw [hsplit]
  refine (eLpNorm_add_le hT'm hT''m one_le_two).trans ?_
  rw [← eLpNorm_fourier_two_eq T' hT'1 hT'2]
  calc eLpNorm (𝓕 T') 2 volume + eLpNorm T'' 2 volume
      ≤ (ENNReal.ofReal B * eLpNorm f 2 volume +
          eLpNorm (K - K') 2 volume * eLpNorm f 1 volume) +
        eLpNorm (K - K') 2 volume * eLpNorm f 1 volume := add_le_add hFT'b hT''b
    _ = _ := by ring

end DbarRegularity

open DbarRegularity

open MeasureTheory FourierTransform Filter Topology
open scoped ENNReal NNReal Convolution

theorem solution {d : ℕ} (K : EuclideanSpace ℝ (Fin d) → ℂ) (hK : MemLp K 2 volume) (B : ℝ)
    (hB : ∀ᵐ ξ, ‖Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin d)) ℂ (hK.toLp K) ξ‖ ≤ B)
    (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (K' : EuclideanSpace ℝ (Fin d) → ℂ) (hK'c : Continuous K') (hK's : HasCompactSupport K')
    (hK'2 : MemLp K' 2 volume) :
    eLpNorm (fun x => ∫ y, K (x - y) * f y) 2 volume ≤
      ENNReal.ofReal B * eLpNorm f 2 volume +
        2 * (eLpNorm (K - K') 2 volume * eLpNorm f 1 volume) :=
  eLpNorm_conv_le_aux K hK B hB f hf1 hf2 K' hK'c hK's hK'2
