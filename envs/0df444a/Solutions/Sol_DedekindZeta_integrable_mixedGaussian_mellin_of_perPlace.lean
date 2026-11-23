-- Prove2me | solution 1 for DedekindZeta.integrable_mixedGaussian_mellin_of_perPlace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:22:39.911478+00:00
-- url     : https://prove2.me/submissions/321451ae-1a6f-438a-9433-1c015ae35bae

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal
open MeasureTheory NumberField.mixedEmbedding
set_option maxHeartbeats 1600000
namespace DedekindZeta
theorem _root_.solution {s : ℂ} (hs : 0 < s.re)
    (hr : MeasureTheory.Integrable
      (fun x : ℝ => Real.exp (-Real.pi * x ^ 2) * |x| ^ (s.re - 1)) volume)
    (hc : MeasureTheory.Integrable
      (fun z : ℂ => Real.exp (-2 * Real.pi * ‖z‖ ^ 2) * ‖z‖ ^ (2 * (s.re - 1)))
        volume) :
    MeasureTheory.Integrable
      (fun x : mixedEmbedding.mixedSpace K =>
        (Theta.mixedGaussian K x : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s)
      (mixedMulHaar K) := by
  classical
  set σ : ℝ := s.re with hσ
  set c : ℝ := (2 / Real.pi) ^ nrComplexPlaces K with hc_def
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hc_nonneg : 0 ≤ c := by
    rw [hc_def]; positivity
  set fR : ℝ → ℝ := fun x => Real.exp (-Real.pi * x ^ 2) * |x| ^ (σ - 1) with hfR
  set fC : ℂ → ℝ := fun z => Real.exp (-2 * Real.pi * ‖z‖ ^ 2) * ‖z‖ ^ (2 * (σ - 1)) with hfC
  set F : mixedEmbedding.mixedSpace K → ℝ := fun x =>
    c * ((∏ w : {w : InfinitePlace K // IsReal w}, fR (x.1 w)) *
          (∏ w : {w : InfinitePlace K // IsComplex w}, fC (x.2 w))) with hF
  have hRprod : MeasureTheory.Integrable
      (fun a : {w : InfinitePlace K // IsReal w} → ℝ => ∏ w, fR (a w)) volume := by
    rw [volume_pi]
    exact MeasureTheory.Integrable.fintype_prod (fun _ => hr)
  have hCprod : MeasureTheory.Integrable
      (fun b : {w : InfinitePlace K // IsComplex w} → ℂ => ∏ w, fC (b w)) volume := by
    rw [volume_pi]
    exact MeasureTheory.Integrable.fintype_prod (fun _ => hc)
  have hmul : MeasureTheory.Integrable
      (fun x : mixedEmbedding.mixedSpace K =>
        (∏ w : {w : InfinitePlace K // IsReal w}, fR (x.1 w)) *
          (∏ w : {w : InfinitePlace K // IsComplex w}, fC (x.2 w))) volume := by
    exact MeasureTheory.Integrable.mul_prod hRprod hCprod
  have hFint : MeasureTheory.Integrable F volume := by
    rw [hF]; exact hmul.const_mul c
  rw [mixedMulHaar, integrable_withDensity_iff_integrable_smul']
  rotate_left
  · refine (Measurable.ennreal_ofReal ?_)
    exact (measurable_const.mul ((mixedEmbedding.continuous_norm K).measurable.inv))
  · exact ae_of_all _ (fun x => ENNReal.ofReal_lt_top)
  refine hFint.mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    apply Measurable.smul
    · exact Complex.measurable_ofReal.comp
        ((((measurable_const.mul
          ((mixedEmbedding.continuous_norm K).measurable.inv))).ennreal_ofReal).ennreal_toReal)
    · apply Measurable.mul
      · refine Complex.measurable_ofReal.comp ?_
        have : Measurable fun x : mixedEmbedding.mixedSpace K => Theta.mixedGaussian K x := by
          unfold Theta.mixedGaussian; fun_prop
        exact this
      · exact (Complex.measurable_ofReal.comp
          (mixedEmbedding.continuous_norm K).measurable).pow_const s
  · refine ae_of_all _ (fun x => ?_)
    have hN0 : 0 ≤ mixedEmbedding.norm x := mixedEmbedding.norm_nonneg x
    have hdens : (ENNReal.ofReal (c * (mixedEmbedding.norm x)⁻¹)).toReal
        = c * (mixedEmbedding.norm x)⁻¹ := by
      rw [ENNReal.toReal_ofReal]
      positivity
    have hFnonneg : 0 ≤ F x := by
      rw [hF]
      refine mul_nonneg hc_nonneg (mul_nonneg (Finset.prod_nonneg ?_) (Finset.prod_nonneg ?_))
      · intro w _; rw [hfR]; positivity
      · intro w _; rw [hfC]; positivity
    have hgauss_pos : 0 < Theta.mixedGaussian K x := Real.exp_pos _
    have hnormg : ‖(Theta.mixedGaussian K x : ℂ) * (mixedEmbedding.norm x : ℂ) ^ s‖
        = Theta.mixedGaussian K x * (mixedEmbedding.norm x) ^ σ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hgauss_pos.le,
        Complex.norm_cpow_eq_rpow_re_of_nonneg hN0 (by rw [← hσ]; exact ne_of_gt hs)]
    rw [_root_.norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, hdens, hnormg]
    by_cases hx0 : mixedEmbedding.norm x = 0
    · rw [hx0]
      simp only [inv_zero, mul_zero, zero_mul]
      exact hFnonneg
    · have hNpos : 0 < mixedEmbedding.norm x := lt_of_le_of_ne hN0 (Ne.symm hx0)
      have hgaussprod : Theta.mixedGaussian K x
          = ∏ w : InfinitePlace K, Real.exp (-Real.pi * ((mult w : ℝ) * normAtPlace w x ^ 2)) := by
        rw [Theta.mixedGaussian, Finset.mul_sum, Real.exp_sum]
      have hpowprod : (mixedEmbedding.norm x) ^ σ * (mixedEmbedding.norm x)⁻¹
          = ∏ w : InfinitePlace K, normAtPlace w x ^ ((mult w : ℝ) * (σ - 1)) := by
        rw [← Real.rpow_neg_one (mixedEmbedding.norm x),
          ← Real.rpow_add hNpos]
        rw [mixedEmbedding.norm_apply]
        rw [← Real.finsetProd_rpow _ _
          (fun w _ => pow_nonneg (normAtPlace_nonneg w x) _)]
        refine Finset.prod_congr rfl (fun w _ => ?_)
        rw [← Real.rpow_natCast (normAtPlace w x) (mult w),
          ← Real.rpow_mul (normAtPlace_nonneg w x)]
        ring_nf
      have hval : c * (mixedEmbedding.norm x)⁻¹ *
          (Theta.mixedGaussian K x * (mixedEmbedding.norm x) ^ σ) = F x := by
        have e1 : c * (mixedEmbedding.norm x)⁻¹ *
            (Theta.mixedGaussian K x * (mixedEmbedding.norm x) ^ σ)
            = c * (Theta.mixedGaussian K x *
                ((mixedEmbedding.norm x) ^ σ * (mixedEmbedding.norm x)⁻¹)) := by ring
        rw [e1, hgaussprod, hpowprod, ← Finset.prod_mul_distrib, hF,
          InfinitePlace.prod_eq_prod_mul_prod
            (fun w => Real.exp (-Real.pi * ((mult w : ℝ) * normAtPlace w x ^ 2)) *
              normAtPlace w x ^ ((mult w : ℝ) * (σ - 1)))]
        congr 1
        congr 1
        · refine Finset.prod_congr rfl (fun w _ => ?_)
          rw [hfR, mult_isReal, normAtPlace_apply_of_isReal w.2, Nat.cast_one, one_mul, one_mul,
            Real.norm_eq_abs, sq_abs]
        · refine Finset.prod_congr rfl (fun w _ => ?_)
          rw [hfC, mult_isComplex, normAtPlace_apply_of_isComplex w.2, Nat.cast_ofNat]
          congr 1
          congr 1
          ring
      rw [hval]
end DedekindZeta
