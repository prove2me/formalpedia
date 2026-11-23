-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.setLIntegral_cone_eq_collar_radial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:37:30.763924+00:00
-- url     : https://prove2.me/submissions/19b842eb-698e-47ad-b4e6-1f25c914a96a

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_continuous_radialMap_uncurry
import Theorems.Thm_DedekindZeta_ConeRadialReduction_lintegral_collar_weight
import Theorems.Thm_DedekindZeta_ConeRadialReduction_lintegral_radialMap_collar
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_ae_norm_ne_zero
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply


attribute [local simp] DedekindZeta.ConeRadialReduction.mem_normEqOneSurface

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (h : mixedSpace K → ℝ≥0∞)
    (hh : Measurable h) :
    ∫⁻ x in mixedEmbedding.fundamentalCone K, h x ∂(DedekindZeta.mixedMulHaar K)
      = ∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
            {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
          (∫⁻ t in Set.Ioi (0 : ℝ),
              h (radialMap K t x) * ENNReal.ofReal t⁻¹ ∂volume)
            ∂(DedekindZeta.mixedMulHaar K) := by
  classical
  -- `mixedMulHaar K = volume.withDensity (ofReal _)` has a finite density, hence is
  -- `SigmaFinite`; this powers the two Tonelli swaps below.
  haveI hsf : SigmaFinite (DedekindZeta.mixedMulHaar K) := by
    unfold DedekindZeta.mixedMulHaar
    exact SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  have hN_meas : Measurable (mixedEmbedding.norm : mixedSpace K → ℝ) :=
    (mixedEmbedding.continuous_norm K).measurable
  have hcone_meas : MeasurableSet (mixedEmbedding.fundamentalCone K) :=
    measurableSet_fundamentalCone K
  -- Measurability of the collar indicator as a function of the radius `t` (fixed `n`).
  have hg1_meas : ∀ n : ℝ, Measurable
      (fun t : ℝ => (Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞) n) := by
    intro n
    have heq : (fun t : ℝ => (Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞) n)
        = Set.indicator {t : ℝ | n ∈ Set.Ioc t (Real.exp 1 * t)} (fun _ => (1 : ℝ≥0∞)) := by
      funext t
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
    rw [heq]
    refine measurable_const.indicator ?_
    have hset : {t : ℝ | n ∈ Set.Ioc t (Real.exp 1 * t)}
        = {t : ℝ | t < n} ∩ {t : ℝ | n ≤ Real.exp 1 * t} := by
      ext t; simp [Set.mem_Ioc, Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [hset]
    exact (measurableSet_lt measurable_id measurable_const).inter
      (measurableSet_le measurable_const (measurable_const.mul measurable_id))
  -- Joint measurability of the collar indicator in `(t, y)`.
  have hg2_meas : Measurable (fun p : ℝ × mixedSpace K =>
      (Set.Ioc p.1 (Real.exp 1 * p.1)).indicator (1 : ℝ → ℝ≥0∞)
        (mixedEmbedding.norm p.2)) := by
    have heq : (fun p : ℝ × mixedSpace K =>
        (Set.Ioc p.1 (Real.exp 1 * p.1)).indicator (1 : ℝ → ℝ≥0∞)
          (mixedEmbedding.norm p.2))
        = Set.indicator {p : ℝ × mixedSpace K |
            mixedEmbedding.norm p.2 ∈ Set.Ioc p.1 (Real.exp 1 * p.1)}
          (fun _ => (1 : ℝ≥0∞)) := by
      funext p
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
    rw [heq]
    refine measurable_const.indicator ?_
    have hset : {p : ℝ × mixedSpace K |
          mixedEmbedding.norm p.2 ∈ Set.Ioc p.1 (Real.exp 1 * p.1)}
        = {p : ℝ × mixedSpace K | p.1 < mixedEmbedding.norm p.2} ∩
          {p : ℝ × mixedSpace K | mixedEmbedding.norm p.2 ≤ Real.exp 1 * p.1} := by
      ext p; simp [Set.mem_Ioc, Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [hset]
    exact (measurableSet_lt measurable_fst (hN_meas.comp measurable_snd)).inter
      (measurableSet_le (hN_meas.comp measurable_snd)
        (measurable_const.mul measurable_fst))
  -- Joint measurability of `(x, t) ↦ h (radialMap K t x)`.
  have hrad_xt : Measurable (fun p : mixedSpace K × ℝ => radialMap K p.2 p.1) :=
    (continuous_radialMap_uncurry.comp continuous_swap).measurable
  -- `uncurry` measurabilities for the two Tonelli swaps.
  have huncurry1 : Measurable
      (fun p : mixedSpace K × ℝ => h (radialMap K p.2 p.1) * ENNReal.ofReal p.2⁻¹) :=
    (hh.comp hrad_xt).mul (measurable_snd.inv.ennreal_ofReal)
  have huncurry2 : Measurable
      (fun p : ℝ × mixedSpace K => h p.2 *
        ((Set.Ioc p.1 (Real.exp 1 * p.1)).indicator (1 : ℝ → ℝ≥0∞)
            (mixedEmbedding.norm p.2) * ENNReal.ofReal p.1⁻¹)) :=
    (hh.comp measurable_snd).mul (hg2_meas.mul (measurable_fst.inv.ennreal_ofReal))
  refine Eq.symm ?_
  calc
    ∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
          {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
        (∫⁻ t in Set.Ioi (0 : ℝ),
            h (radialMap K t x) * ENNReal.ofReal t⁻¹ ∂volume)
          ∂(DedekindZeta.mixedMulHaar K)
        = ∫⁻ t in Set.Ioi (0 : ℝ),
            ∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
                {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
              h (radialMap K t x) * ENNReal.ofReal t⁻¹
              ∂(DedekindZeta.mixedMulHaar K) ∂volume :=
        lintegral_lintegral_swap huncurry1.aemeasurable
    -- step 1: restricted radial change of variable, then pull the radial weight out
    _ = ∫⁻ t in Set.Ioi (0 : ℝ),
          (∫⁻ y in (mixedEmbedding.fundamentalCone K ∩
              {y | mixedEmbedding.norm y ∈ Set.Ioc t (Real.exp 1 * t)}),
            h y ∂(DedekindZeta.mixedMulHaar K)) * ENNReal.ofReal t⁻¹ ∂volume := by
        refine lintegral_congr_ae ?_
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        have htpos : 0 < t := ht
        have hrad_t : Measurable (fun x : mixedSpace K => radialMap K t x) :=
          (continuous_radialMap_uncurry.comp
            (continuous_const.prodMk continuous_id)).measurable
        have hcomp : Measurable (fun x : mixedSpace K => h (radialMap K t x)) :=
          hh.comp hrad_t
        rw [lintegral_mul_const (ENNReal.ofReal t⁻¹) hcomp,
          lintegral_radialMap_collar h hh htpos]
    -- rewrite the scaled collar as a cone integral against the collar indicator
    _ = ∫⁻ t in Set.Ioi (0 : ℝ),
          ∫⁻ y in mixedEmbedding.fundamentalCone K,
            h y * ((Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞)
              (mixedEmbedding.norm y) * ENNReal.ofReal t⁻¹)
            ∂(DedekindZeta.mixedMulHaar K) ∂volume := by
        refine lintegral_congr (fun t => ?_)
        have hS_meas : MeasurableSet
            {y : mixedSpace K | mixedEmbedding.norm y ∈ Set.Ioc t (Real.exp 1 * t)} :=
          hN_meas measurableSet_Ioc
        have hindmeas : Measurable (fun y : mixedSpace K =>
            (Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞)
              (mixedEmbedding.norm y)) :=
          (measurable_const.indicator measurableSet_Ioc).comp hN_meas
        have hpt : ∀ y : mixedSpace K,
            h y * (Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞)
                (mixedEmbedding.norm y)
              = {y : mixedSpace K |
                  mixedEmbedding.norm y ∈ Set.Ioc t (Real.exp 1 * t)}.indicator h y := by
          intro y
          by_cases hyn : mixedEmbedding.norm y ∈ Set.Ioc t (Real.exp 1 * t)
          · rw [Set.indicator_of_mem hyn, Set.indicator_of_mem (show y ∈ _ from hyn),
              Pi.one_apply, mul_one]
          · rw [Set.indicator_of_notMem hyn, Set.indicator_of_notMem (show y ∉ _ from hyn),
              mul_zero]
        have hcs : ∫⁻ y in (mixedEmbedding.fundamentalCone K ∩
              {y | mixedEmbedding.norm y ∈ Set.Ioc t (Real.exp 1 * t)}),
            h y ∂(DedekindZeta.mixedMulHaar K)
            = ∫⁻ y in mixedEmbedding.fundamentalCone K,
              h y * (Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞)
                (mixedEmbedding.norm y) ∂(DedekindZeta.mixedMulHaar K) := by
          rw [lintegral_congr hpt, ← lintegral_indicator hcone_meas,
            Set.indicator_indicator, lintegral_indicator (hcone_meas.inter hS_meas)]
        rw [hcs]
        have hmul := lintegral_mul_const (μ := (DedekindZeta.mixedMulHaar K).restrict (mixedEmbedding.fundamentalCone K)) (ENNReal.ofReal t⁻¹) (hh.mul hindmeas)
        simp only [Pi.mul_apply] at hmul
        rw [← hmul]
        exact lintegral_congr (fun y => by rw [mul_assoc])
    -- step: Tonelli swap `t` and `y`
    _ = ∫⁻ y in mixedEmbedding.fundamentalCone K,
          ∫⁻ t in Set.Ioi (0 : ℝ),
            h y * ((Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞)
              (mixedEmbedding.norm y) * ENNReal.ofReal t⁻¹) ∂volume
            ∂(DedekindZeta.mixedMulHaar K) :=
        lintegral_lintegral_swap huncurry2.aemeasurable
    -- step 5: the inner 1D radial weight integral equals `1` on `N y > 0`
    _ = ∫⁻ y in mixedEmbedding.fundamentalCone K,
          h y * (if 0 < mixedEmbedding.norm y then (1 : ℝ≥0∞) else 0)
          ∂(DedekindZeta.mixedMulHaar K) := by
        refine lintegral_congr (fun y => ?_)
        have hmul := lintegral_const_mul (μ := volume.restrict (Set.Ioi (0 : ℝ))) (h y)
            ((hg1_meas (mixedEmbedding.norm y)).mul (measurable_inv.ennreal_ofReal))
        simp only [Pi.mul_apply] at hmul
        rw [hmul]
        congr 1
        rw [show (fun t => (Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞)
                (mixedEmbedding.norm y) * ENNReal.ofReal t⁻¹)
              = (fun t => ENNReal.ofReal t⁻¹ *
                  (Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞)
                    (mixedEmbedding.norm y)) from by funext t; rw [mul_comm]]
        exact lintegral_collar_weight (mixedEmbedding.norm y)
    -- step 6: discard the `μ`-null locus `{N = 0}`
    _ = ∫⁻ x in mixedEmbedding.fundamentalCone K, h x ∂(DedekindZeta.mixedMulHaar K) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae (DedekindZeta.ae_norm_ne_zero (K := K))] with y hy
        have hpos : 0 < mixedEmbedding.norm y :=
          lt_of_le_of_ne (mixedEmbedding.norm_nonneg y) (Ne.symm hy)
        rw [if_pos hpos, mul_one]
end DedekindZeta.ConeRadialReduction
