-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.lintegral_collar_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:31:37.722013+00:00
-- url     : https://prove2.me/submissions/aa189f35-e1d1-46da-8c24-1110b3d24fde

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
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
theorem _root_.solution (n : ℝ) :
    ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal t⁻¹ * (Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞) n
          ∂volume
      = if 0 < n then 1 else 0 := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  split_ifs with hn
  · -- `n > 0`: rewrite the integrand to the indicator of `Ico (n/e) n`
    set a : ℝ := n / Real.exp 1 with ha
    have hapos : 0 < a := div_pos hn he
    have hbe : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
    have han : a < n := by
      rw [ha, div_lt_iff₀ he]
      nlinarith [hn]
    -- pointwise rewrite of the integrand on `Ioi 0`
    have hcongr : Set.EqOn
        (fun t => ENNReal.ofReal t⁻¹ *
            (Set.Ioc t (Real.exp 1 * t)).indicator (1 : ℝ → ℝ≥0∞) n)
        ((Set.Ico a n).indicator (fun t => ENNReal.ofReal t⁻¹))
        (Set.Ioi (0 : ℝ)) := by
      intro t _
      dsimp only
      by_cases hmem : n ∈ Set.Ioc t (Real.exp 1 * t)
      · rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one,
            Set.indicator_of_mem (Set.mem_Ico.mpr ⟨?_, hmem.1⟩)]
        rw [ha, div_le_iff₀ he, mul_comm]
        exact hmem.2
      · rw [Set.indicator_of_notMem hmem, mul_zero,
            Set.indicator_of_notMem ?_]
        intro hmem2
        rw [Set.mem_Ico] at hmem2
        exact hmem (Set.mem_Ioc.mpr ⟨hmem2.2, by
          rw [mul_comm]; rw [ha, div_le_iff₀ he] at hmem2; exact hmem2.1⟩)
    have hsub : Set.Ico a n ⊆ Set.Ioi (0 : ℝ) :=
      fun t ht => lt_of_lt_of_le hapos ht.1
    rw [setLIntegral_congr_fun measurableSet_Ioi hcongr,
        setLIntegral_indicator measurableSet_Ico,
        Set.inter_eq_left.mpr hsub]
    -- convert `Ico` to `Ioc` (single points are null), then to an interval integral
    rw [setLIntegral_congr (MeasureTheory.Ico_ae_eq_Icc.trans
        MeasureTheory.Ioc_ae_eq_Icc.symm)]
    have hne : ∀ x : ℝ, x ∈ Set.uIcc a n → id x ≠ 0 := by
      intro x hx
      rw [Set.uIcc_of_le han.le, Set.mem_Icc] at hx
      exact (lt_of_lt_of_le hapos hx.1).ne'
    have hii : IntervalIntegrable (fun x : ℝ => x⁻¹) volume a n :=
      intervalIntegral.intervalIntegrable_inv (f := id) hne continuousOn_id
    have hintegrable : Integrable (fun t : ℝ => t⁻¹)
        (volume.restrict (Set.Ioc a n)) := hii.1
    have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc a n)] (fun t : ℝ => t⁻¹) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact inv_nonneg.mpr (lt_trans hapos ht.1).le
    have hint : ∫ t in Set.Ioc a n, t⁻¹ ∂volume = 1 := by
      have h0 : (0 : ℝ) ∉ Set.uIcc a n := by
        rw [Set.uIcc_of_le han.le, Set.mem_Icc]
        rintro ⟨hle, _⟩; linarith
      rw [← intervalIntegral.integral_of_le han.le, integral_inv h0]
      have hdiv : n / a = Real.exp 1 := by
        rw [ha, div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self hn.ne', mul_one]
      rw [hdiv, Real.log_exp]
    rw [← ofReal_integral_eq_lintegral_ofReal hintegrable hnonneg, hint,
        ENNReal.ofReal_one]
  · -- `n ≤ 0`: the indicator is identically `0` on `Ioi 0`
    refine setLIntegral_eq_zero measurableSet_Ioi ?_
    intro t ht
    have htpos : 0 < t := ht
    have hn' : n ≤ 0 := not_lt.mp hn
    have hnotmem : n ∉ Set.Ioc t (Real.exp 1 * t) := by
      rw [Set.mem_Ioc]; rintro ⟨h1, _⟩; linarith
    simp [Set.indicator_of_notMem hnotmem]
end DedekindZeta.ConeRadialReduction
