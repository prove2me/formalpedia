-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.mixedMulHaar_norm_eq_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:44:44.260994+00:00
-- url     : https://prove2.me/submissions/7ee78f06-0da6-4cf7-a9ad-ae488fe4a69e

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_norm_radialMap
import Theorems.Thm_DedekindZeta_ConeRadialReduction_lintegral_radialMap_mixedMulHaar
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
theorem _root_.solution {c : ℝ} (hc : 0 < c) :
    DedekindZeta.mixedMulHaar K {x | mixedEmbedding.norm x = c} = 0 := by
  classical
  haveI : SigmaFinite (DedekindZeta.mixedMulHaar K) := by
    unfold DedekindZeta.mixedMulHaar
    exact SigmaFinite.withDensity_of_ne_top' (fun _ => ENNReal.ofReal_ne_top)
  have hnormmeas : Measurable (mixedEmbedding.norm : mixedSpace K → ℝ) :=
    (mixedEmbedding.continuous_norm K).measurable
  -- The measure of a positive norm-level set is independent of the level.
  have hlevel : ∀ a b : ℝ, 0 < a → 0 < b →
      DedekindZeta.mixedMulHaar K {x | mixedEmbedding.norm x = a}
        = DedekindZeta.mixedMulHaar K {x | mixedEmbedding.norm x = b} := by
    intro a b ha hb
    have hi : ∀ (s : Set (mixedSpace K)), MeasurableSet s →
        ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂(DedekindZeta.mixedMulHaar K)
          = DedekindZeta.mixedMulHaar K s := by
      intro s hs
      rw [lintegral_indicator hs]
      exact setLIntegral_one s
    have ht : 0 < a / b := div_pos ha hb
    have hmeasa : MeasurableSet {x : mixedSpace K | mixedEmbedding.norm x = a} :=
      hnormmeas (measurableSet_singleton a)
    have hmeasb : MeasurableSet {x : mixedSpace K | mixedEmbedding.norm x = b} :=
      hnormmeas (measurableSet_singleton b)
    have key := lintegral_radialMap_mixedMulHaar
      ({x : mixedSpace K | mixedEmbedding.norm x = a}.indicator (fun _ => (1 : ℝ≥0∞)))
      ((measurable_const).indicator hmeasa) ht
    -- Pointwise: the scaled indicator of `{N = a}` is the indicator of `{N = b}`.
    have hpt : (fun x => ({x : mixedSpace K | mixedEmbedding.norm x = a}.indicator
          (fun _ => (1 : ℝ≥0∞))) (radialMap K (a / b) x))
        = {x : mixedSpace K | mixedEmbedding.norm x = b}.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext x
      have hN : mixedEmbedding.norm (radialMap K (a / b) x) = (a / b) * mixedEmbedding.norm x :=
        norm_radialMap (a / b) ht x
      by_cases hx : mixedEmbedding.norm x = b
      · rw [Set.indicator_of_mem (s := {x : mixedSpace K | mixedEmbedding.norm x = a})
              (show radialMap K (a / b) x ∈ {x : mixedSpace K | mixedEmbedding.norm x = a} by
                simp only [Set.mem_setOf_eq, hN, hx, div_mul_cancel₀ a hb.ne']),
            Set.indicator_of_mem (show x ∈ {x : mixedSpace K | mixedEmbedding.norm x = b} from hx)]
      · rw [Set.indicator_of_notMem
              (show radialMap K (a / b) x ∉ {x : mixedSpace K | mixedEmbedding.norm x = a} by
                simp only [Set.mem_setOf_eq, hN]
                intro h
                apply hx
                have hcancel : (a / b) * mixedEmbedding.norm x = (a / b) * b := by
                  rw [h, div_mul_cancel₀ a hb.ne']
                exact mul_left_cancel₀ (div_ne_zero ha.ne' hb.ne') hcancel),
            Set.indicator_of_notMem (show x ∉ {x : mixedSpace K | mixedEmbedding.norm x = b} from hx)]
    rw [hpt, hi _ hmeasb, hi _ hmeasa] at key
    exact key.symm
  -- If `{N = c}` had positive measure, all positive levels would, contradicting countability.
  by_contra hne
  have hpos : 0 < DedekindZeta.mixedMulHaar K {x | mixedEmbedding.norm x = c} :=
    pos_iff_ne_zero.mpr hne
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆
      {t : ℝ | 0 < DedekindZeta.mixedMulHaar K {x | mixedEmbedding.norm x = t}} := by
    intro b hb
    rw [Set.mem_setOf_eq, hlevel b c hb.1 hc]
    exact hpos
  have hcount : Set.Countable
      {t : ℝ | 0 < DedekindZeta.mixedMulHaar K {x | mixedEmbedding.norm x = t}} :=
    Measure.countable_meas_level_set_pos hnormmeas
  have hIoo : (Set.Ioo (0 : ℝ) 1).Countable := hcount.mono hsub
  rw [Cardinal.Real.Ioo_countable_iff] at hIoo
  linarith
end DedekindZeta.ConeRadialReduction
