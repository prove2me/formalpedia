-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.setLIntegral_cone_eq_radial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:40:36.458625+00:00
-- url     : https://prove2.me/submissions/3f0485c0-b30c-4247-8f21-4904c6450cb9

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_continuous_radialMap_uncurry
import Theorems.Thm_DedekindZeta_ConeRadialReduction_surfaceMeasure_apply_compl_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_radialMap_radialMap
import Theorems.Thm_DedekindZeta_ConeRadialReduction_setLIntegral_cone_eq_collar_radial
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply


attribute [local simp] DedekindZeta.ConeRadialReduction.mem_normEqOneSurface
section
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
namespace DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
private theorem lintegral_Ioi_const_mul {F : ℝ → ℝ≥0∞} (hF : Measurable F)
    {n : ℝ} (hn : 0 < n) :
    ∫⁻ s in Set.Ioi (0:ℝ), F (n * s) ∂volume
      = ENNReal.ofReal n⁻¹ * ∫⁻ r in Set.Ioi (0:ℝ), F r ∂volume := by
  have hind : Measurable ((Set.Ioi (0:ℝ)).indicator F) := hF.indicator measurableSet_Ioi
  have hkey : (fun s : ℝ => (Set.Ioi (0:ℝ)).indicator F (n * s))
      = (Set.Ioi (0:ℝ)).indicator (fun s => F (n * s)) := by
    funext s
    by_cases hs : s ∈ Set.Ioi (0:ℝ)
    · have hns : n * s ∈ Set.Ioi (0:ℝ) := by
        simp only [Set.mem_Ioi] at hs ⊢; positivity
      rw [Set.indicator_of_mem hns, Set.indicator_of_mem hs]
    · have hns : n * s ∉ Set.Ioi (0:ℝ) := by
        simp only [Set.mem_Ioi, not_lt] at hs ⊢
        exact mul_nonpos_iff.mpr (Or.inl ⟨hn.le, hs⟩)
      rw [Set.indicator_of_notMem hns, Set.indicator_of_notMem hs]
  calc
    ∫⁻ s in Set.Ioi (0:ℝ), F (n * s) ∂volume
        = ∫⁻ s, (Set.Ioi (0:ℝ)).indicator (fun s => F (n * s)) s ∂volume := by
          rw [lintegral_indicator measurableSet_Ioi]
      _ = ∫⁻ s, (Set.Ioi (0:ℝ)).indicator F (n * s) ∂volume := by rw [hkey]
      _ = ∫⁻ r, (Set.Ioi (0:ℝ)).indicator F r ∂(Measure.map (fun s : ℝ => n * s) volume) := by
          rw [lintegral_map hind (by fun_prop)]
      _ = ∫⁻ r, (Set.Ioi (0:ℝ)).indicator F r ∂(ENNReal.ofReal |n⁻¹| • volume) := by
          rw [Real.map_volume_mul_left hn.ne']
      _ = ENNReal.ofReal |n⁻¹| * ∫⁻ r, (Set.Ioi (0:ℝ)).indicator F r ∂volume := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ = ENNReal.ofReal n⁻¹ * ∫⁻ r in Set.Ioi (0:ℝ), F r ∂volume := by
          rw [lintegral_indicator measurableSet_Ioi, abs_of_pos (inv_pos.mpr hn)]
end DedekindZeta.ConeRadialReduction
end

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (h : mixedSpace K → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ x in mixedEmbedding.fundamentalCone K, h x ∂(DedekindZeta.mixedMulHaar K)
      = ∫⁻ r in Set.Ioi (0 : ℝ),
          (∫⁻ σ in normEqOneSurface K, h (radialMap K r σ) ∂(surfaceMeasure K))
            * ENNReal.ofReal (r⁻¹) ∂volume := by
  classical
  haveI : SFinite (DedekindZeta.mixedMulHaar K) := by
    unfold DedekindZeta.mixedMulHaar; infer_instance
  have hq : (0 : ℝ) ≤ ((finrank ℚ K : ℝ))⁻¹ := by positivity
  have hradialProj : Measurable (radialProj K) := by
    have hscalar : Measurable
        (fun x : mixedSpace K => (mixedEmbedding.norm x)⁻¹ ^ ((finrank ℚ K : ℝ))⁻¹) :=
      (Real.continuous_rpow_const hq).measurable.comp
        ((mixedEmbedding.continuous_norm K).measurable.inv)
    exact hscalar.smul measurable_id
  -- (1) Push the surface measure back to the collar, rewriting the inner integral.
  have hinner : ∀ r : ℝ, 0 ≤ r →
      (∫⁻ σ in normEqOneSurface K, h (radialMap K r σ) ∂(surfaceMeasure K))
        = ∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
            {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
            h (radialMap K (r / mixedEmbedding.norm x) x) ∂(DedekindZeta.mixedMulHaar K) := by
    intro r hr
    have hgσ : Measurable (fun σ : mixedSpace K => h (radialMap K r σ)) := by
      have hcont : Continuous (fun σ : mixedSpace K => radialMap K r σ) := by
        simp only [radialMap]
        exact (continuous_const : Continuous (fun _ : mixedSpace K => (r ^ ((finrank ℚ K : ℝ)⁻¹) : ℝ))).smul continuous_id
      exact hh.comp hcont.measurable
    rw [show (surfaceMeasure K).restrict (normEqOneSurface K) = surfaceMeasure K from
          Measure.restrict_eq_self_of_ae_mem
            (ae_iff.mpr surfaceMeasure_apply_compl_normEqOneSurface)]
    unfold surfaceMeasure
    rw [lintegral_map hgσ hradialProj]
    refine lintegral_congr (fun x => ?_)
    congr 1
    rw [radialProj,
      radialMap_radialMap r (mixedEmbedding.norm x)⁻¹ hr
        (inv_nonneg.mpr (mixedEmbedding.norm_nonneg x)) x,
      div_eq_mul_inv]
  -- (2) Measurability of the integrand in `x` for fixed `r`, and jointly in `(r, x)`.
  have hFmeas : ∀ r : ℝ,
      Measurable (fun x : mixedSpace K => h (radialMap K (r / mixedEmbedding.norm x) x)) := by
    intro r
    have hsc : Measurable (fun x : mixedSpace K =>
        (r / mixedEmbedding.norm x) ^ ((finrank ℚ K : ℝ))⁻¹) :=
      (Real.continuous_rpow_const hq).measurable.comp
        (measurable_const.div (mixedEmbedding.continuous_norm K).measurable)
    have hrm : Measurable (fun x : mixedSpace K => radialMap K (r / mixedEmbedding.norm x) x) := by
      simp only [radialMap]; exact hsc.smul measurable_id
    exact hh.comp hrm
  have hf_meas : Measurable (fun p : ℝ × mixedSpace K =>
      h (radialMap K (p.1 / mixedEmbedding.norm p.2) p.2) * ENNReal.ofReal p.1⁻¹) := by
    refine Measurable.mul ?_ ?_
    · have hpair : Measurable (fun p : ℝ × mixedSpace K =>
          (p.1 / mixedEmbedding.norm p.2, p.2)) :=
        (measurable_fst.div
          ((mixedEmbedding.continuous_norm K).measurable.comp measurable_snd)).prodMk
            measurable_snd
      exact hh.comp ((continuous_radialMap_uncurry).measurable.comp hpair)
    · exact (measurable_fst.inv).ennreal_ofReal
  -- (3) The per-`x` radial substitution `r = N x · t`, collapsing the `r`-integral.
  have hsub : ∀ x : mixedSpace K, 0 < mixedEmbedding.norm x →
      (∫⁻ r in Set.Ioi (0:ℝ),
          h (radialMap K (r / mixedEmbedding.norm x) x) * ENNReal.ofReal r⁻¹ ∂volume)
        = ∫⁻ t in Set.Ioi (0:ℝ),
            h (radialMap K t x) * ENNReal.ofReal t⁻¹ ∂volume := by
    intro x hn
    set n : ℝ := mixedEmbedding.norm x with hndef
    have hf0 : Measurable (fun r : ℝ =>
        h (radialMap K (r / n) x) * ENNReal.ofReal r⁻¹) := by
      refine Measurable.mul ?_ ?_
      · have hsc : Measurable (fun r : ℝ => (r / n) ^ ((finrank ℚ K : ℝ))⁻¹) :=
          (Real.continuous_rpow_const hq).measurable.comp (measurable_id.div_const n)
        have hrm : Measurable (fun r : ℝ => radialMap K (r / n) x) := by
          simp only [radialMap]; exact hsc.smul measurable_const
        exact hh.comp hrm
      · exact (measurable_id.inv).ennreal_ofReal
    have hmeas2 : Measurable (fun s : ℝ =>
        h (radialMap K s x) * ENNReal.ofReal s⁻¹) := by
      refine Measurable.mul ?_ ?_
      · have hsc : Measurable (fun s : ℝ => s ^ ((finrank ℚ K : ℝ))⁻¹) :=
          (Real.continuous_rpow_const hq).measurable
        have hrm : Measurable (fun s : ℝ => radialMap K s x) := by
          simp only [radialMap]; exact hsc.smul measurable_const
        exact hh.comp hrm
      · exact (measurable_id.inv).ennreal_ofReal
    have hIA : (∫⁻ s in Set.Ioi (0:ℝ),
        h (radialMap K ((n * s) / n) x) * ENNReal.ofReal (n * s)⁻¹ ∂volume)
        = ENNReal.ofReal n⁻¹ * ∫⁻ r in Set.Ioi (0:ℝ),
            h (radialMap K (r / n) x) * ENNReal.ofReal r⁻¹ ∂volume :=
      lintegral_Ioi_const_mul hf0 hn
    have hIB : (∫⁻ s in Set.Ioi (0:ℝ),
        h (radialMap K ((n * s) / n) x) * ENNReal.ofReal (n * s)⁻¹ ∂volume)
        = ENNReal.ofReal n⁻¹ * ∫⁻ t in Set.Ioi (0:ℝ),
            h (radialMap K t x) * ENNReal.ofReal t⁻¹ ∂volume := by
      have hcongr : (∫⁻ s in Set.Ioi (0:ℝ),
            h (radialMap K ((n * s) / n) x) * ENNReal.ofReal (n * s)⁻¹ ∂volume)
            = ∫⁻ s in Set.Ioi (0:ℝ),
                ENNReal.ofReal n⁻¹ * (h (radialMap K s x) * ENNReal.ofReal s⁻¹) ∂volume :=
        setLIntegral_congr_fun measurableSet_Ioi (fun s hs => by
          have hs0 : (0:ℝ) < s := hs
          rw [mul_div_cancel_left₀ s hn.ne', mul_inv_rev,
            ENNReal.ofReal_mul (inv_nonneg.mpr hs0.le)]
          ring)
      rw [hcongr, lintegral_const_mul _ hmeas2]
    have hne0 : ENNReal.ofReal n⁻¹ ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr hn)).ne'
    exact (ENNReal.mul_right_inj hne0 ENNReal.ofReal_ne_top).mp (hIA.symm.trans hIB)
  -- (4) Assemble: collar-form core, then the three rewrites above.
  rw [setLIntegral_cone_eq_collar_radial h hh]
  refine Eq.symm ?_
  calc
    ∫⁻ r in Set.Ioi (0:ℝ),
        (∫⁻ σ in normEqOneSurface K, h (radialMap K r σ) ∂(surfaceMeasure K))
          * ENNReal.ofReal r⁻¹ ∂volume
      = ∫⁻ r in Set.Ioi (0:ℝ),
          (∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
              {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
              h (radialMap K (r / mixedEmbedding.norm x) x)
                ∂(DedekindZeta.mixedMulHaar K)) * ENNReal.ofReal r⁻¹ ∂volume := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
        rw [hinner r (Set.mem_Ioi.mp hr).le]
    _ = ∫⁻ r in Set.Ioi (0:ℝ),
          ∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
              {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
              h (radialMap K (r / mixedEmbedding.norm x) x) * ENNReal.ofReal r⁻¹
                ∂(DedekindZeta.mixedMulHaar K) ∂volume := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
        rw [← lintegral_mul_const (ENNReal.ofReal r⁻¹) (hFmeas r)]
    _ = ∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
            {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
          ∫⁻ r in Set.Ioi (0:ℝ),
              h (radialMap K (r / mixedEmbedding.norm x) x) * ENNReal.ofReal r⁻¹
                ∂volume ∂(DedekindZeta.mixedMulHaar K) :=
        lintegral_lintegral_swap hf_meas.aemeasurable
    _ = ∫⁻ x in (mixedEmbedding.fundamentalCone K ∩
            {x | mixedEmbedding.norm x ∈ Set.Ioc 1 (Real.exp 1)}),
          ∫⁻ t in Set.Ioi (0:ℝ), h (radialMap K t x) * ENNReal.ofReal t⁻¹
                ∂volume ∂(DedekindZeta.mixedMulHaar K) := by
        refine setLIntegral_congr_fun ?_ (fun x hx => ?_)
        · exact (measurableSet_fundamentalCone K).inter
            ((mixedEmbedding.continuous_norm K).measurable measurableSet_Ioc)
        · exact hsub x (lt_trans one_pos (Set.mem_Ioc.mp hx.2).1)
end DedekindZeta.ConeRadialReduction
