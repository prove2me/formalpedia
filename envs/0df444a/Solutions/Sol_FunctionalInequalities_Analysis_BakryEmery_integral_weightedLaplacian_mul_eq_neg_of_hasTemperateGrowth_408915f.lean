-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:47:34.37615+00:00
-- url     : https://prove2.me/submissions/75308618-143b-4305-8890-a4863268652e

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_abs_laplacian_le_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cutoff_eq_one_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_hasCompactSupport_cutoff_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_of_norm_le_pow_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_weightedLaplacian_mul_eq_neg_of_hasCompactSupport_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_norm_iteratedFDeriv_cutoff_le_408915f

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
section DifferentialTools
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gradient
variable [CompleteSpace E]
/-- Product rule for the gradient. -/
theorem FunctionalInequalities.Analysis.BakryEmery.gradient_mul {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y * g y) x = f x • gradient g x + g x • gradient f x := by
  unfold gradient
  rw [fderiv_fun_mul hf hg, map_add, map_smulₛₗ, map_smulₛₗ]
  simp
end Gradient
end DifferentialTools
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem FunctionalInequalities.Analysis.BakryEmery.contDiff_cutoff (R : ℝ) : ContDiff ℝ ∞ (cutoff (E := E) R) := by
    change ContDiff ℝ ∞
      (fun x : E => (unitBump : ContDiffBump (0 : E)) (R⁻¹ • x))
    exact unitBump.contDiff.comp (contDiff_const_smul R⁻¹)
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem FunctionalInequalities.Analysis.BakryEmery.abs_cutoff_le_one (R : ℝ) (x : E) : |cutoff R x| ≤ 1 := by
    change |(unitBump : ContDiffBump (0 : E)) (R⁻¹ • x)| ≤ 1
    have hnonneg :
        0 ≤ (unitBump : ContDiffBump (0 : E)) (R⁻¹ • x) :=
      ContDiffBump.nonneg (unitBump : ContDiffBump (0 : E))
    have hle :
        (unitBump : ContDiffBump (0 : E)) (R⁻¹ • x) ≤ 1 :=
      ContDiffBump.le_one (unitBump : ContDiffBump (0 : E))
    exact abs_le.2 ⟨by linarith, hle⟩
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `‖∇g(x)‖ = ‖∇¹g(x)‖`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.norm_gradient_eq_norm_iteratedFDeriv_one (g : E → ℝ) (x : E) :
    ‖gradient g x‖ = ‖iteratedFDeriv ℝ 1 g x‖ := by
    rw [gradient, (InnerProductSpace.toDual ℝ E).symm.norm_map,
      norm_iteratedFDeriv_one]
variable (m : Measure E) [m.IsAddHaarMeasure]
end
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : Measure E) [m.IsAddHaarMeasure]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Analysis.BakryEmery.ibp_temperate_bounds {f : E → ℝ} (hf : f.HasTemperateGrowth) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ x,
      |f x| ≤ C * (1 + ‖x‖) ^ k ∧
      ‖gradient f x‖ ≤ C * (1 + ‖x‖) ^ k ∧
      ‖iteratedFDeriv ℝ 2 f x‖ ≤ C * (1 + ‖x‖) ^ k := by
  obtain ⟨k, C, hC, hb⟩ := hf.norm_iteratedFDeriv_le_uniform 2
  refine ⟨k, C, hC, fun x => ⟨?_, ?_, hb 2 le_rfl x⟩⟩
  · simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hb 0 (by omega) x
  · simpa only [norm_gradient_eq_norm_iteratedFDeriv_one] using hb 1 (by omega) x
omit [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Analysis.BakryEmery.ibp_weightedLaplacian_bound {V f : E → ℝ}
    {CV C : ℝ} {kV k : ℕ} (hCV : 0 ≤ CV) (hC : 0 ≤ C)
    (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hf : ∀ x, ‖gradient f x‖ ≤ C * (1 + ‖x‖) ^ k ∧
      ‖iteratedFDeriv ℝ 2 f x‖ ≤ C * (1 + ‖x‖) ^ k) (x : E) :
    |weightedLaplacian V f x| ≤
      ((Module.finrank ℝ E : ℝ) * C + CV * C) * (1 + ‖x‖) ^ (k + kV) := by
  have hp : 1 ≤ (1 + ‖x‖) ^ kV := one_le_pow₀ (by linarith [norm_nonneg x])
  calc
    |weightedLaplacian V f x| ≤
        (Module.finrank ℝ E : ℝ) * ‖iteratedFDeriv ℝ 2 f x‖ +
          ‖gradient V x‖ * ‖gradient f x‖ := by
      rw [weightedLaplacian_apply]
      exact (abs_sub _ _).trans (add_le_add (abs_laplacian_le_408915f f x)
        (abs_real_inner_le_norm _ _))
    _ ≤ (Module.finrank ℝ E : ℝ) * (C * (1 + ‖x‖) ^ k) +
          (CV * (1 + ‖x‖) ^ kV) * (C * (1 + ‖x‖) ^ k) := by
      gcongr
      · exact (hf x).2
      · exact hVg x
      · exact (hf x).1
    _ ≤ (Module.finrank ℝ E : ℝ) * (C * (1 + ‖x‖) ^ k) *
          (1 + ‖x‖) ^ kV +
          (CV * (1 + ‖x‖) ^ kV) * (C * (1 + ‖x‖) ^ k) := by
      have hm : (Module.finrank ℝ E : ℝ) * (C * (1 + ‖x‖) ^ k) ≤
          (Module.finrank ℝ E : ℝ) * (C * (1 + ‖x‖) ^ k) * (1 + ‖x‖) ^ kV :=
        le_mul_of_one_le_right (by positivity) hp
      exact add_le_add_left hm _
    _ = _ := by rw [pow_add]; ring
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- **BKL (15)**, first equality, for `u, v ∈ 𝒜`: `∫ (ℒu) v dμ = -∫ ⟪∇u, ∇v⟫ dμ`. -/
theorem solution {V f g : E → ℝ}
    (hV : ContDiff ℝ 1 V) {CV : ℝ} {kV : ℕ} (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
    ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x * g x ∂(m.tilted (-V)) =
      -∫ x, ⟪gradient f x, gradient g x⟫ ∂(m.tilted (-V)) := by
  obtain ⟨kf, Cf, hCf, hfb⟩ := ibp_temperate_bounds hf
  obtain ⟨kg, Cg, hCg, hgb⟩ := ibp_temperate_bounds hg
  have hf2 : ContDiff ℝ 2 f := hf.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg2 : ContDiff ℝ 2 g := hg.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hCV : 0 ≤ CV := by
    have h := hVg 0
    simp only [norm_zero, add_zero, one_pow, mul_one] at h
    exact (norm_nonneg _).trans h
  obtain ⟨K₀, hK₀⟩ := FunctionalInequalities.Analysis.BakryEmery.norm_iteratedFDeriv_cutoff_le_408915f (E := E) 1
  let K : ℝ := max K₀ 0
  have hK : 0 ≤ K := le_max_right _ _
  have hcut (n : ℕ) (x : E) : ‖gradient (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1)) x‖ ≤ K := by
    rw [FunctionalInequalities.Analysis.BakryEmery.norm_gradient_eq_norm_iteratedFDeriv_one]
    exact (hK₀ _ (by linarith [Nat.cast_nonneg (α := ℝ) n]) x).trans (le_max_left _ _)
  let w : ℕ → E → ℝ := fun n x => FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1) x * g x
  have hw (n : ℕ) : ContDiff ℝ 2 (w n) :=
    ((FunctionalInequalities.Analysis.BakryEmery.contDiff_cutoff ((n : ℝ) + 1)).of_le (WithTop.coe_le_coe.mpr le_top)).mul hg2
  let A : ℝ := (Module.finrank ℝ E : ℝ) * Cf + CV * Cf
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hLf (x : E) : |FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x| ≤ A * (1 + ‖x‖) ^ (kf + kV) :=
    ibp_weightedLaplacian_bound hCV hCf hVg (fun x => (hfb x).2) x
  have hwb (n : ℕ) (x : E) : |w n x| ≤ Cg * (1 + ‖x‖) ^ kg := by
    dsimp only [w]
    rw [abs_mul]
    calc
      _ ≤ 1 * (Cg * (1 + ‖x‖) ^ kg) := by
        gcongr
        · exact FunctionalInequalities.Analysis.BakryEmery.abs_cutoff_le_one _ _
        · exact (hgb x).1
      _ = _ := one_mul _
  have hgw (n : ℕ) (x : E) :
      ‖gradient (w n) x‖ ≤ (Cg + Cg * K) * (1 + ‖x‖) ^ kg := by
    have hc : ContDiff ℝ 2 (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1) : E → ℝ) :=
      (FunctionalInequalities.Analysis.BakryEmery.contDiff_cutoff _).of_le (WithTop.coe_le_coe.mpr le_top)
    dsimp only [w]
    rw [FunctionalInequalities.Analysis.BakryEmery.gradient_mul (hc.differentiable (by norm_num) x)
      (hg2.differentiable (by norm_num) x)]
    calc
      _ ≤ ‖FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1) x • gradient g x‖ +
          ‖g x • gradient (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1)) x‖ := norm_add_le _ _
      _ = |FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1) x| * ‖gradient g x‖ +
          |g x| * ‖gradient (FunctionalInequalities.Analysis.BakryEmery.cutoff ((n : ℝ) + 1)) x‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * (Cg * (1 + ‖x‖) ^ kg) + (Cg * (1 + ‖x‖) ^ kg) * K := by
        gcongr
        · exact FunctionalInequalities.Analysis.BakryEmery.abs_cutoff_le_one _ _
        · exact (hgb x).2.1
        · exact (hgb x).1
        · exact hcut n x
      _ = _ := by ring
  let F : ℕ → E → ℝ := fun n x => FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x * w n x
  let G : ℕ → E → ℝ := fun n x => ⟪gradient f x, gradient (w n) x⟫
  have hFbound (n : ℕ) (x : E) :
      ‖F n x‖ ≤ (A * Cg) * (1 + ‖x‖) ^ (kf + kV + kg) := by
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ (A * (1 + ‖x‖) ^ (kf + kV)) * (Cg * (1 + ‖x‖) ^ kg) := by
        gcongr
        · exact hLf x
        · exact hwb n x
      _ = _ := by rw [pow_add]; ring
  have hGbound (n : ℕ) (x : E) :
      ‖G n x‖ ≤ (Cf * (Cg + Cg * K)) * (1 + ‖x‖) ^ (kf + kg) := by
    dsimp only [G]
    rw [Real.norm_eq_abs]
    calc
      _ ≤ ‖gradient f x‖ * ‖gradient (w n) x‖ := abs_real_inner_le_norm _ _
      _ ≤ (Cf * (1 + ‖x‖) ^ kf) * ((Cg + Cg * K) * (1 + ‖x‖) ^ kg) := by
        gcongr
        · exact (hfb x).2.1
        · exact hgw n x
      _ = _ := by rw [pow_add]; ring
  have hFi : Integrable (fun x : E => (A * Cg) * (1 + ‖x‖) ^ (kf + kV + kg))
      (m.tilted (-V)) := by
    apply FunctionalInequalities.Analysis.BakryEmery.integrable_of_norm_le_pow_408915f _ hexp (by fun_prop) (C := A * Cg) (k := kf + kV + kg)
    intro x
    rw [Real.norm_of_nonneg (by positivity)]
  have hGi : Integrable (fun x : E => (Cf * (Cg + Cg * K)) * (1 + ‖x‖) ^ (kf + kg))
      (m.tilted (-V)) := by
    apply FunctionalInequalities.Analysis.BakryEmery.integrable_of_norm_le_pow_408915f _ hexp (by fun_prop)
      (C := Cf * (Cg + Cg * K)) (k := kf + kg)
    intro x
    rw [Real.norm_of_nonneg (by positivity)]
  have hlocal (x : E) : ∀ᶠ n : ℕ in atTop, w n =ᶠ[𝓝 x] g := by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hx : ‖x‖ < (n : ℝ) + 1 := by linarith
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    dsimp only [w]
    rw [FunctionalInequalities.Analysis.BakryEmery.cutoff_eq_one_408915f (by positivity) hy.le, one_mul]
  have hFlim (x : E) :
      Tendsto (fun n => F n x) atTop (𝓝 (FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x * g x)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hlocal x] with n hn
    dsimp only [F]
    rw [hn.eq_of_nhds]
  have hGlim (x : E) :
      Tendsto (fun n => G n x) atTop (𝓝 ⟪gradient f x, gradient g x⟫) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hlocal x] with n hn
    dsimp only [G]
    rw [hn.gradient_eq]
  have hFt := tendsto_integral_of_dominated_convergence
    (fun x : E => (A * Cg) * (1 + ‖x‖) ^ (kf + kV + kg))
    (fun n => ((FunctionalInequalities.Analysis.BakryEmery.continuous_weightedLaplacian hV hf2).mul (hw n).continuous).aestronglyMeasurable)
    hFi (fun n => ae_of_all _ (hFbound n)) (ae_of_all _ hFlim)
  have hGt := tendsto_integral_of_dominated_convergence
    (fun x : E => (Cf * (Cg + Cg * K)) * (1 + ‖x‖) ^ (kf + kg))
    (fun n => ((FunctionalInequalities.Analysis.BakryEmery.continuous_gradient (hf2.of_le (by norm_num))).inner
      (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient ((hw n).of_le (by norm_num)))).aestronglyMeasurable)
    hGi (fun n => ae_of_all _ (hGbound n)) (ae_of_all _ hGlim)
  have hIBP (n : ℕ) : (∫ x, F n x ∂(m.tilted (-V))) =
      -(∫ x, G n x ∂(m.tilted (-V))) :=
    FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasCompactSupport_408915f m hV hf2 (hw n)
      ((FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_cutoff_408915f (by positivity)).mul_right)
  have hneg := hGt.neg
  simp_rw [← hIBP] at hneg
  exact tendsto_nhds_unique hFt hneg
