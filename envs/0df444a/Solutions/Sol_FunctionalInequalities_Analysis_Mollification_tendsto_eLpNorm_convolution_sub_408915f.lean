-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:57:08.450825+00:00
-- url     : https://prove2.me/submissions/34b8ed0a-9417-45e8-a2b0-dad9c83ee926

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Theorems.Thm_FunctionalInequalities_Analysis_Mollification_lintegral_enorm_convolution_sq_le_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Mollification_tendsto_eLpNorm_convolution_sub_of_continuous_408915f

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Mollification
end FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : Measure V} [m.IsAddHaarMeasure]
section Contraction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (φ : ContDiffBump (0 : V))
/-- `L²` contraction of the mollifier in `eLpNorm` form. -/
theorem FunctionalInequalities.Analysis.Mollification.eLpNorm_convolution_le {f : V → E} (hf : AEStronglyMeasurable f m) :
    eLpNorm (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) 2 m ≤ eLpNorm f 2 m := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact ENNReal.rpow_le_rpow (lintegral_enorm_convolution_sq_le_408915f φ hf) (by norm_num)
/-- The mollification of a locally integrable function is continuous. -/
theorem FunctionalInequalities.Analysis.Mollification.continuous_convolution {f : V → E} (hf : LocallyIntegrable f m) :
    Continuous (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) :=
  HasCompactSupport.continuous_convolution_left _ (φ.hasCompactSupport_normed (μ := m))
    φ.continuous_normed hf
/-- The mollifier is linear on locally integrable functions. -/
theorem FunctionalInequalities.Analysis.Mollification.convolution_sub {f g : V → E} (hf : LocallyIntegrable f m) (hg : LocallyIntegrable g m) :
    φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] (f - g) =
      φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f -
        φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g := by
  funext x
  have h1 := HasCompactSupport.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.hasCompactSupport_normed (μ := m)) φ.continuous_normed hf x
  have h2 := HasCompactSupport.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.hasCompactSupport_normed (μ := m)) φ.continuous_normed hg x
  simp only [Pi.sub_apply, convolution_def, ContinuousLinearMap.lsmul_apply, smul_sub]
  exact integral_sub h1 h2
end Contraction
section Convergence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
namespace FunctionalInequalities.Analysis.Mollification
end FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities.Analysis.Mollification in
/-- **Mollifications of an `L²` function converge in `L²`** as the radius of the bump tends to
zero: the contraction property reduces the statement to the continuous compactly supported case,
which is dense. -/
theorem solution {φ : ℕ → ContDiffBump (0 : V)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) {f : V → E} (hf : MemLp f 2 m) :
    Tendsto (fun n => eLpNorm ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) 2 m)
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top).ne'
  obtain ⟨g, hgc, hfg, hg, hgL⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le ENNReal.ofNat_ne_top hε3
  have hloc_f : LocallyIntegrable f m := hf.locallyIntegrable one_le_two
  have hloc_g : LocallyIntegrable g m := hgL.locallyIntegrable one_le_two
  have hg3 := (FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub_of_continuous_408915f (m := m) hφ hg hgc).eventually
    (ge_mem_nhds (pos_iff_ne_zero.mpr hε3))
  filter_upwards [hg3] with n hn
  have hsplit : (φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f =
      ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] (f - g) +
        ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g - g)) + (g - f) := by
    rw [FunctionalInequalities.Analysis.Mollification.convolution_sub (φ n) hloc_f hloc_g]
    abel
  have hm1 : AEStronglyMeasurable ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] (f - g)) m :=
    (FunctionalInequalities.Analysis.Mollification.continuous_convolution (φ n) (hloc_f.sub hloc_g)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g - g) m :=
    ((FunctionalInequalities.Analysis.Mollification.continuous_convolution (φ n) hloc_g).sub hg).aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (g - f) m := hg.aestronglyMeasurable.sub hf.1
  calc eLpNorm ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) 2 m
      ≤ eLpNorm ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] (f - g)) 2 m +
          eLpNorm ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g - g) 2 m +
          eLpNorm (g - f) 2 m := by
        rw [hsplit]
        exact (eLpNorm_add_le (hm1.add hm2) hm3 one_le_two).trans
          (add_le_add_left (eLpNorm_add_le hm1 hm2 one_le_two) _)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact (FunctionalInequalities.Analysis.Mollification.eLpNorm_convolution_le (φ n) (hf.1.sub hg.aestronglyMeasurable)).trans hfg
        · rw [eLpNorm_sub_comm]; exact hfg
    _ = ε := ENNReal.add_thirds ε
