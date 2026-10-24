-- Prove2me | solution 1 for FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_of_memLp_two_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:58:12.2098+00:00
-- url     : https://prove2.me/submissions/7a2ebb8b-3581-43ee-a6a2-9dcacf45d67b

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_FunctionalInequalities_Analysis_Mollification_lintegral_enorm_convolution_sq_le_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Mollification_tendsto_eLpNorm_convolution_sub_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_fderiv_convolution_eq_of_hasWeakDerivAlong_408915f

section
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
/-- The mollification of an `L²` function is again `L²`. -/
theorem FunctionalInequalities.Analysis.Mollification.memLp_convolution {f : V → E} (hf : MemLp f 2 m) :
    MemLp (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) 2 m :=
  ⟨(continuous_convolution φ (hf.locallyIntegrable one_le_two)).aestronglyMeasurable,
    (eLpNorm_convolution_le φ hf.1).trans_lt hf.2⟩
end Contraction
end
end
end
end
end

noncomputable section
open MeasureTheory
open scoped ContDiff
section WeakProducts
open MeasureTheory Filter Set Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
private lemma FunctionalInequalities.Analysis.tendsto_integral_mul_of_l2
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a b : X → ℝ} {u : ℕ → X → ℝ}
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (hu : ∀ m, MemLp (u m) 2 μ)
    (hconv : Tendsto (fun m => eLpNorm (u m - b) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ x, a x * u m x ∂μ) atTop
      (𝓝 (∫ x, a x * b x ∂μ)) := by
  have hp {z : X → ℝ} (hz : MemLp z 2 μ) :
      inner ℝ (ha.toLp a) (hz.toLp z) = ∫ x, a x * z x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hz.coeFn_toLp] with x hx hz'
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hx, hz']
    exact mul_comm _ _
  have ht :
      Tendsto (fun m => (hu m).toLp (u m)) atTop (𝓝 (hb.toLp b)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' u hu b hb).2 hconv
  have hi :
      Tendsto (fun m => inner ℝ (ha.toLp a) ((hu m).toLp (u m)))
        atTop (𝓝 (inner ℝ (ha.toLp a) (hb.toLp b))) :=
    tendsto_const_nhds.inner ht
  simpa only [hp] using hi
namespace FunctionalInequalities.Analysis.HasWeakDerivAlong
end FunctionalInequalities.Analysis.HasWeakDerivAlong
open FunctionalInequalities.Analysis.HasWeakDerivAlong in
set_option maxHeartbeats 800000 in
/-- Scalar weak product rule: global L2 factors and directional derivatives
produce a locally integrable product and its actual weak derivative. -/
theorem solution {n : ℕ}
    {f df g dg : EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : FunctionalInequalities.Analysis.HasWeakDerivAlong f df v) (hg : FunctionalInequalities.Analysis.HasWeakDerivAlong g dg v)
    (hf2 : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf2 : MemLp df 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg2 : MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdg2 : MemLp dg 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => f x * g x)
      (fun x => df x * g x + f x * dg x) v := by
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun m =>
    { rIn := (1 / ((m : ℝ) + 1)) / 2
      rOut := 1 / ((m : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have hr : 0 < 1 / ((m : ℝ) + 1) := by positivity
        linarith }
  have hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0) := by
    change Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  let gm : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m =>
    (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
  let dgm : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m =>
    (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] dg
  have hgm2 (m : ℕ) :
      MemLp (gm m) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    FunctionalInequalities.Analysis.Mollification.memLp_convolution (φ m) hg2
  have hdgm2 (m : ℕ) :
      MemLp (dgm m) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    FunctionalInequalities.Analysis.Mollification.memLp_convolution (φ m) hdg2
  have hgmconv :
      Tendsto (fun m => eLpNorm (gm m - g) 2 volume) atTop (𝓝 0) :=
    FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub_408915f hφ hg2
  have hdgmconv :
      Tendsto (fun m => eLpNorm (dgm m - dg) 2 volume) atTop (𝓝 0) :=
    FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub_408915f hφ hdg2
  have hgmC (m : ℕ) : ContDiff ℝ 1 (gm m) :=
    ((φ m).hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) ((φ m).contDiff_normed (n := 1)) hg.1
  have hgmder (m : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (gm m) x v = dgm m x :=
    FunctionalInequalities.Analysis.fderiv_convolution_eq_of_hasWeakDerivAlong_408915f hg (φ m) x
  refine ⟨(hf2.integrable_mul hg2).locallyIntegrable,
    ((hdf2.integrable_mul hg2).add (hf2.integrable_mul hdg2)).locallyIntegrable, ?_⟩
  intro ψ hψ hψc
  have hψd : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hψdc : HasCompactSupport (fun x => fderiv ℝ ψ x v) := by
    change HasCompactSupport ((fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) ∘
      fderiv ℝ ψ)
    exact (hψc.fderiv ℝ).comp_left (by simp)
  have hψtop : MemLp ψ (⊤ : ℝ≥0∞)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hψ.continuous.memLp_of_hasCompactSupport hψc
  have hψdtop : MemLp (fun x => fderiv ℝ ψ x v) (⊤ : ℝ≥0∞)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hψd.memLp_of_hasCompactSupport hψdc
  let a : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f x * fderiv ℝ ψ x v
  let b : EuclideanSpace ℝ (Fin n) → ℝ := fun x => df x * ψ x
  let c : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f x * ψ x
  have ha : MemLp a 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hψdtop.mul' hf2
  have hb : MemLp b 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hψtop.mul' hdf2
  have hc : MemLp c 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hψtop.mul' hf2
  have hid (m : ℕ) :
      (∫ x, a x * gm m x) + (∫ x, c x * dgm m x) =
        -(∫ x, b x * gm m x) := by
    have hder (x : EuclideanSpace ℝ (Fin n)) :
        fderiv ℝ (fun y => ψ y * gm m y) x v =
          ψ x * dgm m x + gm m x * fderiv ℝ ψ x v := by
      change (fderiv ℝ (ψ * gm m) x) v = _
      rw [fderiv_mul
        ((hψ.differentiable one_ne_zero).differentiableAt)
        (((hgmC m).differentiable one_ne_zero).differentiableAt)]
      simp only [add_apply, smul_apply, smul_eq_mul, hgmder]
    have hw := hf.2.2 (fun x => ψ x * gm m x)
      (hψ.mul (hgmC m)) hψc.mul_right
    calc
      (∫ x, a x * gm m x) + (∫ x, c x * dgm m x) =
          ∫ x, a x * gm m x + c x * dgm m x :=
        (integral_add (ha.integrable_mul (hgm2 m))
          (hc.integrable_mul (hdgm2 m))).symm
      _ = ∫ x, f x * fderiv ℝ (fun y => ψ y * gm m y) x v := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change a x * gm m x + c x * dgm m x =
            f x * fderiv ℝ (fun y => ψ y * gm m y) x v
          rw [hder]
          dsimp only [a, c]
          ring
      _ = -(∫ x, df x * (ψ x * gm m x)) := hw
      _ = -(∫ x, b x * gm m x) := by
        apply congrArg Neg.neg
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          dsimp only [b]
          ring
  have hA := tendsto_integral_mul_of_l2 ha hg2 hgm2 hgmconv
  have hB := tendsto_integral_mul_of_l2 hb hg2 hgm2 hgmconv
  have hC := tendsto_integral_mul_of_l2 hc hdg2 hdgm2 hdgmconv
  have hlim :
      (∫ x, a x * g x) + (∫ x, c x * dg x) =
        -(∫ x, b x * g x) :=
    tendsto_nhds_unique (hA.add hC)
      (Filter.Tendsto.congr (fun m => (hid m).symm) hB.neg)
  have hleft :
      (∫ x, (f x * g x) * fderiv ℝ ψ x v) = ∫ x, a x * g x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [a]
      ring
  have hright :
      (∫ x, (df x * g x + f x * dg x) * ψ x) =
        (∫ x, b x * g x) + (∫ x, c x * dg x) := by
    calc
      (∫ x, (df x * g x + f x * dg x) * ψ x) =
          ∫ x, b x * g x + c x * dg x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          dsimp only [b, c]
          ring
      _ = (∫ x, b x * g x) + (∫ x, c x * dg x) :=
        integral_add (hb.integrable_mul hg2) (hc.integrable_mul hdg2)
  rw [hleft, hright]
  linarith
