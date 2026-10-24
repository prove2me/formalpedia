-- Prove2me | solution 1 for FunctionalInequalities.Probability.Stein.compact_linear_pairing_sq_le_of_source_identity_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:29:59.175953+00:00
-- url     : https://prove2.me/submissions/e7b5e015-dd99-480d-a412-23bddecf8a1c

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

section
open MeasureTheory Filter
open scoped RealInnerProductSpace Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
variable {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {μ : Measure A}
/-- `∫ ⟪a, f⟫ = ⟪a, f⟫_{L²}` for `a, f ∈ L²(μ; E)`. -/
theorem FunctionalInequalities.L2.integral_inner_toLp {a f : A → E} (ha : MemLp a 2 μ) (hf : MemLp f 2 μ) :
    (∫ x, ⟪a x, f x⟫ ∂μ) = ⟪ha.toLp a, hf.toLp f⟫ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ha.coeFn_toLp, hf.coeFn_toLp] with x hax hfx
  rw [hax, hfx]
/-- Cauchy–Schwarz: `|∫ ⟪a, f⟫| ≤ ‖a‖₂ ‖f‖₂`. -/
theorem FunctionalInequalities.L2.abs_integral_inner_le {a f : A → E} (ha : MemLp a 2 μ) (hf : MemLp f 2 μ) :
    |∫ x, ⟪a x, f x⟫ ∂μ| ≤ (eLpNorm a 2 μ).toReal * (eLpNorm f 2 μ).toReal := by
  rw [integral_inner_toLp ha hf]
  simpa only [Lp.norm_toLp] using abs_real_inner_le_norm (ha.toLp a) (hf.toLp f)
/-- `∫ ‖a‖² = ‖a‖₂²` for `a ∈ L²`. -/
theorem FunctionalInequalities.L2.integral_norm_sq_eq_eLpNorm_sq {a : A → E} (ha : MemLp a 2 μ) :
    (∫ x, ‖a x‖ ^ 2 ∂μ) = (eLpNorm a 2 μ).toReal ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq, Lp.norm_toLp] using integral_inner_toLp ha ha
end
end
end

open MeasureTheory Filter
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace Topology ContDiff
section CompactSourceDualBound
open MeasureTheory Filter
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff Topology RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Stein
end FunctionalInequalities.Probability.Stein
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Stein
namespace FunctionalInequalities.Probability.Stein
end FunctionalInequalities.Probability.Stein
open FunctionalInequalities.Probability.Stein in
set_option maxHeartbeats 400000 in
/-- Squared dual bound from a source identity: for a latent L2 field paired with compactly supported smooth tests through a
measurable pushforward onto an actual probability law, the linear pairing squared is bounded by the field's L2 norm
squared times `∫ ‖Dh‖²`. Arbitrary latent measure space; all Euclidean dimensions. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (mu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (Z F : Ω → EuclideanSpace ℝ (Fin n)) (hZ : Measurable Z)
    (hmap : P.map Z = (mu : Measure (EuclideanSpace ℝ (Fin n))))
    (hF : MemLp F 2 P) (v : EuclideanSpace ℝ (Fin n))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h)
    (hid : (∫ x, ⟪x, v⟫ * h x ∂(mu : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ w, ⟪F w, gradient h (Z w)⟫ ∂P) :
    (∫ x, ⟪x, v⟫ * h x ∂(mu : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 ≤
      (∫ w, ‖F w‖ ^ 2 ∂P) *
        ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(mu : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hh1 : ContDiff ℝ 1 h := hh.of_le (WithTop.coe_le_coe.mpr le_top)
  have hgc := FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hh1
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gradient hhc)
  have hg : MemLp (gradient h) 2 (mu : Measure (EuclideanSpace ℝ (Fin n))) :=
    MemLp.of_bound hgc.aestronglyMeasurable C (ae_of_all _ hC)
  have hMP : MeasurePreserving Z P (mu : Measure (EuclideanSpace ℝ (Fin n))) := ⟨hZ, hmap⟩
  have hG := hg.comp_measurePreserving hMP
  have hCS := FunctionalInequalities.L2.abs_integral_inner_le hF hG
  have hEnergy : (∫ w, ‖gradient h (Z w)‖ ^ 2 ∂P) =
      ∫ x, ‖gradient h x‖ ^ 2 ∂(mu : Measure (EuclideanSpace ℝ (Fin n))) := by
    change (∫ w, ‖(gradient h ∘ Z) w‖ ^ 2 ∂P) = _
    rw [FunctionalInequalities.L2.integral_norm_sq_eq_eLpNorm_sq hG,
      FunctionalInequalities.L2.integral_norm_sq_eq_eLpNorm_sq hg,
      eLpNorm_comp_measurePreserving hg.aestronglyMeasurable hMP]
  have hNorm (x : EuclideanSpace ℝ (Fin n)) : ‖gradient h x‖ = ‖fderiv ℝ h x‖ :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.norm_map _
  rw [hid]
  calc
    _ = |∫ w, ⟪F w, gradient h (Z w)⟫ ∂P| ^ 2 := (sq_abs _).symm
    _ ≤ ((eLpNorm F 2 P).toReal * (eLpNorm (gradient h ∘ Z) 2 P).toReal) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)).2 hCS
    _ = (∫ w, ‖F w‖ ^ 2 ∂P) * ∫ w, ‖gradient h (Z w)‖ ^ 2 ∂P := by
      rw [mul_pow, ← FunctionalInequalities.L2.integral_norm_sq_eq_eLpNorm_sq hF,
        ← FunctionalInequalities.L2.integral_norm_sq_eq_eLpNorm_sq hG]
      rfl
    _ = _ := by rw [hEnergy]; simp_rw [hNorm]
