-- Prove2me | solution 1 for FunctionalInequalities.Probability.zero_mem_interior_convexHull_support_of_integral_eq_zero_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:26:24.554578+00:00
-- url     : https://prove2.me/submissions/42fb3a8f-70b5-43c9-9a01-20cd88e9472e

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Order.Compact

open MeasureTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
open MeasureTheory
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities.Probability in
/-- The origin is interior to the convex hull of the support of a nonzero finite measure with finite first moment and
zero barycenter that is not concentrated on any proper linear subspace. -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hint : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    (0 : E) ∈ interior (convexHull ℝ μ.support) := by
  classical
  let : NeZero μ := ⟨hμ⟩
  have hmass : 0 < μ.real Set.univ := measureReal_univ_pos
  have hzero (L : E →L[ℝ] ℝ) : (∫ x, L x ∂μ) = 0 := by
    simpa only [hbar, map_zero] using L.integral_comp_comm hint
  have hker (L : E →L[ℝ] ℝ) (hz : ∀ᵐ x ∂μ, L x = 0) : L = 0 := by
    have hk : μ (L.toLinearMap.ker : Set E)ᶜ = 0 := by
      change μ {x | ¬ L x = 0} = 0
      exact ae_iff.mp hz
    have ht : L.toLinearMap.ker = ⊤ := hsub _ hk
    have hl : L.toLinearMap = 0 := LinearMap.ker_eq_top.mp ht
    ext x
    exact congrArg (fun f : E →ₗ[ℝ] ℝ => f x) hl
  have hspan : affineSpan ℝ μ.support = ⊤ := by
    obtain ⟨p, hp⟩ := μ.nonempty_support hμ
    let A := affineSpan ℝ μ.support
    have hpA : p ∈ A := mem_affineSpan ℝ hp
    by_contra hA
    have hdir : A.direction ≠ ⊤ := by
      intro hd
      exact hA ((AffineSubspace.direction_eq_top_iff_of_nonempty ⟨p, hpA⟩).mp hd)
    obtain ⟨g, hg, hgd⟩ := A.direction.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hdir)
    let L : E →L[ℝ] ℝ := g.toContinuousLinearMap
    have hconstant (x : E) (hx : x ∈ μ.support) : L x = L p := by
      have hd := A.vsub_mem_direction (mem_affineSpan ℝ hx) hpA
      have hk : g (x - p) = 0 := hgd hd
      change g x = g p
      exact sub_eq_zero.mp (by simpa only [map_sub] using hk)
    have hae : (fun x => L x) =ᵐ[μ] (fun _ => L p) := by
      filter_upwards [μ.support_mem_ae] with x hx
      exact hconstant x hx
    have hpzero : L p = 0 := by
      have hm : μ.real Set.univ * L p = 0 := by
        calc
          μ.real Set.univ * L p = ∫ _ : E, L p ∂μ := by simp only [integral_const, smul_eq_mul]
          _ = ∫ x, L x ∂μ := (integral_congr_ae hae).symm
          _ = 0 := hzero L
      exact (mul_eq_zero.mp hm).resolve_left hmass.ne'
    have hl : L = 0 := hker L (by filter_upwards [hae] with x hx; exact hx.trans hpzero)
    apply hg
    ext x
    exact congrArg (fun f : E →L[ℝ] ℝ => f x) hl
  have hinterior : (interior (convexHull ℝ μ.support)).Nonempty :=
    interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan
  by_contra hnot
  obtain ⟨L, hL, hle⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point (convex_convexHull ℝ μ.support) hnot hinterior
  have hnonpos : ∀ᵐ x ∂μ, L x ≤ 0 := by
    filter_upwards [μ.support_mem_ae] with x hx
    simpa only [map_zero] using hle x (subset_convexHull ℝ μ.support hx)
  have hi : Integrable (fun x => -L x) μ := (L.integrable_comp hint).neg
  have hn : 0 ≤ᵐ[μ] (fun x => -L x) := by
    filter_upwards [hnonpos] with x hx
    exact neg_nonneg.mpr hx
  have hnint : (∫ x, -L x ∂μ) = 0 := by rw [integral_neg, hzero L, neg_zero]
  have hnzero := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hnint
  have hz : ∀ᵐ x ∂μ, L x = 0 := by
    filter_upwards [hnzero] with x hx
    exact neg_eq_zero.mp hx
  exact hL (hker L hz)
