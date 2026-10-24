-- Prove2me | solution 1 for FunctionalInequalities.Analysis.subgradient_expansion_of_hasFDerivAt_resolvent_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:01:58.501621+00:00
-- url     : https://prove2.me/submissions/eb4e752e-d42b-4a6f-aaf5-5623669780b6

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_resolvent_preimage_near_408915f

noncomputable section
open Set Filter
open scoped RealInnerProductSpace Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.resolvent_subgradient_monotone {f : E → ℝ} {u v p q : E}
    (hp : ∀ w, f u + ⟪p, w - u⟫ ≤ f w)
    (hq : ∀ w, f v + ⟪q, w - v⟫ ≤ f w) :
    0 ≤ ⟪p - q, u - v⟫ := by
  have h₁ := hp v
  have h₂ := hq u
  have he : ⟪p, v - u⟫ + ⟪q, u - v⟫ = -⟪p - q, u - v⟫ := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  linarith
private lemma FunctionalInequalities.Analysis.resolvent_firm_monotone {f : E → ℝ} {P : E → E}
    (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) (a b : E) :
    ‖P a - P b‖ ^ 2 ≤ ⟪P a - P b, a - b⟫ := by
  have h := resolvent_subgradient_monotone (hP a) (hP b)
  have he :
      ⟪(a - P a) - (b - P b), P a - P b⟫ =
        ⟪P a - P b, a - b⟫ - ‖P a - P b‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    rw [real_inner_comm a (P a), real_inner_comm a (P b),
      real_inner_comm b (P a), real_inner_comm b (P b)]
    ring
  rw [he] at h
  linarith
private lemma FunctionalInequalities.Analysis.resolvent_subgradient_inverse {f : E → ℝ} {P : E → E}
    (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y)
    {y q : E} (hq : ∀ w, f y + ⟪q, w - y⟫ ≤ f w) :
    P (y + q) = y := by
  have h := resolvent_subgradient_monotone (hP (y + q)) hq
  have he : (y + q - P (y + q)) - q = -(P (y + q) - y) := by
    abel
  rw [he, inner_neg_left, real_inner_self_eq_norm_sq] at h
  have hn : ‖P (y + q) - y‖ = 0 := by
    nlinarith [norm_nonneg (P (y + q) - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)
private lemma FunctionalInequalities.Analysis.resolvent_absorb_remainder (T : E ≃L[ℝ] E) {K c : ℝ}
    (hK : 0 < K) (hnorm : ‖(T.symm : E →L[ℝ] E)‖ ≤ K)
    (hc : K * c = 1 / 2) (d u : E)
    (hr : ‖u - T d‖ ≤ c * ‖d‖) :
    ‖d‖ ≤ 2 * K * ‖u‖ := by
  have hop := (T.symm : E →L[ℝ] E).le_opNorm (T d)
  simp only [ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply] at hop
  have ht := norm_sub_norm_le (T d) u
  rw [norm_sub_rev] at ht
  have hb : ‖d‖ ≤ K * (‖u‖ + ‖u - T d‖) :=
    hop.trans
      ((mul_le_mul_of_nonneg_right hnorm (norm_nonneg (T d))).trans
        (mul_le_mul_of_nonneg_left (by linarith only [ht]) hK.le))
  have hm := mul_le_mul_of_nonneg_left hr hK.le
  have he : K * (c * ‖d‖) = ‖d‖ / 2 := by
    rw [← mul_assoc, hc]
    ring
  rw [he] at hm
  nlinarith only [hb, hm]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
set_option maxHeartbeats 800000 in
/-- **Inverting the resolvent at a point of invertible differentiability** (weak Letwin route,
Alexandrov's theorem): let `P` be the resolvent of `f` (`z − P z` is a subgradient of `f` at
`P z` for every `z`). If `P` is differentiable at `z` with invertible derivative `T`, then `p₀ := z − P z` is
the only subgradient of `f` at `x := P z`, and every subgradient `q` of `f` at `y` near `x` satisfies
`‖q − p₀ − (T⁻¹ (y − x) − (y − x))‖ ≤ ε ‖y − x‖`. -/
theorem solution {f : E → ℝ} {P : E → E}
    (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) {z : E} {T : E ≃L[ℝ] E}
    (hT : HasFDerivAt P (T : E →L[ℝ] E) z) :
    (∀ q : E, (∀ y, f (P z) + ⟪q, y - P z⟫ ≤ f y) → q = z - P z) ∧
    ∀ ε > 0, ∀ᶠ y in 𝓝 (P z), ∀ q : E, (∀ w, f y + ⟪q, w - y⟫ ≤ f w) →
      ‖q - (z - P z) - (T.symm (y - P z) - (y - P z))‖ ≤ ε * ‖y - P z‖ := by
  -- Adding one also covers the zero-dimensional case without a case split.
  let K : ℝ := ‖(T.symm : E →L[ℝ] E)‖ + 1
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hnorm : ‖(T.symm : E →L[ℝ] E)‖ ≤ K := by
    dsimp [K]
    linarith
  let c : ℝ := 1 / (2 * K)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hKc : K * c = 1 / 2 := by
    dsimp [c]
    field_simp
  have hexp :
      ∀ ε > 0, ∀ᶠ y in 𝓝 (P z), ∀ q : E,
        (∀ w, f y + ⟪q, w - y⟫ ≤ f w) →
          ‖q - (z - P z) - (T.symm (y - P z) - (y - P z))‖
            ≤ ε * ‖y - P z‖ := by
    intro ε hε
    let η : ℝ := min c (ε / (2 * K ^ 2))
    have hη : 0 < η := lt_min hc (by positivity)
    have hηc : η ≤ c := min_le_left _ _
    have hηε : 2 * K ^ 2 * η ≤ ε := by
      have h := (le_div_iff₀ (by positivity : 0 < 2 * K ^ 2)).mp
        (min_le_right c (ε / (2 * K ^ 2)))
      nlinarith only [h]
    obtain ⟨δ, hδ, hd⟩ :=
      Metric.eventually_nhds_iff.mp (hT.isLittleO.def hη)
    have hr (w : E) (hw : ‖w - z‖ < δ) :
        ‖P w - P z - T (w - z)‖ ≤ η * ‖w - z‖ :=
      hd (by
        rw [dist_eq_norm]
        exact hw)
    have hlocal (w : E) (hw : ‖w - z‖ < δ) :
        ‖w - z‖ ≤ 2 * K * ‖P w - P z‖ :=
      resolvent_absorb_remainder T hK hnorm hKc (w - z) (P w - P z)
        ((hr w hw).trans (mul_le_mul_of_nonneg_right hηc (norm_nonneg _)))
    have hl (w : E) (hw : ‖w - z‖ < δ) :
        c * ‖w - z‖ ≤ ‖P w - P z‖ := by
      have hm := mul_le_mul_of_nonneg_left (hlocal w hw) hc.le
      have he : c * (2 * K * ‖P w - P z‖) = ‖P w - P z‖ := by
        calc
          c * (2 * K * ‖P w - P z‖) =
              (2 * (K * c)) * ‖P w - P z‖ := by ring
          _ = ‖P w - P z‖ := by rw [hKc]; ring
      rw [he] at hm
      exact hm
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨c ^ 2 * δ / 2, by positivity, ?_⟩
    intro y hy q hq
    rw [dist_eq_norm] at hy
    have hinv : P (y + q) = y := resolvent_subgradient_inverse hP hq
    have hnear : ‖y + q - z‖ < δ :=
      FunctionalInequalities.Analysis.resolvent_preimage_near_408915f (resolvent_firm_monotone hP) hc hδ hl (y + q)
        (by simpa only [hinv] using hy)
    have hR : ‖y - P z - T (y + q - z)‖ ≤ η * ‖y + q - z‖ := by
      simpa only [hinv] using hr (y + q) hnear
    have hD : ‖y + q - z‖ ≤ 2 * K * ‖y - P z‖ := by
      simpa only [hinv] using hlocal (y + q) hnear
    have he :
        T.symm (y - P z - T (y + q - z)) =
          T.symm (y - P z) - (y + q - z) := by
      rw [map_sub, T.symm_apply_apply]
    have hA :
        ‖(y + q - z) - T.symm (y - P z)‖ ≤
          K * ‖y - P z - T (y + q - z)‖ := by
      rw [norm_sub_rev, ← he]
      exact ((T.symm : E →L[ℝ] E).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
    have h₁ := mul_le_mul_of_nonneg_left hR hK.le
    have h₂ := mul_le_mul_of_nonneg_left hD (mul_nonneg hK.le hη.le)
    have h₃ := mul_le_mul_of_nonneg_right hηε (norm_nonneg (y - P z))
    have hfinal :
        ‖(y + q - z) - T.symm (y - P z)‖ ≤ ε * ‖y - P z‖ := by
      nlinarith only [hA, h₁, h₂, h₃]
    have halg :
        q - (z - P z) - (T.symm (y - P z) - (y - P z)) =
          (y + q - z) - T.symm (y - P z) := by
      abel
    rw [halg]
    exact hfinal
  refine ⟨?_, hexp⟩
  intro q hq
  have hh := (hexp 1 zero_lt_one).self_of_nhds q hq
  simp only [sub_self, map_zero, sub_zero, norm_zero, mul_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
