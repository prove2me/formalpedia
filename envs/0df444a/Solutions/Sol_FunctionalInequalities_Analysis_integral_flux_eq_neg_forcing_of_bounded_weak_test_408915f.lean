-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_flux_eq_neg_forcing_of_bounded_weak_test_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:39:21.743922+00:00
-- url     : https://prove2.me/submissions/e36728f4-37ba-45ff-8df4-bde934f3c803

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
import Theorems.Thm_FunctionalInequalities_Analysis_compact_bounded_test_domination_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset_408915f

section
noncomputable section
open MeasureTheory
open scoped ContDiff
section BoundedWeakDerivativeApproximation
open MeasureTheory Filter Set Metric
open scoped ContDiff Convolution Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
/-- A bounded compact rough test whose weak derivatives along every coordinate are compactly supported
and globally L2 admits ONE smooth compactly supported sequence with supports in one compact set, the
uniform bound `3 * C`, global L2 coordinate derivatives converging in L2 to the given weak derivatives,
and full-sequence almost-everywhere convergence. Every finite dimension, zero included; no continuity of
`η` is assumed. Support for Letwin arXiv:2607.24164v1 (2.6). -/
theorem FunctionalInequalities.Analysis.exists_contDiff_compact_bounded_all_weak_deriv_approximation {n : ℕ}
    {η : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i)
      (EuclideanSpace.basisFun (Fin n) ℝ i))
    (hac : ∀ i : Fin n, HasCompactSupport (a i))
    (ha2 : ∀ i : Fin n, MemLp (a i) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S ∧
      Function.support η ⊆ S ∧ (∀ i : Fin n, Function.support (a i) ⊆ S) ∧
      ∃ θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ m : ℕ, ContDiff ℝ ∞ (θ m) ∧ HasCompactSupport (θ m) ∧
          Function.support (θ m) ⊆ S ∧ (∀ x, ‖θ m x‖ ≤ 3 * C) ∧
          ∀ i : Fin n,
            Function.support (fun x => fderiv ℝ (θ m) x
              (EuclideanSpace.basisFun (Fin n) ℝ i)) ⊆ S ∧
            MemLp (fun x => fderiv ℝ (θ m) x
              (EuclideanSpace.basisFun (Fin n) ℝ i)) 2
              (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        (∀ i : Fin n,
          Tendsto (fun m => eLpNorm
            (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i) - a i x)
            2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0)) ∧
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          Tendsto (fun m => θ m x) atTop (𝓝 (η x)) := by
  have hK : IsCompact (tsupport η ∪ ⋃ i, tsupport (a i)) :=
    hηc.isCompact.union (isCompact_iUnion fun i => (hac i).isCompact)
  obtain ⟨S, hS, -, hηS, haS, hθ⟩ :=
    exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset_408915f hη hbound hK
      ((subset_tsupport η).trans subset_union_left)
      (fun i => (subset_tsupport (a i)).trans
        ((subset_iUnion (fun i => tsupport (a i)) i).trans subset_union_right))
      one_pos hweak ha2
  exact ⟨S, hS, hηS, haS, hθ⟩
end
end
end BoundedWeakDerivativeApproximation
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
end
end
end WeakProducts
universe u
section BoundedWeakDerivativeTesting
open MeasureTheory Filter Set
open scoped Topology ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
/-- Dominated convergence for local L1 forcing and common compact uniformly bounded tests. -/
private theorem FunctionalInequalities.Analysis.tendsto_integral_mul_compact_bounded_tests {n : ℕ}
    {F η : EuclideanSpace ℝ (Fin n) → ℝ}
    {θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin n))} {C : ℝ}
    (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hS : IsCompact S)
    (hη : AEStronglyMeasurable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hηsupp : Function.support η ⊆ S) (hηbound : ∀ x, ‖η x‖ ≤ C)
    (hθ : ∀ m, AEStronglyMeasurable (θ m)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hθsupp : ∀ m, Function.support (θ m) ⊆ S)
    (hθbound : ∀ m x, ‖θ m x‖ ≤ C)
    (hAE : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun m => θ m x) atTop (𝓝 (η x))) :
    (∀ m, Integrable (fun x => F x * θ m x)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun x => F x * η x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Tendsto (fun m => ∫ x, F x * θ m x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop
      (𝓝 (∫ x, F x * η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) := by
  have hlim := compact_bounded_test_domination_408915f hF hS hη hηsupp hηbound
  have hseq (m : ℕ) :=
    compact_bounded_test_domination_408915f hF hS (hθ m) (hθsupp m) (hθbound m)
  refine ⟨fun m => (hseq m).2.2, hlim.2.2, ?_⟩
  refine tendsto_integral_of_dominated_convergence
    (S.indicator fun x => C * ‖F x‖)
    (fun m => hF.aestronglyMeasurable.mul (hθ m)) hlim.1
    (fun m => Filter.Eventually.of_forall (hseq m).2.1) ?_
  filter_upwards [hAE] with x hx
  exact tendsto_const_nhds.mul hx
/-- Local L2 fluxes can be paired with common compact global L2 test derivatives. -/
private theorem FunctionalInequalities.Analysis.tendsto_integral_mul_of_compact_local_l2 {n : ℕ}
    {J b : EuclideanSpace ℝ (Fin n) → ℝ}
    {v : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S)
    (hJ : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      MemLp J 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K))
    (hb : MemLp b 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hv : ∀ m, MemLp (v m) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbS : Function.support b ⊆ S) (hvS : ∀ m, Function.support (v m) ⊆ S)
    (hconv : Tendsto (fun m => eLpNorm (v m - b) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0)) :
    Integrable (fun x => J x * b x) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∀ m, Integrable (fun x => J x * v m x)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    Tendsto (fun m => ∫ x, J x * v m x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop
      (𝓝 (∫ x, J x * b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) := by
  have hJS : MemLp (S.indicator J) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_indicator_iff_restrict hS.measurableSet).2 (hJ S hS)
  have heqb : (fun x => S.indicator J x * b x) = (fun x => J x * b x) := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · have hz : b x = 0 := by
        by_contra hne
        exact hx (hbS hne)
      rw [Set.indicator_of_notMem hx, hz, mul_zero, mul_zero]
  have heqv (m : ℕ) : (fun x => S.indicator J x * v m x) =
      (fun x => J x * v m x) := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · have hz : v m x = 0 := by
        by_contra hne
        exact hx (hvS m hne)
      rw [Set.indicator_of_notMem hx, hz, mul_zero, mul_zero]
  have hJb : Integrable (fun x => J x * b x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [← heqb]
    exact hJS.integrable_mul hb
  have hJv (m : ℕ) : Integrable (fun x => J x * v m x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [← heqv m]
    exact hJS.integrable_mul (hv m)
  refine ⟨hJb, hJv, ?_⟩
  have ht := tendsto_integral_mul_of_l2 hJS hb hv hconv
  have hseq : (fun m => ∫ x, S.indicator J x * v m x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      (fun m => ∫ x, J x * v m x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    funext m
    rw [heqv m]
  rw [hseq, heqb] at ht
  exact ht
private theorem FunctionalInequalities.Analysis.integral_flux_eq_neg_forcing_of_test_limits {n : ℕ}
    {J a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {F η : EuclideanSpace ℝ (Fin n) → ℝ}
    {θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {v : ℕ → Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin n))} {C : ℝ}
    (hS : IsCompact S)
    (hJ : ∀ i : Fin n, ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      MemLp (J i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K))
    (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hη : AEStronglyMeasurable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hηsupp : Function.support η ⊆ S) (hηbound : ∀ x, ‖η x‖ ≤ C)
    (hθ : ∀ m, AEStronglyMeasurable (θ m)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hθsupp : ∀ m, Function.support (θ m) ⊆ S)
    (hθbound : ∀ m x, ‖θ m x‖ ≤ C)
    (hAE : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun m => θ m x) atTop (𝓝 (η x)))
    (ha : ∀ i : Fin n, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hasupp : ∀ i : Fin n, Function.support (a i) ⊆ S)
    (hv : ∀ m i, MemLp (v m i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hvsupp : ∀ m i, Function.support (v m i) ⊆ S)
    (hconv : ∀ i : Fin n, Tendsto (fun m => eLpNorm (v m i - a i) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0))
    (hId : ∀ m, (∫ x, ∑ i : Fin n, J i x * v m i x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * θ m x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :
    (∀ i : Fin n, Integrable (fun x => J i x * a i x)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun x => F x * η x) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ∑ i : Fin n, J i x * a i x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  have hforcing := tendsto_integral_mul_compact_bounded_tests
    hF hS hη hηsupp hηbound hθ hθsupp hθbound hAE
  have hflux (i : Fin n) := tendsto_integral_mul_of_compact_local_l2
    hS (hJ i) (ha i) (fun m => hv m i) (hasupp i) (fun m => hvsupp m i) (hconv i)
  refine ⟨fun i => (hflux i).1, hforcing.2.1, ?_⟩
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin n))
    (fun i _ => (hflux i).2.2)
  have hL : Tendsto (fun m => ∫ x, ∑ i : Fin n, J i x * v m i x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop
      (𝓝 (∫ x, ∑ i : Fin n, J i x * a i x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) := by
    have hseq (m : ℕ) := integral_finsetSum (Finset.univ : Finset (Fin n))
      (fun i _ => (hflux i).2.1 m)
    have hlim := integral_finsetSum (Finset.univ : Finset (Fin n))
      (fun i _ => (hflux i).1)
    simpa only [← hseq, ← hlim] using hsum
  have hR : Tendsto (fun m => ∫ x, ∑ i : Fin n, J i x * v m i x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop
      (𝓝 (-(∫ x, F x * η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))) := by
    simpa only [hId] using hforcing.2.2.neg
  exact tendsto_nhds_unique hL hR
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- Bounded weak-test extension of a compact-test divergence identity: a compact-local L2 flux `J` and a
locally integrable forcing `F` satisfying `∫ Σᵢ Jᵢ ∂ᵢψ = -∫ F ψ` for every compactly supported C1 `ψ`
satisfy it for a bounded compactly supported locally integrable `η` whose coordinate weak derivatives are
compactly supported and globally L2, with both sides integrable. Every finite dimension, zero included. -/
theorem solution {n : ℕ}
    {J a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {F η : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hJ : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (J i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hId : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, ∑ i : Fin n, J i x * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ i : Fin n, FunctionalInequalities.Analysis.HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (hac : ∀ i : Fin n, HasCompactSupport (a i))
    (ha2 : ∀ i : Fin n, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (∀ i : Fin n, Integrable (fun x => J i x * a i x)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun x => F x * η x) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ∑ i : Fin n, J i x * a i x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  obtain ⟨S, hS, hηS, haS, θ, hθ, hconv, hAE⟩ :=
    FunctionalInequalities.Analysis.exists_contDiff_compact_bounded_all_weak_deriv_approximation hη hbound hηc hweak hac ha2
  have hC : 0 ≤ C := (norm_nonneg (η 0)).trans (hbound 0)
  have hη3 (x : EuclideanSpace ℝ (Fin n)) : ‖η x‖ ≤ 3 * C :=
    (hbound x).trans (by linarith)
  exact integral_flux_eq_neg_forcing_of_test_limits hS hJ hF
    hη.aestronglyMeasurable hηS hη3
    (fun m => (hθ m).1.continuous.aestronglyMeasurable)
    (fun m => (hθ m).2.2.1) (fun m => (hθ m).2.2.2.1) hAE ha2 haS
    (fun m i => ((hθ m).2.2.2.2 i).2)
    (fun m i => ((hθ m).2.2.2.2 i).1) hconv
    (fun m => hId (θ m) ((hθ m).1.of_le (WithTop.coe_le_coe.mpr le_top)) (hθ m).2.1)
