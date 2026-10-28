-- Prove2me | solution 1 for FunctionalInequalities.Analysis.localLp_hessian_flux_trace_forcing_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:39:27.137506+00:00
-- url     : https://prove2.me/submissions/ed9f6db7-d5ae-4bfb-a8dc-eed7cf54126b

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution

section
noncomputable section
open MeasureTheory
open scoped ContDiff
universe u
section SharedCompactLocalTools
open MeasureTheory Set Filter
open scoped ContDiff RealInnerProductSpace Topology
section
/-- The product of two functions that are L2 on every compact set is locally integrable. -/
theorem FunctionalInequalities.Analysis.locallyIntegrable_mul_of_compact_L2 {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hg : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    LocallyIntegrable (fun x => f x * g x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  apply locallyIntegrable_iff.mpr
  intro S hS
  exact (hf S hS).integrable_mul (hg S hS)
end
end SharedCompactLocalTools
end
end

noncomputable section
section HessianFluxTraceForcing
open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace Topology
set_option maxHeartbeats 800000 in
/-- Compact-local L2 Hessian flux `Jᵢⱼₐ = Σ_b (H⁻¹)_{ba} T_{bij}` and local integrability of the trace
forcing `Cᵢⱼ` from compact-local L2 tensor and inverse-derivative data and compact-local inverse bounds. -/
theorem solution {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT2 : ∀ k i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => T x k i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv2 : ∀ k i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
        (Matrix.of fun a b => T x k a b) * (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) i j)) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hRtop : ∀ i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (Q : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (hQ : ∀ i j : Fin n, LocallyIntegrable (fun x => Q x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  dsimp only
  intro i j
  constructor
  · intro a S hS
    apply MeasureTheory.memLp_finsetSum (Finset.univ : Finset (Fin n))
    intro b _hb
    exact (hT2 b i j S hS).mul' (hRtop b a S hS)
  · have hTD :
        LocallyIntegrable
          (fun x => ∑ a : Fin n, ∑ b : Fin n,
            T x i a b *
              -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
                (Matrix.of fun c d => T x j c d) *
                (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) b a))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply MeasureTheory.locallyIntegrable_finsetSum
        (Finset.univ : Finset (Fin n))
      intro a _ha
      apply MeasureTheory.locallyIntegrable_finsetSum
        (Finset.univ : Finset (Fin n))
      intro b _hb
      exact FunctionalInequalities.Analysis.locallyIntegrable_mul_of_compact_L2
        (hT2 i a b) (hInv2 j b a)
    have hdouble :
        LocallyIntegrable
          (fun x => ∑ b : Fin n, ∑ a : Fin n,
            T x b i j *
              -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
                (Matrix.of fun c d => T x a c d) *
                (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) b a))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply MeasureTheory.locallyIntegrable_finsetSum
        (Finset.univ : Finset (Fin n))
      intro b _hb
      apply MeasureTheory.locallyIntegrable_finsetSum
        (Finset.univ : Finset (Fin n))
      intro a _ha
      exact FunctionalInequalities.Analysis.locallyIntegrable_mul_of_compact_L2
        (hT2 b i j) (hInv2 a b a)
    have hRow :
        LocallyIntegrable
          (fun x => ∑ b : Fin n, T x b i j *
            (∑ a : Fin n,
              -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
                (Matrix.of fun c d => T x a c d) *
                (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) b a)))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      simpa only [Finset.mul_sum] using hdouble
    exact ((hQ i j).sub hTD).add hRow
