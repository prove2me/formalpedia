-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_weak_hessian_flux_eq_trace_derivative_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:43:03.626805+00:00
-- url     : https://prove2.me/submissions/15c9464f-c84c-41a9-8f16-594aa5dce090

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_compact_mul_data_readable
import Theorems.Thm_FunctionalInequalities_Analysis_ae_weak_third_derivative_symm_readable
import Theorems.Thm_FunctionalInequalities_Analysis_integral_weakDeriv_mul_eq_swap_readable
import Theorems.Thm_FunctionalInequalities_Analysis_localLp_hessian_flux_trace_forcing_readable
import Theorems.Thm_FunctionalInequalities_Analysis_integral_array_pair_balance_readable

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
/-- A function that is L2 on every compact set is locally integrable. -/
theorem FunctionalInequalities.Analysis.locallyIntegrable_of_compact_local_memLp_two {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    LocallyIntegrable f (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  apply locallyIntegrable_iff.mpr
  intro S hS
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  exact (hf S hS).integrable (by norm_num)
end
end SharedCompactLocalTools
end
end

noncomputable section
section WeakHessianFlux
open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace Topology
private theorem FunctionalInequalities.Analysis.memLp_two_of_compact_local_memLp_top {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  intro S hS
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  exact (hf S hS).mono_exponent le_top
/-- Closed actual inverse/Hessian pairwise compact curl test, before any trace assembly. -/
private theorem FunctionalInequalities.Analysis.integral_compact_hessian_inverse_curl {n : ℕ}
    {u ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv : ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (i j a b : Fin n) :
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k r s => -((R x * (Matrix.of fun c d => T x k c d) * R x) r s)
    (∫ x, T x j i b * (ψ x * D x a b a +
      fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a) * R x b a)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
    ∫ x, T x a i b * (ψ x * D x j b a +
      fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j) * R x b a)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hηj := HasWeakDerivAlong.compact_mul_data_readable
    (hInv j b a).1 (hInv j b a).2.1 (hInv j b a).2.2 hψ hψc
  have hηa := HasWeakDerivAlong.compact_mul_data_readable
    (hInv a b a).1 (hInv a b a).2.1 (hInv a b a).2.2 hψ hψc
  exact integral_weakDeriv_mul_eq_swap_readable
    (hT j i b).1 (hT a i b).1 (hT j i b).2 (hT a i b).2
    hηj.1 hηa.1 hηj.2.1 hηj.2.2.1 hηa.2.2.1 hηj.2.2.2 hηa.2.2.2
private theorem FunctionalInequalities.Analysis.integrable_compact_continuous_mul_of_local_memLp_two {n : ℕ}
    {f χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Integrable (fun x => χ x * f x) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  simpa only [smul_eq_mul] using
    (locallyIntegrable_of_compact_local_memLp_two hf).integrable_smul_left_of_hasCompactSupport
      hχ hχc
set_option maxHeartbeats 1200000 in
/-- Unweighted weak Hessian flux identity: for every compactly supported C1 `ψ`,
`∫ Σₐ Jᵢⱼₐ ∂ₐψ = -∫ Cᵢⱼ ψ`, with `J` compact-local L2 and `C` locally integrable, from a C1 potential
with Lipschitz gradient, its weak Hessian tensor, weak inverse derivatives and a weak trace derivative. -/
theorem solution {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hu : ContDiff ℝ 1 u) (hG : LipschitzWith G (gradient u))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv : ∀ k i j : Fin n,
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j)
          (fun x => -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹) i j)) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (Q : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (hQ : ∀ i j : Fin n,
      FunctionalInequalities.Analysis.HasWeakDerivAlong
        (fun x => ((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * (Matrix.of fun a b => T x i a b)).trace)
        (fun x => Q x i j) (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => Q x i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
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
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, ∑ a : Fin n, J x i j a *
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -(∫ x, C x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  classical
  let R := fun x => (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹
  let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
  let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
  let C₀ := fun x i j => Q x i j -
    (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
    ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
  change ∀ i j : Fin n, _
  intro i j
  have hdata := FunctionalInequalities.Analysis.localLp_hessian_flux_trace_forcing_readable T
    (fun k i j => (hT k i j).2)
    (fun k i j => (hInv k i j).2.1)
    (fun i j => (hInv i i j).2.2)
    Q (fun i j => (hQ i j).1.2.1)
  refine ⟨(hdata i j).1, (hdata i j).2, ?_⟩
  intro ψ hψ hψc
  let e : Fin n → EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ
  let dψ := fun x a => fderiv ℝ ψ x (e a)
  let A := fun a b x => ψ x * (T x b i j * D x a b a)
  let B := fun a b x => dψ x a * (T x b i j * R x b a)
  let C := fun a b x => ψ x * (T x i a b * D x j b a)
  let E := fun a b x => dψ x j * (T x i a b * R x b a)
  let F := fun x => Q x i j * ψ x
  have hR2 (b a : Fin n) : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => R x b a) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    FunctionalInequalities.Analysis.memLp_two_of_compact_local_memLp_top (hInv i b a).2.2
  have hdψ (a : Fin n) : Continuous (fun x => dψ x a) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdψc (a : Fin n) : HasCompactSupport (fun x => dψ x a) :=
    hψc.fderiv_apply ℝ (e a)
  have hTD (k l m v b a : Fin n) :
      LocallyIntegrable (fun x => T x k l m * D x v b a)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    FunctionalInequalities.Analysis.locallyIntegrable_mul_of_compact_L2 (hT k l m).2 (hInv v b a).2.1
  have hTR (k l m b a : Fin n) :
      LocallyIntegrable (fun x => T x k l m * R x b a)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    FunctionalInequalities.Analysis.locallyIntegrable_mul_of_compact_L2 (hT k l m).2 (hR2 b a)
  have hA (a b : Fin n) : Integrable (A a b)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul] using
      (hTD b i j a b a).integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
  have hB (a b : Fin n) : Integrable (B a b)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul] using
      (hTR b i j b a).integrable_smul_left_of_hasCompactSupport (hdψ a) (hdψc a)
  have hC (a b : Fin n) : Integrable (C a b)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul] using
      (hTD i a b j b a).integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
  have hE (a b : Fin n) : Integrable (E a b)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [smul_eq_mul] using
      (hTR i a b b a).integrable_smul_left_of_hasCompactSupport (hdψ j) (hdψc j)
  have hF : Integrable F (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hf := FunctionalInequalities.Analysis.integrable_compact_continuous_mul_of_local_memLp_two
      (hQ i j).2 hψ.continuous hψc
    simpa only [mul_comm] using hf
  have hsymm := FunctionalInequalities.Analysis.ae_weak_third_derivative_symm_readable hu hG (fun k i j => (hT k i j).1)
  have hPair (a b : Fin n) :
      (∫ x, A a b x + B a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, C a b x + E a b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hc := FunctionalInequalities.Analysis.integral_compact_hessian_inverse_curl T hT hInv hψ hψc i j a b
    change (∫ x, T x j i b * (ψ x * D x a b a + dψ x a * R x b a)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, T x a i b * (ψ x * D x j b a + dψ x j * R x b a)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) at hc
    calc
      _ = ∫ x, T x j i b * (ψ x * D x a b a + dψ x a * R x b a)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
        apply integral_congr_ae
        filter_upwards [hsymm] with x hx
        have ht : T x j i b = T x b i j :=
          (hx j i b).1.trans ((hx i j b).2.trans (hx i b j).1)
        dsimp only [A, B]
        rw [ht]
        ring
      _ = _ := hc
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hsymm] with x hx
        dsimp only [C, E]
        rw [(hx a i b).1]
        ring
  have hTracePoint (x : EuclideanSpace ℝ (Fin n)) :
      (∑ a : Fin n, ∑ b : Fin n, E a b x) =
        (R x * (Matrix.of fun a b => T x i a b)).trace * dψ x j := by
    dsimp only [E]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hTrace : (∫ x, ∑ a : Fin n, ∑ b : Fin n, E a b x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    calc
      _ = ∫ x, (R x * (Matrix.of fun a b => T x i a b)).trace * dψ x j
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
        integral_congr_ae (Filter.Eventually.of_forall hTracePoint)
      _ = _ := (hQ i j).1.2.2 ψ hψ hψc
  have hBalance := FunctionalInequalities.Analysis.integral_array_pair_balance_readable A B C E F hA hB hC hE hF hPair hTrace
  have hFluxPoint (x : EuclideanSpace ℝ (Fin n)) :
      (∑ a : Fin n, J x i j a * dψ x a) =
        ∑ a : Fin n, ∑ b : Fin n, B a b x := by
    dsimp only [J, B]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hForcePoint (x : EuclideanSpace ℝ (Fin n)) :
      C₀ x i j * ψ x = F x - (∑ a : Fin n, ∑ b : Fin n, C a b x) +
        ∑ a : Fin n, ∑ b : Fin n, A a b x := by
    dsimp only [C₀, F, C, A]
    simp only [sub_mul, add_mul, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
  change (∫ x, ∑ a : Fin n, J x i j a * dψ x a
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
    -(∫ x, C₀ x i j * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
  rw [integral_congr_ae (Filter.Eventually.of_forall hFluxPoint)]
  rw [integral_congr_ae (Filter.Eventually.of_forall hForcePoint)]
  exact hBalance
