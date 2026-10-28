-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_resolvent_dominated_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T14:30:30.491988+00:00
-- url     : https://prove2.me/submissions/88d40efa-23ce-4b63-8a01-ce9c3248213f

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Theorems.Thm_AvramDividend_Classical_causal_neumann_integral_resolvent_of_convergence
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_kernel_integral_tendsto_dominated

open AvramDividend.Classical MeasureTheory Set Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A dominated Neumann series solves the causal integral resolvent. -/
theorem solution
    (a : ℝ) (B F g : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (hzero : Q 0 = F)
    (hstep : ∀ n : ℕ, Q (n + 1) =
      -(fun x : ℝ => (1 / a) *
        (∫ s in Ioc (0 : ℝ) x, B (x - s) * Q n s ∂volume)))
    (hI : ∀ m : ℕ, ∀ x : ℝ, ∀ i ∈ Finset.range (m + 1),
      IntegrableOn (fun s : ℝ => B (x - s) * Q i s)
        (Ioc (0 : ℝ) x) volume)
    (hS : ∀ x : ℝ, Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range (n + 1), Q i) x)
      atTop (nhds (g x)))
    (hQ : ∀ x : ℝ, Tendsto (fun n : ℕ => Q (n + 1) x)
      atTop (nhds (0 : ℝ)))
    (hMeas : ∀ x : ℝ, ∀ n : ℕ, AEStronglyMeasurable
      (fun s : ℝ => B (x - s) * (∑ i ∈ Finset.range (n + 1), Q i) s)
      (volume.restrict (Ioc (0 : ℝ) x)))
    (hDom : ∀ x : ℝ, ∃ D : ℝ → ℝ,
      IntegrableOn D (Ioc (0 : ℝ) x) volume ∧
      (∀ n : ℕ, ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) x)),
        ‖B (x - s) * (∑ i ∈ Finset.range (n + 1), Q i) s‖ ≤ D s)) :
    ∀ x : ℝ, g x + (1 / a) *
      (∫ s in Ioc (0 : ℝ) x, B (x - s) * g s ∂volume) = F x := by
  have hTS (x : ℝ) : Tendsto
      (fun n : ℕ => (1 / a) * (∫ s in Ioc (0 : ℝ) x,
        B (x - s) * (∑ i ∈ Finset.range (n + 1), Q i) s ∂volume))
      atTop (nhds ((1 / a) *
        (∫ s in Ioc (0 : ℝ) x, B (x - s) * g s ∂volume))) := by
    obtain ⟨D, hD, hbound⟩ := hDom x
    have hpoint : ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) x)),
        Tendsto
          (fun n : ℕ => (∑ i ∈ Finset.range (n + 1), Q i) s)
          atTop (nhds (g s)) :=
      Filter.Eventually.of_forall (fun s => hS s)
    have ht := causal_Ioc_kernel_integral_tendsto_dominated
      B (fun n s => (∑ i ∈ Finset.range (n + 1), Q i) s)
      g D x (hMeas x) hD hbound hpoint
    exact ht.const_mul (1 / a)
  exact causal_neumann_integral_resolvent_of_convergence
    a B F g Q hzero hstep hI hS hTS hQ
