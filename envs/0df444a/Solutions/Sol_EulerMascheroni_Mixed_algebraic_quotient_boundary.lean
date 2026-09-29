-- Prove2me | solution 1 for EulerMascheroni.Mixed.algebraic_quotient_boundary
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T13:40:31.11918+00:00
-- url     : https://prove2.me/submissions/2fb76b6b-7dd3-4f8e-8e04-f7362572cf15

import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
open Filter
open scoped Topology

/-- The positive coefficients of a mixed quotient force its boundary constant.
This uses actual convergence, not evaluation of the divergent negative series. -/
theorem mixed_quotient_boundary
    (f b : ℕ → ℂ) (c s : ℂ)
    (hb0 : b 0 = c - f 0)
    (hrec : ∀ n, b (n + 1) = b n - f (n + 1))
    (hsum : HasSum f s)
    (hb : Tendsto b atTop (𝓝 0)) : c = s := by
  have hfinite : ∀ n, b n = c - ∑ k ∈ Finset.range (n + 1), f k := by
    intro n
    induction n with
    | zero => simpa using hb0
    | succ n ih =>
      calc
        b (n + 1) = b n - f (n + 1) := hrec n
        _ = c - ((∑ k ∈ Finset.range (n + 1), f k) + f (n + 1)) := by
          rw [ih]
          ring
        _ = c - ∑ k ∈ Finset.range ((n + 1) + 1), f k := by
          rw [Finset.sum_range_succ f (n + 1)]
  have hlim : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), f k) atTop (𝓝 s) :=
    hsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hb' : Tendsto b atTop (𝓝 (c - s)) := by
    have hhlim : Tendsto (fun n => c - ∑ k ∈ Finset.range (n + 1), f k)
        atTop (𝓝 (c - s)) := tendsto_const_nhds.sub hlim
    exact hhlim.congr (fun n => (hfinite n).symm)
  have heq := tendsto_nhds_unique hb hb'
  exact sub_eq_zero.mp heq.symm

/-- If the relevant two coefficients are algebraic, so is the forced boundary. -/
theorem algebraic_mixed_quotient_boundary
    (f b : ℕ → ℂ) (c s : ℂ)
    (hb0 : b 0 = c - f 0)
    (hrec : ∀ n, b (n + 1) = b n - f (n + 1))
    (hsum : HasSum f s)
    (hb : Tendsto b atTop (𝓝 0))
    (hf0 : IsAlgebraic ℚ (f 0)) (hba : IsAlgebraic ℚ (b 0)) :
    IsAlgebraic ℚ s := by
  have hcs := mixed_quotient_boundary f b c s hb0 hrec hsum hb
  have hcb : c = b 0 + f 0 := by rw [hb0]; ring
  rw [← hcs, hcb]
  exact hba.add hf0


theorem solution (f b : ℕ → ℂ) (c s : ℂ)
    (hb0 : b 0 = c - f 0)
    (hrec : ∀ n, b (n+1) = b n - f (n+1))
    (hsum : HasSum f s)
    (hb : Filter.Tendsto b Filter.atTop (nhds 0))
    (hf0 : IsAlgebraic ℚ (f 0)) (hba : IsAlgebraic ℚ (b 0)) :
    IsAlgebraic ℚ s := by
  exact algebraic_mixed_quotient_boundary f b c s hb0 hrec hsum hb hf0 hba

#print axioms solution
