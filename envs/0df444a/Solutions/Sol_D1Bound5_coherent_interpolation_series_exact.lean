-- Prove2me | solution 1 for D1Bound5.coherent_interpolation_series_exact
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:47:26.748069+00:00
-- url     : https://prove2.me/submissions/4bdc64b8-e619-4e87-91bf-88ef723d0359

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Theorems.Thm_D1Bound5_coherent_anchor_power_moment_high
import Theorems.Thm_D1Bound5_coherent_anchor_power_moment_low

section
open Finset Polynomial

namespace D1Bound5





/-- Exact interpolation of a convergent complex Taylor series.  This
proves convergence of the homogeneous tail from convergence at the finitely
many distinct nonzero anchors.  No majorant or desired interpolation
identity is included among the hypotheses. -/
theorem _root_.solution
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) (hs : s.Nonempty)
    (ha : ∀ i ∈ s, a i ≠ 0) (hinj : Set.InjOn a s)
    (c : ℕ → ℂ) (g : ι → ℂ)
    (hc : ∀ i ∈ s, HasSum (fun n : ℕ => c n * ((a i)⁻¹) ^ n) (g i)) :
    Summable (fun k : ℕ => c (s.card + k) *
      MvPolynomial.aeval (fun i : s => (a i)⁻¹)
        (MvPolynomial.hsymm s ℂ k)) ∧
    (∑ i ∈ s, ((a i) ^ (s.card - 1) /
      (∏ j ∈ s.erase i, (a i - a j))) * g i) =
      c 0 + ((-1 : ℂ) ^ (s.card - 1) * (∏ i ∈ s, a i)⁻¹) *
        ∑' k : ℕ, c (s.card + k) *
          MvPolynomial.aeval (fun i : s => (a i)⁻¹)
            (MvPolynomial.hsymm s ℂ k) := by
  let w : ι → ℂ := fun i =>
    (a i) ^ (s.card - 1) / (∏ j ∈ s.erase i, (a i - a j))
  let M : ℕ → ℂ := fun n => ∑ i ∈ s, w i * ((a i)⁻¹) ^ n
  let H : ℕ → ℂ := fun k =>
    MvPolynomial.aeval (fun i : s => (a i)⁻¹) (MvPolynomial.hsymm s ℂ k)
  let A : ℂ := (-1 : ℂ) ^ (s.card - 1) * (∏ i ∈ s, a i)⁻¹
  let lhs : ℂ := ∑ i ∈ s, w i * g i
  have hfull : HasSum (fun n : ℕ => c n * M n) lhs := by
    have h := hasSum_sum (s := s) (fun i hi => (hc i hi).mul_left (w i))
    refine h.congr_fun ?_
    intro n
    dsimp only [M]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hprefix : (∑ n ∈ Finset.range s.card, c n * M n) = c 0 := by
    calc
      (∑ n ∈ Finset.range s.card, c n * M n) =
        ∑ n ∈ Finset.range s.card, if n = 0 then c 0 else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        have hm : M n = if n = 0 then 1 else 0 :=
          coherent_anchor_power_moment_low s a hs ha hinj n (Finset.mem_range.mp hn)
        rw [hm]
        by_cases hn0 : n = 0 <;> simp [hn0]
      _ = c 0 := by simp [hs.card_pos]
  have htailRaw := (hasSum_nat_add_iff' s.card).2 hfull
  rw [hprefix] at htailRaw
  have htail : HasSum (fun k : ℕ => A * (c (s.card + k) * H k)) (lhs - c 0) := by
    refine htailRaw.congr_fun ?_
    intro k
    have hm : M (s.card + k) = A * H k :=
      coherent_anchor_power_moment_high s a hs ha hinj k
    rw [Nat.add_comm k s.card, hm]
    ring
  have hA : A ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ (by norm_num))
    exact inv_ne_zero (Finset.prod_ne_zero_iff.mpr ha)
  have hsum : Summable (fun k : ℕ => c (s.card + k) * H k) :=
    (summable_mul_left_iff hA).mp htail.summable
  refine ⟨hsum, ?_⟩
  have heq := htail.tsum_eq
  rw [tsum_mul_left] at heq
  change lhs = c 0 + A * ∑' k : ℕ, c (s.card + k) * H k
  calc
    lhs = c 0 + (lhs - c 0) := by ring
    _ = _ := by rw [heq]







end D1Bound5




open Finset

namespace D1Bound5



end D1Bound5




open Finset

namespace D1Bound5





end D1Bound5




namespace D1Bound5









end D1Bound5
end
