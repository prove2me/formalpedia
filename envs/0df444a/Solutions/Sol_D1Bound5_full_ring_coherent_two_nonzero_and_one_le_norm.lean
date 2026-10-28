-- Prove2me | solution 1 for D1Bound5.full_ring_coherent_two_nonzero_and_one_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:49:41.358223+00:00
-- url     : https://prove2.me/submissions/fd938624-4e74-43e2-b10f-575443e7ce9f

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_coherent_analytic_two_ne_zero_of_large_terminal
import Theorems.Thm_D1Bound5_full_ring_coherent_linear_form_one_le_norm
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5









/-- The arithmetic and analytic bridges combined for actual tuple
entries.  The paper's size assumptions force the coherent form nonzero
and therefore give its integral lower bound, with neither fact assumed. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {T : Finset (𝓞 K)} (hT : IsD1 T) (a b p q : 𝓞 K)
    (ha : a ∈ T) (hb : b ∈ T) (hp : p ∈ T) (hq : q ∈ T)
    (hab : a ≠ b) (hap : a ≠ p) (haq : a ≠ q)
    (hbp : b ≠ p) (hbq : b ≠ q) (hpq : p ≠ q)
    (eta : ℂ) (heta : eta ^ 2 = phi (p : K) * phi (q : K))
    (hB : 3 ≤ ‖phi (b : K)‖) (hP : 5 * ‖phi (b : K)‖ ≤ ‖phi (p : K)‖)
    (hQ : 5 * ‖phi (a : K)‖ * ‖phi (b : K)‖ * ‖phi (p : K)‖ ≤ ‖phi (q : K)‖) :
    let L := coherentAnchorRoot (phi (a : K)) (phi (p : K)) (phi (q : K)) eta -
      coherentAnchorRoot (phi (b : K)) (phi (p : K)) (phi (q : K)) eta -
      (phi (a : K) - phi (b : K)) *
        coherentTerminalRoot (phi (p : K)) (phi (q : K)) eta
    L ≠ 0 ∧ 1 ≤ ‖L‖ := by
  dsimp only
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hnz (u : 𝓞 K) (hu : u ∈ T) : f u ≠ 0 := by
    intro h
    exact hT.1 u hu (hf (by simpa only [map_zero] using h))
  obtain ⟨r, hr⟩ := hT.2 a ha b hb hab
  obtain ⟨s, hs⟩ := hT.2 a ha p hp hap
  obtain ⟨t, ht⟩ := hT.2 b hb p hp hbp
  have hr' : (f r) ^ 2 = f a * f b + 1 := by
    simpa only [pow_two, map_mul, map_add, map_one] using congrArg f hr
  have hs' : (f s) ^ 2 = f a * f p + 1 := by
    simpa only [pow_two, map_mul, map_add, map_one] using congrArg f hs
  have ht' : (f t) ^ 2 = f b * f p + 1 := by
    simpa only [pow_two, map_mul, map_add, map_one] using congrArg f ht
  have hnonzero := coherent_analytic_two_ne_zero_of_large_terminal
    (f a) (f b) (f p) (f q) eta (f r) (f s) (f t)
    (hnz a ha) (hnz b hb) (hnz p hp) (hnz q hq) (fun h => hab (hf h))
    heta hr' hs' ht' (one_le_norm_integer hK phi (hT.1 a ha)) hB hP hQ
  refine ⟨hnonzero, ?_⟩
  let av : Fin 2 → 𝓞 K := ![a, b]
  let cv : Fin 2 → 𝓞 K := ![1, -1]
  have hav : ∀ i, av i ∈ T := by
    intro i
    fin_cases i <;> simp [av, ha, hb]
  have havp : ∀ i, av i ≠ p := by
    intro i
    fin_cases i <;> simp [av, hap, hbp]
  have havq : ∀ i, av i ≠ q := by
    intro i
    fin_cases i <;> simp [av, haq, hbq]
  have hE :
      -phi ((a - b : 𝓞 K) : K) * coherentTerminalRoot (f p) (f q) eta +
        (∑ i : Fin 2, phi (cv i : K) * coherentAnchorRoot (phi (av i : K)) (f p) (f q) eta) =
      coherentAnchorRoot (f a) (f p) (f q) eta -
        coherentAnchorRoot (f b) (f p) (f q) eta -
        (f a - f b) * coherentTerminalRoot (f p) (f q) eta := by
    change -f (a - b) * coherentTerminalRoot (f p) (f q) eta +
      (∑ i : Fin 2, f (cv i) * coherentAnchorRoot (f (av i)) (f p) (f q) eta) = _
    simp [Fin.sum_univ_two, av, cv]
    ring
  have hE0 :
      -phi ((a - b : 𝓞 K) : K) * coherentTerminalRoot (f p) (f q) eta +
        (∑ i : Fin 2, phi (cv i : K) * coherentAnchorRoot (phi (av i : K)) (f p) (f q) eta) ≠ 0 := by
    rw [hE]
    exact hnonzero
  have hlow := full_ring_coherent_linear_form_one_le_norm hK phi hT hp hq hpq
    av cv (a - b) hav havp havq eta heta hE0
  change 1 ≤ ‖-phi ((a - b : 𝓞 K) : K) * coherentTerminalRoot (f p) (f q) eta +
    (∑ i : Fin 2, phi (cv i : K) * coherentAnchorRoot (phi (av i : K)) (f p) (f q) eta)‖ at hlow
  rw [hE] at hlow
  exact hlow

end D1Bound5
end
