-- Prove2me | solution 1 for DerivativeChainGini.actual_polynomial_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:57:39.071899+00:00
-- url     : https://prove2.me/submissions/9dc4ee75-5765-4a45-87fd-c99dfc4cf2d4

import Mathlib
import Definitions.Def_DerivativeChainGini_GiniCounterexample
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainDivisorAnchor
end DerivativeChainDivisorAnchor
namespace DerivativeChainGini
end DerivativeChainGini
namespace DerivativeChainGiniCircle
end DerivativeChainGiniCircle
namespace DerivativeChainGiniFamily
end DerivativeChainGiniFamily
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainGini
noncomputable section
















theorem cost_table : ∀ i j : Fin 5,
    cost i j = (![![0, 2, Real.sqrt 2, Real.sqrt 2, 1],
      ![2, 0, Real.sqrt 2, Real.sqrt 2, 1],
      ![Real.sqrt 2, Real.sqrt 2, 0, 2, 1],
      ![Real.sqrt 2, Real.sqrt 2, 2, 0, 1],
      ![1, 1, 1, 1, 0]] : Fin 5 → Fin 5 → ℝ) i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cost, vertex, Complex.norm_def, Complex.normSq]

theorem radialCoupling_valid : IsCoupling radialCoupling := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [ radialCoupling]
  constructor
  · intro i
    fin_cases i <;> norm_num [ radialCoupling, parentMass, parentMultiplicity, Fin.sum_univ_succ]
  · intro j
    fin_cases j <;> norm_num [ radialCoupling, childMass, childMultiplicity, Fin.sum_univ_succ]

theorem radialCoupling_cost : transportCost radialCoupling = 1/5 := by
  simp only [transportCost, cost_table]
  norm_num [ radialCoupling, Fin.sum_univ_succ]

theorem coupling_lower_bound (q : Fin 5 → Fin 5 → ℝ) (hq : IsCoupling q) :
    1/5 ≤ transportCost q := by
  have hz : ∀ j, q (⟨4, by decide⟩ : Fin 5) j = 0 := by
    have hs := hq.2.1 (⟨4, by decide⟩ : Fin 5)
    norm_num [parentMass, parentMultiplicity] at hs
    exact fun j => (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hq.1 (⟨4, by decide⟩ : Fin 5) k)).mp hs j (Finset.mem_univ j)
  have hterm : ∀ i j : Fin 5, (if j = (⟨4, by decide⟩ : Fin 5) then q i j else 0) ≤ q i j * cost i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [cost_table, hz] <;>
      first | positivity | exact mul_nonneg (hq.1 _ _) (Real.sqrt_nonneg _) | exact hq.1 _ _
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm i j))
  simpa only [transportCost, Finset.sum_ite_eq', Finset.mem_univ, if_true, hq.2.2 (⟨4, by decide⟩ : Fin 5),
    show childMass (⟨4, by decide⟩ : Fin 5) = (1/5 : ℝ) by norm_num [childMass, childMultiplicity]] using hs

theorem optimalW1_exact : optimalW1 = 1/5 := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨radialCoupling, radialCoupling_valid, radialCoupling_cost⟩
  · rintro t ⟨q, hq, rfl⟩
    exact coupling_lower_bound q hq

theorem parent_gini : gini parentMass = (1 + Real.sqrt 2)/2 := by
  simp only [gini, cost_table]
  norm_num [parentMass, parentMultiplicity, Fin.sum_univ_succ]
  ring

theorem child_gini : gini childMass = (16/25 : ℝ) * ((1 + Real.sqrt 2)/2) + 8/25 := by
  simp only [gini, cost_table]
  norm_num [childMass, childMultiplicity, Fin.sum_univ_succ]
  ring

theorem candidateA_exact_excess :
    optimalW1 - ((16/15 : ℝ) * gini parentMass - gini childMass) =
      (23 - 16 * Real.sqrt 2)/75 := by
  rw [optimalW1_exact, parent_gini, child_gini]
  ring

theorem candidateA_false : (16/15 : ℝ) * gini parentMass - gini childMass < optimalW1 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  have hstrict : 0 < (23 - 16 * Real.sqrt 2)/75 := by nlinarith
  linarith [candidateA_exact_excess]

open Polynomial




theorem square_factorization :
    (X-1)*(X+1)*(X-C Complex.I)*(X+C Complex.I) = (X^4-1 : ℂ[X]) := by
  have hi : (C Complex.I : ℂ[X])^2 = -1 := by
    rw [← map_pow, Complex.I_sq]
    simp
  linear_combination -(X^2-1)*hi

theorem parent_factorization :
    (∏ i : Fin 5, (X-C (vertex i)) ^ parentMultiplicity i) = source := by
  norm_num [parentMultiplicity, vertex, Fin.prod_univ_succ, source]
  convert congrArg (fun t : ℂ[X] => t^4) square_factorization using 1 <;> ring

theorem child_factorization :
    (∏ i : Fin 5, (X-C (vertex i)) ^ childMultiplicity i) = normalizedChild := by
  norm_num [childMultiplicity, vertex, Fin.prod_univ_succ, normalizedChild]
  convert congrArg (fun t : ℂ[X] => X^3*t^3) square_factorization using 1 <;> ring

theorem derivative_factorization : source.derivative = C 16 * normalizedChild := by
  simp [source, normalizedChild, derivative_pow]
  norm_num [Polynomial.C_ofNat]
  ring

theorem parent_degree : source.natDegree = 16 := by
  unfold source
  compute_degree <;> norm_num

theorem child_degree : normalizedChild.natDegree = 15 := by
  unfold normalizedChild
  compute_degree <;> norm_num







theorem parent_roots : source.roots = Finset.univ.val.bind (fun i : Fin 5 => parentMultiplicity i • ({vertex i} : Multiset ℂ)) := by
  rw [← parent_factorization, roots_prod]
  · simp only [roots_pow, roots_X_sub_C]
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (X_sub_C_ne_zero _))

theorem child_roots : normalizedChild.roots = Finset.univ.val.bind (fun i : Fin 5 => childMultiplicity i • ({vertex i} : Multiset ℂ)) := by
  rw [← child_factorization, roots_prod]
  · simp only [roots_pow, roots_X_sub_C]
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (X_sub_C_ne_zero _))

theorem vertex_injective : Function.Injective vertex := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [vertex, Complex.ext_iff] <;> norm_num at *




theorem parent_root_count (i : Fin 5) : source.roots.count (vertex i) = parentMultiplicity i := by
  rw [parent_roots, Multiset.count_bind]
  change (∑ j : Fin 5, Multiset.count (vertex i) (parentMultiplicity j • {vertex j})) = _
  simp [Multiset.count_singleton, vertex_injective.eq_iff]

theorem child_root_count (i : Fin 5) : normalizedChild.roots.count (vertex i) = childMultiplicity i := by
  rw [child_roots, Multiset.count_bind]
  change (∑ j : Fin 5, Multiset.count (vertex i) (childMultiplicity j • {vertex j})) = _
  simp [Multiset.count_singleton, vertex_injective.eq_iff]

theorem parent_uniform_slot_law (i : Fin 5) :
    parentMass i = (source.roots.count (vertex i) : ℝ) / source.natDegree := by
  rw [parent_root_count, parent_degree]
  rfl

theorem child_uniform_slot_law (i : Fin 5) :
    childMass i = (normalizedChild.roots.count (vertex i) : ℝ) / normalizedChild.natDegree := by
  rw [child_root_count, child_degree]
  rfl

theorem source_monic : source.Monic := by
  change Monic ((X^4-1 : ℂ[X])^4)
  apply Monic.pow
  simpa using (monic_X_pow_sub_C (R := ℂ) 1 (n := 4) (by decide))

theorem normalized_derivative : C (1/16 : ℂ) * source.derivative = normalizedChild := by
  rw [derivative_factorization, ← mul_assoc, ← map_mul]
  norm_num



end
end DerivativeChainGini


set_option autoImplicit false
open scoped BigOperators
open DerivativeChainGini



































open Polynomial











































theorem solution :
    source = (X^4-1 : ℂ[X])^4 ∧ source.Monic ∧ source.natDegree = 16 ∧
    C (1/16 : ℂ) * source.derivative = X^3*(X^4-1)^3 ∧
    (∀ i : Fin 5, parentMass i = (source.roots.count (vertex i) : ℝ)/source.natDegree) ∧
    (∀ i : Fin 5, childMass i = (normalizedChild.roots.count (vertex i) : ℝ)/normalizedChild.natDegree) ∧
    optimalW1 = 1/5 ∧ gini parentMass = (1+Real.sqrt 2)/2 ∧
    optimalW1 - ((16/15 : ℝ)*gini parentMass-gini childMass) = (23-16*Real.sqrt 2)/75 ∧
    (16/15 : ℝ)*gini parentMass-gini childMass < optimalW1 := by
  exact ⟨rfl, source_monic, parent_degree, normalized_derivative,
    parent_uniform_slot_law, child_uniform_slot_law, optimalW1_exact, parent_gini,
    candidateA_exact_excess, candidateA_false⟩
