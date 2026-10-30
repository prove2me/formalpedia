-- Prove2me | solution 1 for DerivativeChainGiniFamily.actual_polynomial_family_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:00:06.140191+00:00
-- url     : https://prove2.me/submissions/e1518a27-e982-4d70-9fe9-bd34569110bd

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteNormMean
import Definitions.Def_DerivativeChainGini_GiniBinomialFamily
import Definitions.Def_DerivativeChainGini_GiniCandidateB
import Definitions.Def_DerivativeChainGini_GiniFamilyTransport
import Theorems.Thm_DerivativeChainContinuation_finite_gini_disk_bound
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
namespace DerivativeChainGiniFamily
noncomputable section
variable {ι : Type} [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable













theorem radialCoupling_valid (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    IsCoupling ε (radialCoupling ε : Option ι → Option ι → ℝ) := by
  classical
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : 0 ≤ 1-ε := sub_nonneg.mpr hε1
  constructor
  · intro i j
    cases i <;> cases j <;> simp only [radialCoupling]
    · positivity
    · positivity
    · positivity
    · split_ifs <;> positivity
  constructor
  · intro i
    cases i with
    | none => simp [radialCoupling, parentMass]
    | some i =>
      simp [Fintype.sum_option, radialCoupling, parentMass]
      field_simp [hn]
      <;> ring
  · intro j
    cases j with
    | none =>
      simp [Fintype.sum_option, radialCoupling, childMass]
      field_simp
    | some j => simp [Fintype.sum_option, radialCoupling, childMass]

theorem radialCoupling_cost (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) (ε : ℝ) :
    transportCost z (radialCoupling ε) = ε := by
  classical
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [transportCost, Fintype.sum_option, radialCoupling, point, hz, ite_mul]
  field_simp

theorem coupling_lower_bound (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (ε : ℝ) (q : Option ι → Option ι → ℝ) (hq : IsCoupling ε q) :
    ε ≤ transportCost z q := by
  classical
  have hzero : ∀ j, q none j = 0 := by
    exact fun j => (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hq.1 none k)).mp
      (hq.2.1 none) j (Finset.mem_univ j)
  have hterm (i j : Option ι) : (if j = none then q i j else 0) ≤ q i j * ‖point z i-point z j‖ := by
    cases i <;> cases j <;> simp [point, hz, hzero]
    exact mul_nonneg (hq.1 _ _) (norm_nonneg _)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm i j))
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true, hq.2.2 none, childMass, transportCost] using hs

theorem optimalW1_exact (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) : optimalW1 z ε = ε := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨radialCoupling ε, radialCoupling_valid ε hε hε1, radialCoupling_cost z hz ε⟩
  · rintro t ⟨q, hq, rfl⟩
    exact coupling_lower_bound z hz ε q hq


theorem parent_gini (z : ι → ℂ) :
    DerivativeChainContinuation.finiteGini parentMass (point z) =
      DerivativeChainContinuation.finiteGini (fun _ : ι => 1/(Fintype.card ι : ℝ)) z := by
  simp [DerivativeChainContinuation.finiteGini, Fintype.sum_option, parentMass, point]

theorem child_gini (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) (ε : ℝ) :
    DerivativeChainContinuation.finiteGini (childMass ε) (point z) =
      (1-ε)^2 * DerivativeChainContinuation.finiteGini (fun _ : ι => 1/(Fintype.card ι : ℝ)) z +
        2*ε*(1-ε) := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [DerivativeChainContinuation.finiteGini, Fintype.sum_option, childMass, point, hz,
    norm_neg, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  field_simp
  <;> ring

end
end DerivativeChainGiniFamily


set_option autoImplicit false
open scoped BigOperators
open Polynomial
namespace DerivativeChainGiniFamily
noncomputable section






theorem base_monic (n : ℕ) : (base n).Monic := by
  simpa [base] using monic_X_pow_sub_C (R := ℂ) 1 (n := n+2) (by omega)







theorem slot_root (n : ℕ) (i : Slots n) : (i : ℂ)^(n+2) = 1 := by
  have hi := (mem_roots (base_monic n).ne_zero).mp (Multiset.coe_mem (x := i))
  simpa [base, eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero] using hi

theorem slot_norm (n : ℕ) (i : Slots n) : ‖(i : ℂ)‖ = 1 := by
  have hi := congrArg norm (slot_root n i)
  simp only [norm_pow, norm_one] at hi
  exact (pow_left_inj₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1) (by omega : n+2 ≠ 0)).mp (by simpa using hi)

theorem base_roots_sum (n : ℕ) : (base n).roots.sum = 0 := by
  have h := (IsAlgClosed.splits (base n)).nextCoeff_eq_neg_sum_roots_of_monic (base_monic n)
  have hn : (base n).nextCoeff = 0 := by
    rw [nextCoeff, base_degree]
    simp [base, show n+2 ≠ 0 by omega,
      show n+2-1 = n+1 by omega, show n+1 ≠ n+2 by omega, show n+1 ≠ 0 by omega]
    simp only [coeff_one, show n+1 ≠ 0 by omega, if_false]
  rw [hn] at h
  exact neg_eq_zero.mp h.symm

theorem slots_sum (n : ℕ) : ∑ i : Slots n, (i : ℂ) = 0 := by
  rw [← Multiset.sum_eq_sum_coe]
  exact base_roots_sum n

theorem uniform_mean (n : ℕ) :
    ∑ i : Slots n, ((1 / (n+2 : ℝ) : ℝ) : ℂ) * (i : ℂ) = 0 := by
  rw [← Finset.mul_sum, slots_sum, mul_zero]

theorem uniform_variance (n : ℕ) :
    ∑ i : Slots n, (1 / (n+2 : ℝ))*‖(i : ℂ)-0‖^2 = 1 := by
  have hn : (n+2 : ℝ) ≠ 0 := by positivity
  simp only [sub_zero, slot_norm, one_pow, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [slots_card]
  push_cast
  field_simp

theorem source_degree (n : ℕ) : (source n).natDegree = 16*(n+2) := by
  rw [source, natDegree_pow, base_degree]

theorem child_degree (n : ℕ) : (normalizedChild n).natDegree = 16*(n+2)-1 := by
  rw [normalizedChild, natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ (base_monic n).ne_zero),
    natDegree_X_pow, natDegree_pow, base_degree]
  omega

theorem source_derivative (n : ℕ) :
    (source n).derivative = C (16*(n+2) : ℂ)*normalizedChild n := by
  simp [source, normalizedChild, base, derivative_pow, show n+2-1=n+1 by omega,
    Polynomial.C_ofNat]
  ring

theorem source_roots (n : ℕ) : (source n).roots = 16 • (base n).roots := by
  simp [source]

theorem child_roots (n : ℕ) :
    (normalizedChild n).roots = (n+1) • ({0} : Multiset ℂ) + 15 • (base n).roots := by
  rw [normalizedChild, roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ (base_monic n).ne_zero)),
    roots_X_pow, roots_pow]

end
end DerivativeChainGiniFamily


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainContinuation
namespace DerivativeChainGiniFamily
noncomputable section










theorem slot_sum_map (n : ℕ) (f : ℂ → ℝ) :
    ∑ i : Slots n, f (rootSlot n i) = ((base n).roots.map f).sum := by
  change ((Finset.univ : Finset (Slots n)).val.map (fun i : Slots n => f (i : ℂ))).sum = _
  rw [Multiset.map_univ]

theorem parent_actual_root_law (n : ℕ) (f : ℂ → ℝ) :
    ∑ i : Option (Slots n), parentMass i * f (point (rootSlot n) i) =
      empiricalExpectation (source n) f := by
  simp only [Fintype.sum_option, parentMass, point, zero_mul, zero_add]
  rw [← Finset.mul_sum, slot_sum_map]
  simp only [empiricalExpectation, source_roots, Multiset.map_nsmul, Multiset.sum_nsmul,
    source_degree, nsmul_eq_mul]
  rw [slots_card]
  push_cast
  field_simp

theorem child_actual_root_law (n : ℕ) (f : ℂ → ℝ) :
    ∑ i : Option (Slots n), childMass (epsilon n) i * f (point (rootSlot n) i) =
      empiricalExpectation (normalizedChild n) f := by
  simp only [Fintype.sum_option, childMass, point]
  rw [← Finset.mul_sum, slot_sum_map]
  simp only [empiricalExpectation, child_roots, Multiset.map_add, Multiset.map_nsmul,
    Multiset.map_singleton, Multiset.sum_add, Multiset.sum_nsmul, Multiset.sum_singleton,
    child_degree, nsmul_eq_mul]
  rw [slots_card]
  have hd : 1 ≤ 16*(n+2) := by omega
  rw [Nat.cast_sub hd]
  push_cast
  unfold epsilon
  ring_nf
  field_simp
  ring

theorem epsilon_bounds (n : ℕ) : 0 < epsilon n ∧ epsilon n < 1/16 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden : (0 : ℝ) < 16*(n+2)-1 := by nlinarith
  unfold epsilon
  constructor
  · positivity
  · apply (div_lt_iff₀ hden).mpr
    linarith

theorem family_W1_exact (n : ℕ) : optimalW1 (rootSlot n) (epsilon n) = epsilon n := by
  apply optimalW1_exact (rootSlot n) (slot_norm n) (epsilon n) (epsilon_bounds n).1.le
  linarith [(epsilon_bounds n).2]

theorem parentGini_eq (n : ℕ) : parentGini n = uniformGini n := by
  have h := parent_gini (rootSlot n)
  simpa only [parentGini, childGini, uniformGini, slots_card, Nat.cast_add, Nat.cast_ofNat] using h

theorem childGini_eq (n : ℕ) : childGini n =
    (1-epsilon n)^2*uniformGini n + 2*epsilon n*(1-epsilon n) := by
  have h := child_gini (rootSlot n) (slot_norm n) (epsilon n)
  simpa only [parentGini, childGini, uniformGini, slots_card, Nat.cast_add, Nat.cast_ofNat] using h

theorem uniformGini_bound (n : ℕ) : uniformGini n ≤ Real.sqrt 2 := by
  have hs : (∑ i : Slots n, (1/(n+2 : ℝ))) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [slots_card]
    push_cast
    field_simp
  have h := finite_gini_disk_bound (fun _ : Slots n => (1/(n+2 : ℝ))) (rootSlot n)
    (fun _ => by positivity) hs 0 0 1 (by norm_num) (uniform_mean n)
    (fun i => by simpa [rootSlot, slot_norm] using le_of_eq (slot_norm n i))
  simpa [uniformGini] using h

theorem uniformGini_strict_bound (n : ℕ) : uniformGini n < 17/12 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith [uniformGini_bound n]

theorem excess_exact (n : ℕ) :
    optimalW1 (rootSlot n) (epsilon n) - (parentGini n-childGini n) =
      epsilon n * ((3-2*epsilon n)-(2-epsilon n)*uniformGini n) := by
  rw [family_W1_exact, parentGini_eq, childGini_eq]
  ring

theorem excess_lower_bound (n : ℕ) : epsilon n/24 <
    optimalW1 (rootSlot n) (epsilon n) - (parentGini n-childGini n) := by
  have hε := epsilon_bounds n
  have hm := mul_lt_mul_of_pos_left (uniformGini_strict_bound n)
    (by linarith : 0 < 2-epsilon n)
  have hbr : (1/24 : ℝ) < (3-2*epsilon n)-(2-epsilon n)*uniformGini n := by
    nlinarith [hε.2]
  rw [excess_exact]
  calc
    epsilon n/24 = epsilon n*(1/24) := by ring
    _ < _ := mul_lt_mul_of_pos_left hbr hε.1

theorem candidateB_forces_growth (n : ℕ) (C : ℝ)
    (hC : optimalW1 (rootSlot n) (epsilon n) ≤ parentGini n-childGini n +
      C/(source n).natDegree) : (n+1 : ℝ)/24 < C := by
  have hm : (0 : ℝ) < 16*(n+2) := by positivity
  have hd : (0 : ℝ) < 16*(n+2)-1 := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hnum : (n+1 : ℝ) < (16*(n+2))*epsilon n := by
    unfold epsilon
    rw [← mul_div_assoc]
    apply (lt_div_iff₀ hd).mpr
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hl := excess_lower_bound n
  rw [source_degree] at hC
  push_cast at hC
  have hdiv : epsilon n/24 < C/(16*(n+2)) := by linarith
  have hmul := (lt_div_iff₀ hm).mp hdiv
  nlinarith

theorem no_finite_candidateB_constant (C : ℝ) : ∃ n : ℕ,
    parentGini n-childGini n + C/(source n).natDegree < optimalW1 (rootSlot n) (epsilon n) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (24*C)
  refine ⟨n, ?_⟩
  by_contra h
  have hg := candidateB_forces_growth n C (le_of_not_gt h)
  nlinarith



theorem source_roots_sum (n : ℕ) : (source n).roots.sum = 0 := by
  simp [source_roots, Multiset.sum_nsmul, base_roots_sum]

theorem source_variance (n : ℕ) : empiricalVariance (source n) = 1 := by
  rw [empiricalVariance, source_roots_sum, zero_div]
  rw [← parent_actual_root_law]
  simp only [Fintype.sum_option, parentMass, point, zero_mul, zero_add]
  have hv := uniform_variance n
  simpa only [rootSlot, slots_card, Nat.cast_add, Nat.cast_ofNat] using hv

theorem actual_family_refutes_candidateB (C : ℝ) : ∃ n : ℕ,
    parentGini n-childGini n + C*Real.sqrt (empiricalVariance (source n))/(source n).natDegree <
      optimalW1 (rootSlot n) (epsilon n) := by
  simpa only [source_variance, Real.sqrt_one, mul_one] using no_finite_candidateB_constant C



theorem parentGini_actual (n : ℕ) : parentGini n = empiricalGini (source n) := by
  unfold empiricalGini
  rw [← parent_actual_root_law n (fun x => empiricalExpectation (source n) (fun y => ‖x-y‖))]
  unfold parentGini finiteGini
  apply Finset.sum_congr rfl
  intro i _
  rw [← parent_actual_root_law n (fun y => ‖point (rootSlot n) i-y‖), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem childGini_actual (n : ℕ) : childGini n = empiricalGini (normalizedChild n) := by
  unfold empiricalGini
  rw [← child_actual_root_law n (fun x => empiricalExpectation (normalizedChild n) (fun y => ‖x-y‖))]
  unfold childGini finiteGini
  apply Finset.sum_congr rfl
  intro i _
  rw [← child_actual_root_law n (fun y => ‖point (rootSlot n) i-y‖), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem actual_normalized_derivative (n : ℕ) :
    C ((16*(n+2) : ℂ)⁻¹)*(source n).derivative = normalizedChild n := by
  have hn : (16*(n+2) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 16*(n+2) ≠ 0)
  rw [source_derivative, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hn, map_one, one_mul]

theorem actual_empirical_family_refutes_candidateB (C : ℝ) : ∃ n : ℕ,
    empiricalGini (source n)-empiricalGini (normalizedChild n) +
      C*Real.sqrt (empiricalVariance (source n))/(source n).natDegree <
        optimalW1 (rootSlot n) (epsilon n) := by
  simpa only [← parentGini_actual, ← childGini_actual] using actual_family_refutes_candidateB C



end
end DerivativeChainGiniFamily


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainContinuation
open DerivativeChainGiniFamily























































theorem solution (C : ℝ) : ∃ n : ℕ,
    source n = (X^(n+2)-1 : ℂ[X])^16 ∧ (source n).Monic ∧
    (source n).natDegree = 16*(n+2) ∧
    Polynomial.C ((16*(n+2) : ℂ)⁻¹)*(source n).derivative =
      X^(n+1)*(X^(n+2)-1)^15 ∧
    (∀ f : ℂ → ℝ, (∑ i : Option (Slots n), parentMass i*f (point (rootSlot n) i)) =
      empiricalExpectation (source n) f) ∧
    (∀ f : ℂ → ℝ, (∑ i : Option (Slots n), childMass (epsilon n) i*f (point (rootSlot n) i)) =
      empiricalExpectation (normalizedChild n) f) ∧
    empiricalVariance (source n) = 1 ∧
    optimalW1 (rootSlot n) (epsilon n) = epsilon n ∧
    empiricalGini (source n)-empiricalGini (normalizedChild n) +
      C*Real.sqrt (empiricalVariance (source n))/(source n).natDegree <
        optimalW1 (rootSlot n) (epsilon n) := by
  obtain ⟨n, hn⟩ := actual_empirical_family_refutes_candidateB C
  refine ⟨n, rfl, ?_, source_degree n, ?_, parent_actual_root_law n,
    child_actual_root_law n, source_variance n, family_W1_exact n, hn⟩
  · simpa only [source] using (base_monic n).pow 16
  · simpa only [normalizedChild, base] using actual_normalized_derivative n
