-- Prove2me | solution 1 for F3SubsetSum.fact_1_2
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T22:39:02.76659+00:00
-- url     : https://prove2.me/submissions/78614c07-c9fd-43e9-86c0-365dc5f0ed74

import Definitions.Def_F3SubsetSum_SubsetSum
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open F3SubsetSum MvPolynomial
open scoped BigOperators

namespace Fact12Proof

/- Chevalley–Warning gives the deterministic guarantee. For the probability bounds, a union
bound controls existence below the threshold, while counting uniquely represented binary vectors
controls failure above it. The common exponential constant can be chosen as c = η. -/

private theorem deterministic (n m : ℕ) (hm : 2 * n + 1 ≤ m)
    (h : Fin m → Fin n → ZMod 3) : HasZeroSubsetSum h := by
  classical
  let f : Fin n → MvPolynomial (Fin m) (ZMod 3) :=
    fun j => ∑ i, C (h i j) * X i ^ 2
  have hdeg (j : Fin n) : (f j).totalDegree ≤ 2 := by
    apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_mul _ _).trans (by simp [totalDegree_X_pow])
  have hsum : (∑ j, (f j).totalDegree) < Fintype.card (Fin m) := by
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hdeg j)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_id] at hh
    simp only [Fintype.card_fin]
    omega
  have hdiv0 := char_dvd_card_solutions_of_fintype_sum_lt 3 hsum
  have hdiv : 3 ∣ Fintype.card {x : Fin m → ZMod 3 // ∀ j, eval x (f j) = 0} := by
    convert hdiv0 using 1
    exact congrArg
      (fun inst : Fintype {x : Fin m → ZMod 3 // ∀ j, eval x (f j) = 0} =>
        @Fintype.card _ inst) (Subsingleton.elim _ _)
  by_contra hbad
  have hroot (x : Fin m → ZMod 3) (hx : ∀ j, eval x (f j) = 0) : x = 0 := by
    let S := Finset.univ.filter fun i => x i ≠ 0
    have hS : ∑ i ∈ S, h i = 0 := by
      ext j
      have hsquare : ∀ a : ZMod 3, a ^ 2 = if a = 0 then 0 else 1 := by decide
      have hh := hx j
      simp only [f, map_sum, map_mul, map_pow, eval_C, eval_X, hsquare] at hh
      simpa [S, Finset.sum_filter, mul_ite, ite_not] using hh
    by_contra hx0
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hx0
    apply hbad
    exact ⟨S, ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩, hS⟩⟩
  let E : {x : Fin m → ZMod 3 // ∀ j, eval x (f j) = 0} ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨0, by intro j; simp [f]⟩
      left_inv := fun x => Subtype.ext (hroot x.val x.property).symm
      right_inv := fun x => by cases x; rfl }
  have hc : Fintype.card {x : Fin m → ZMod 3 // ∀ j, eval x (f j) = 0} = 1 := by
    simpa only [Fintype.card_unit] using Fintype.card_congr E
  rw [hc] at hdiv
  norm_num at hdiv

section
variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]

-- A surjective homomorphism sends the uniform distribution to the uniform distribution.
open Classical in
private lemma uniform_preimage_card (f : G →+ H) (hf : Function.Surjective f) (S : Finset H) :
    (Finset.univ.filter fun x => f x ∈ S).card * Fintype.card H =
      S.card * Fintype.card G := by
  classical
  let N := (Finset.univ.filter fun x : G => f x = 0).card
  have hcard (y : H) : (Finset.univ.filter fun x => f x = y).card = N := by
    obtain ⟨d, hd⟩ := hf y
    symm
    apply Finset.card_equiv (Equiv.addRight d)
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_addRight, map_add, hd]
    simp
  have hfull : Fintype.card G = Fintype.card H * N := by
    have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset G)
      (Finset.univ : Finset H) f
    simpa only [hcard, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.mem_univ, Finset.filter_true, Nat.cast_id] using h.symm
  have hS : (Finset.univ.filter fun x => f x ∈ S).card = S.card * N := by
    have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset G) S f
    simpa only [hcard, Finset.sum_const, nsmul_eq_mul, Nat.cast_id] using h.symm
  rw [hS, hfull]
  ring
end


section
variable {n m : ℕ}

private def cubeSum (h : Fin m → Fin n → ZMod 3) (e : Fin m → Bool) :
    Fin n → ZMod 3 :=
  ∑ i, if e i then h i else 0

private def UniqueCode (h : Fin m → Fin n → ZMod 3) (e : Fin m → Bool) : Prop :=
  ∀ f, cubeSum h f = cubeSum h e → f = e

private lemma unique_zero (h : Fin m → Fin n → ZMod 3) :
    UniqueCode h (fun _ => false) ↔ ¬HasZeroSubsetSum h := by
  classical
  constructor
  · intro hu ⟨S, hS, hz⟩
    let e : Fin m → Bool := fun i => decide (i ∈ S)
    have he : cubeSum h e = cubeSum h (fun _ => false) := by
      simpa [cubeSum, e, Finset.sum_filter] using hz
    have he0 := hu e he
    obtain ⟨i, hi⟩ := hS
    have hh := congrFun he0 i
    simp [e, hi] at hh
  · intro hbad f hf
    by_contra hf0
    let S := Finset.univ.filter fun i => f i = true
    have hS : S.Nonempty := by
      obtain ⟨i, hi⟩ : ∃ i, f i ≠ false := by
        simpa only [ne_eq, funext_iff, not_forall] using hf0
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Bool.eq_true_of_not_eq_false hi⟩⟩
    apply hbad
    refine ⟨S, hS, ?_⟩
    simpa [S, cubeSum, Finset.sum_filter] using hf

private def signFlip (e : Fin m → Bool) (h : Fin m → Fin n → ZMod 3) :
    Fin m → Fin n → ZMod 3 :=
  fun i => if e i then -h i else h i

private lemma signFlip_twice (e : Fin m → Bool) (h : Fin m → Fin n → ZMod 3) :
    signFlip e (signFlip e h) = h := by
  funext i
  cases he : e i <;> simp [signFlip, he]

private def signEquiv (e : Fin m → Bool) :
    Equiv.Perm (Fin m → Fin n → ZMod 3) where
  toFun := signFlip e
  invFun := signFlip e
  left_inv := signFlip_twice e
  right_inv := signFlip_twice e

private lemma cubeSum_xor (e f : Fin m → Bool) (h : Fin m → Fin n → ZMod 3) :
    cubeSum (signFlip e h) (fun i => Bool.xor (e i) (f i)) =
      cubeSum h f - cubeSum h e := by
  classical
  simp only [cubeSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hs (a : Fin n → ZMod 3) (c d : Bool) :
      (if Bool.xor c d then (if c then -a else a) else 0) =
        (if d then a else 0) - (if c then a else 0) := by
    cases c <;> cases d <;> simp
  exact hs (h i) (e i) (f i)

private lemma unique_sign (e : Fin m → Bool) (h : Fin m → Fin n → ZMod 3) :
    UniqueCode h e ↔ UniqueCode (signFlip e h) (fun _ => false) := by
  constructor
  · intro hu f hf
    have hxor : cubeSum h (fun i => Bool.xor (e i) (f i)) = cubeSum h e := by
      have hx := cubeSum_xor e (fun i => Bool.xor (e i) (f i)) h
      simp only [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor] at hx
      have hh : cubeSum (signFlip e h) f = 0 := by simpa [cubeSum] using hf
      rw [hh] at hx
      exact sub_eq_zero.mp hx.symm
    have hfu := hu _ hxor
    funext i
    have hh := congrFun hfu i
    cases he : e i <;> cases hfi : f i <;> simp_all
  · intro hu f hf
    have hx := cubeSum_xor e f h
    rw [hf, sub_self] at hx
    have hh := hu (fun i => Bool.xor (e i) (f i)) (by simpa [cubeSum] using hx)
    funext i
    have hi := congrFun hh i
    cases he : e i <;> cases hfi : f i <;> simp_all

open Classical in
private noncomputable def failSet (n m : ℕ) : Finset (Fin m → Fin n → ZMod 3) :=
  Finset.univ.filter fun h => ¬HasZeroSubsetSum h

open Classical in
private lemma unique_count (e : Fin m → Bool) :
    (Finset.univ.filter fun h : Fin m → Fin n → ZMod 3 => UniqueCode h e).card =
      (failSet n m).card := by
  classical
  apply Finset.card_equiv (signEquiv e)
  intro h
  simp only [failSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (unique_sign e h).trans (unique_zero _)

-- Uniquely represented binary vectors inject into the range of their subset-sum map.
private lemma fail_count_bound :
    2 ^ m * (failSet n m).card ≤ 3 ^ (n * m) * 3 ^ n := by
  classical
  let D := Σ e : Fin m → Bool, {h : Fin m → Fin n → ZMod 3 // UniqueCode h e}
  let out : D → (Fin m → Fin n → ZMod 3) × (Fin n → ZMod 3) :=
    fun x => (x.2.val, cubeSum x.2.val x.1)
  have hinj : Function.Injective out := by
    rintro ⟨e, h, hh⟩ ⟨e', h', hh'⟩ heq
    change (h, cubeSum h e) = (h', cubeSum h' e') at heq
    have heqh : h = h' := congrArg Prod.fst heq
    subst h'
    have heqsum : cubeSum h e = cubeSum h e' := congrArg Prod.snd heq
    have he := hh e' heqsum.symm
    subst e'
    rfl
  have hD : Fintype.card D = 2 ^ m * (failSet n m).card := by
    dsimp only [D]
    simp only [Fintype.card_sigma, Fintype.card_subtype, unique_count, Finset.sum_const,
      Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_id]
  have hh := Fintype.card_le_of_injective out hinj
  rw [hD] at hh
  simpa [Fintype.card_prod, Fintype.card_fun, ZMod.card, pow_mul] using hh
end

section
variable {n m : ℕ}

private def subsetMap (S : Finset (Fin m)) :
    (Fin m → Fin n → ZMod 3) →+ (Fin n → ZMod 3) where
  toFun h := ∑ i ∈ S, h i
  map_zero' := by simp
  map_add' h g := by simp [Finset.sum_add_distrib]

private lemma subsetMap_surjective (S : Finset (Fin m)) (hS : S.Nonempty) :
    Function.Surjective (subsetMap (n := n) S) := by
  classical
  obtain ⟨i, hi⟩ := hS
  intro v
  refine ⟨fun j => if j = i then v else 0, ?_⟩
  simp [subsetMap, hi]

open Classical in
private noncomputable def solvedSet (n m : ℕ) : Finset (Fin m → Fin n → ZMod 3) :=
  Finset.univ.filter fun h => HasZeroSubsetSum h

private lemma solved_count_bound :
    (solvedSet n m).card * 3 ^ n ≤ 2 ^ m * 3 ^ (n * m) := by
  classical
  let U : Finset (Finset (Fin m)) := Finset.univ.filter Finset.Nonempty
  let B : Finset (Fin m) → Finset (Fin m → Fin n → ZMod 3) :=
    fun S => Finset.univ.filter fun h => subsetMap S h = 0
  have hsub : solvedSet n m ⊆ U.biUnion B := by
    intro h hh
    obtain ⟨S, hS, hz⟩ := (Finset.mem_filter.mp hh).2
    exact Finset.mem_biUnion.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩⟩
  have hfiber (S : Finset (Fin m)) (hS : S ∈ U) :
      (B S).card * 3 ^ n = 3 ^ (n * m) := by
    have hh := uniform_preimage_card (subsetMap (n := n) S)
      (subsetMap_surjective S (Finset.mem_filter.mp hS).2) {0}
    simpa only [B, Finset.mem_singleton, Finset.card_singleton, one_mul,
      Fintype.card_fun, Fintype.card_fin, ZMod.card, pow_mul] using hh
  have hU : U.card ≤ 2 ^ m := by
    have hh := Finset.card_le_card (Finset.filter_subset Finset.Nonempty
      (Finset.univ : Finset (Finset (Fin m))))
    simpa using hh
  calc
    (solvedSet n m).card * 3 ^ n ≤ (U.biUnion B).card * 3 ^ n :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ (∑ S ∈ U, (B S).card) * 3 ^ n := Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ S ∈ U, (B S).card * 3 ^ n := by rw [Finset.sum_mul]
    _ = ∑ S ∈ U, 3 ^ (n * m) := Finset.sum_congr rfl hfiber
    _ = U.card * 3 ^ (n * m) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hU

private lemma solved_add_fail :
    (solvedSet n m).card + (failSet n m).card = 3 ^ (n * m) := by
  classical
  have hh := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m → Fin n → ZMod 3))) HasZeroSubsetSum
  simpa [solvedSet, failSet, Fintype.card_fun, ZMod.card, pow_mul] using hh

private lemma probability_lower :
    1 - (3 : ℝ) ^ n / (2 : ℝ) ^ m ≤ probSolvable n m := by
  have hc : ((solvedSet n m).card : ℝ) + ((failSet n m).card : ℝ) =
      (3 : ℝ) ^ (n * m) := by exact_mod_cast (solved_add_fail (n := n) (m := m))
  have hb : (2 : ℝ) ^ m * ((failSet n m).card : ℝ) ≤
      (3 : ℝ) ^ (n * m) * (3 : ℝ) ^ n := by
    exact_mod_cast (fail_count_bound (n := n) (m := m))
  change 1 - (3 : ℝ) ^ n / (2 : ℝ) ^ m ≤
    ((solvedSet n m).card : ℝ) / (3 : ℝ) ^ (n * m)
  apply (le_div_iff₀ (by positivity : 0 < (3 : ℝ) ^ (n * m))).mpr
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < (2 : ℝ) ^ m)).mp
  field_simp
  have hcMul := congrArg (fun x : ℝ => x * (2 : ℝ) ^ m) hc
  nlinarith only [hcMul, hb]

private lemma probability_upper :
    probSolvable n m ≤ (2 : ℝ) ^ m / (3 : ℝ) ^ n := by
  have hb : ((solvedSet n m).card : ℝ) * (3 : ℝ) ^ n ≤
      (2 : ℝ) ^ m * (3 : ℝ) ^ (n * m) := by
    exact_mod_cast (solved_count_bound (n := n) (m := m))
  apply (div_le_div_iff₀ (by positivity : 0 < (3 : ℝ) ^ (n * m))
    (by positivity : 0 < (3 : ℝ) ^ n)).mpr
  exact hb
end

private lemma nat_pow_exp (a : ℝ) (ha : 0 < a) (k : ℕ) :
    a ^ k = Real.exp (Real.log a * k) := by
  rw [← Real.rpow_natCast a k, Real.rpow_def_of_pos ha]

private lemma threshold_bounds (η : ℝ) (n m : ℕ) :
    ((Real.logb 2 3 + η) * n ≤ m →
      (3 : ℝ) ^ n / (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (-(η * n))) ∧
    ((m : ℝ) ≤ (Real.logb 2 3 - η) * n →
      (2 : ℝ) ^ m / (3 : ℝ) ^ n ≤ (2 : ℝ) ^ (-(η * n))) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk : Real.logb 2 3 * Real.log 2 = Real.log 3 := by
    rw [Real.logb, div_mul_cancel₀ _ hlog2.ne']
  constructor
  · intro hm
    rw [nat_pow_exp 3 (by norm_num) n, nat_pow_exp 2 (by norm_num) m,
      ← Real.exp_sub, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hm hlog2.le
    rw [← hk]
    nlinarith only [hh]
  · intro hm
    rw [nat_pow_exp 2 (by norm_num) m, nat_pow_exp 3 (by norm_num) n,
      ← Real.exp_sub, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hm hlog2.le
    rw [← hk]
    nlinarith only [hh]

end Fact12Proof

open Fact12Proof

theorem solution :
    (∀ n m : ℕ, 2 * n + 1 ≤ m → ∀ h : Fin m → Fin n → ZMod 3, HasZeroSubsetSum h) ∧
    ∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧ ∀ n m : ℕ,
      ((Real.logb 2 3 + η) * n ≤ m → 1 - (2 : ℝ) ^ (-(c * n)) ≤ probSolvable n m) ∧
      ((m : ℝ) ≤ (Real.logb 2 3 - η) * n → probSolvable n m ≤ (2 : ℝ) ^ (-(c * n))) := by
  refine ⟨deterministic, ?_⟩
  intro η hη
  refine ⟨η, hη, fun n m => ⟨?_, ?_⟩⟩
  · intro hm
    have hb := probability_lower (n := n) (m := m)
    have ht := (threshold_bounds η n m).1 hm
    linarith
  · intro hm
    exact (probability_upper (n := n) (m := m)).trans ((threshold_bounds η n m).2 hm)
