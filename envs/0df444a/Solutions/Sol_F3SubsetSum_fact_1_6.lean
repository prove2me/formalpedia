-- Prove2me | solution 1 for F3SubsetSum.fact_1_6
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T22:19:59.572196+00:00
-- url     : https://prove2.me/submissions/1799cf54-52e7-4274-9f49-4fb2648525b4

import Definitions.Def_F3SubsetSum_BinaryErrorLWE
import Definitions.Def_F3SubsetSum_QuotientAlgebra
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open F3SubsetSum MvPolynomial Matrix
open scoped BigOperators

namespace Fact16Proof

/- Two finite counting bounds imply both uniqueness thresholds. Translation of the secret and
independent sign changes of the matrix columns show that the uniqueness probability is the same
for all planted secrets and binary errors. A union bound controls competing secrets. Counting
unique secret-error representations controls the low-sample regime. -/

section
variable {q n m : ℕ} [Fact q.Prime]

private lemma matrix_card : Fintype.card (Matrix (Fin n) (Fin m) (ZMod q)) = q ^ (n * m) := by
  calc
    _ = Fintype.card (Fin n → Fin m → ZMod q) :=
      (Fintype.card_congr (Matrix.of : (Fin n → Fin m → ZMod q) ≃ _)).symm
    _ = _ := by
      simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
      rw [← pow_mul, Nat.mul_comm m n]

private lemma eval_lin (A : Matrix (Fin n) (Fin m) (ZMod q)) (u : Fin n → ZMod q) (i : Fin m) :
    eval u (linForm (cols A i)) = (Aᵀ *ᵥ u) i := by
  simp [linForm, cols, Matrix.mulVec, dotProduct]

private lemma candidate_iff (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (u : Fin n → ZMod q) :
    u ∈ candidates A b ↔ ∃ e : Fin m → Bool, lweSample A u e = b := by
  classical
  have hi (i : Fin m) : eval u (fPoly A b i) = 0 ↔
      ∃ e : Bool, (Aᵀ *ᵥ u) i + (if e then 1 else 0) = b i := by
    simp only [fPoly, map_mul, map_add, map_sub, map_one, eval_C, eval_lin,
      mul_eq_zero, sub_eq_zero]
    constructor
    · rintro (h | h)
      · exact ⟨false, by simpa using h⟩
      · refine ⟨true, ?_⟩
        simp only [if_true]
        linear_combination h
    · rintro ⟨e, he⟩
      cases e
      · exact Or.inl (by simpa using he)
      · exact Or.inr (by simp only [if_true] at he; linear_combination he)
  constructor
  · intro hu
    choose e he using fun i => (hi i).mp (hu i)
    exact ⟨e, funext he⟩
  · rintro ⟨e, he⟩ i
    exact (hi i).mpr ⟨e i, congrFun he i⟩

private lemma planted_mem (A : Matrix (Fin n) (Fin m) (ZMod q))
    (s : Fin n → ZMod q) (e : Fin m → Bool) :
    s ∈ candidates A (lweSample A s e) :=
  (candidate_iff A _ s).mpr ⟨e, rfl⟩

private def Good (A : Matrix (Fin n) (Fin m) (ZMod q))
    (s : Fin n → ZMod q) (e : Fin m → Bool) : Prop :=
  candidates A (lweSample A s e) = {s}

private lemma good_iff (A : Matrix (Fin n) (Fin m) (ZMod q))
    (s : Fin n → ZMod q) (e : Fin m → Bool) :
    Good A s e ↔ ∀ t f, lweSample A t f = lweSample A s e → t = s := by
  constructor
  · intro h t f he
    have ht := (candidate_iff A _ t).mpr ⟨f, he⟩
    change candidates A (lweSample A s e) = {s} at h
    simpa only [h, Set.mem_singleton_iff] using ht
  · intro h
    apply Set.ext
    intro t
    constructor
    · rintro ht
      obtain ⟨f, hf⟩ := (candidate_iff A _ t).mp ht
      exact h t f hf
    · intro ht
      have ht' : t = s := ht
      subst t
      exact planted_mem A s e

private lemma sample_sub (A : Matrix (Fin n) (Fin m) (ZMod q))
    (u s : Fin n → ZMod q) (e f : Fin m → Bool) :
    lweSample A u f = lweSample A s e ↔
      lweSample A (u - s) f = lweSample A 0 e := by
  simp only [lweSample, Matrix.mulVec_sub, Matrix.mulVec_zero, zero_add]
  constructor <;> intro h <;> linear_combination h

private lemma good_shift (A : Matrix (Fin n) (Fin m) (ZMod q))
    (s : Fin n → ZMod q) (e : Fin m → Bool) :
    Good A s e ↔ Good A 0 e := by
  rw [good_iff, good_iff]
  constructor
  · intro h u f hu
    have hh : lweSample A (u + s) f = lweSample A s e := by
      apply (sample_sub A (u + s) s e f).mpr
      simpa only [add_sub_cancel_right] using hu
    exact add_right_cancel (by simpa using h _ f hh : u + s = 0 + s)
  · intro h u f hu
    exact sub_eq_zero.mp (h (u - s) f ((sample_sub A u s e f).mp hu))

private def flip (e : Fin m → Bool) (A : Matrix (Fin n) (Fin m) (ZMod q)) :
    Matrix (Fin n) (Fin m) (ZMod q) :=
  fun j i => if e i then -A j i else A j i

private lemma flip_flip (e : Fin m → Bool) (A : Matrix (Fin n) (Fin m) (ZMod q)) :
    flip e (flip e A) = A := by
  ext j i
  cases hi : e i <;> simp [flip, hi]

private def flipEquiv (e : Fin m → Bool) :
    Equiv.Perm (Matrix (Fin n) (Fin m) (ZMod q)) where
  toFun := flip e
  invFun := flip e
  left_inv := flip_flip e
  right_inv := flip_flip e

private lemma flip_mulVec (e : Fin m → Bool) (A : Matrix (Fin n) (Fin m) (ZMod q))
    (u : Fin n → ZMod q) (i : Fin m) :
    ((flip e A)ᵀ *ᵥ u) i = if e i then -(Aᵀ *ᵥ u) i else (Aᵀ *ᵥ u) i := by
  cases hi : e i <;> simp [flip, Matrix.mulVec, dotProduct, hi, neg_mul]

private lemma flip_sample (e : Fin m → Bool) (A : Matrix (Fin n) (Fin m) (ZMod q))
    (u : Fin n → ZMod q) (f : Fin m → Bool) :
    lweSample A u f = lweSample A 0 e ↔
      lweSample (flip e A) u (fun i => Bool.xor (e i) (f i)) =
        lweSample (flip e A) 0 (fun _ => false) := by
  simp only [funext_iff, lweSample, Pi.add_apply, Matrix.mulVec_zero,
    zero_add, binVec, flip_mulVec]
  apply forall_congr'
  intro i
  have scalar (x : ZMod q) (c d : Bool) :
      (x + (if d then 1 else 0) = (if c then 1 else 0)) ↔
        ((if c then -x else x) + (if Bool.xor c d then 1 else 0)) = 0 := by
    cases c <;> cases d <;> simp
    constructor <;> intro h
    · linear_combination -h
    · linear_combination -h
  simpa using scalar ((Aᵀ *ᵥ u) i) (e i) (f i)

private lemma good_flip (e : Fin m → Bool) (A : Matrix (Fin n) (Fin m) (ZMod q)) :
    Good A 0 e ↔ Good (flip e A) 0 (fun _ => false) := by
  rw [good_iff, good_iff]
  constructor
  · intro h u f hf
    have hf' := (flip_sample e A u (fun i => Bool.xor (e i) (f i))).mpr (by simpa using hf)
    exact h u _ hf'
  · intro h u f hf
    exact h u _ ((flip_sample e A u f).mp hf)

open Classical in
private noncomputable def goodCount (s : Fin n → ZMod q) (e : Fin m → Bool) : ℕ :=
  (Finset.univ.filter fun A => Good A s e).card

private lemma goodCount_eq (s : Fin n → ZMod q) (e : Fin m → Bool) :
    goodCount s e = goodCount (0 : Fin n → ZMod q) (fun _ : Fin m => false) := by
  classical
  have h (A : Matrix (Fin n) (Fin m) (ZMod q)) :
      Good A s e ↔ Good ((flipEquiv e) A) 0 (fun _ => false) :=
    (good_shift A s e).trans (good_flip e A)
  unfold goodCount
  apply Finset.card_equiv (flipEquiv (q := q) (n := n) e)
  intro A
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h A

private lemma binVec_injective : Function.Injective (binVec q (m := m)) := by
  have hb : Function.Injective (fun c : Bool => (if c then 1 else 0 : ZMod q)) := by
    intro c d
    cases c <;> cases d <;> simp
  intro e f h
  funext i
  exact hb (congrFun h i)

private lemma sample_error_injective (A : Matrix (Fin n) (Fin m) (ZMod q))
    (s : Fin n → ZMod q) : Function.Injective (lweSample A s) := by
  intro e f h
  exact binVec_injective (add_left_cancel h)

-- Every sample vector has at most one representation whose secret is uniquely determined.
private lemma count_bound_low (s : Fin n → ZMod q) (e : Fin m → Bool) :
    q ^ n * 2 ^ m * goodCount s e ≤ q ^ (n * m) * q ^ m := by
  classical
  let D := Σ t : Fin n → ZMod q, Σ f : Fin m → Bool,
    {A : Matrix (Fin n) (Fin m) (ZMod q) // Good A t f}
  let out : D → Matrix (Fin n) (Fin m) (ZMod q) × (Fin m → ZMod q) :=
    fun x => (x.2.2.val, lweSample x.2.2.val x.1 x.2.1)
  have hinj : Function.Injective out := by
    rintro ⟨t, f, A, hA⟩ ⟨t', f', A', hA'⟩ h
    change (A, lweSample A t f) = (A', lweSample A' t' f') at h
    have hM : A = A' := congrArg Prod.fst h
    subst A'
    have hb : lweSample A t f = lweSample A t' f' := congrArg Prod.snd h
    have ht := (good_iff A t f).mp hA t' f' hb.symm
    subst t'
    have hf := sample_error_injective A t hb
    subst f'
    rfl
  have hcount (t : Fin n → ZMod q) (f : Fin m → Bool) :
      goodCount t f = goodCount s e :=
    (goodCount_eq t f).trans (goodCount_eq s e).symm
  have hD : Fintype.card D = q ^ n * 2 ^ m * goodCount s e := by
    dsimp only [D]
    simp only [Fintype.card_sigma, Fintype.card_subtype]
    change (∑ t : Fin n → ZMod q, ∑ f : Fin m → Bool, goodCount t f) = _
    simp_rw [hcount]
    simp [ZMod.card, mul_assoc]
  have h := Fintype.card_le_of_injective out hinj
  rw [hD] at h
  have hcod : Fintype.card (Matrix (Fin n) (Fin m) (ZMod q) × (Fin m → ZMod q)) =
      q ^ (n * m) * q ^ m := by
    rw [Fintype.card_prod, matrix_card]
    simp
  rw [hcod] at h
  exact h

end

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
variable {q n m : ℕ} [Fact q.Prime]

private def columnEval (u : Fin n → ZMod q) :
    Matrix (Fin n) (Fin m) (ZMod q) →+ (Fin m → ZMod q) where
  toFun A := Aᵀ *ᵥ u
  map_zero' := by simp
  map_add' A B := by simp [Matrix.transpose_add, Matrix.add_mulVec]

private lemma columnEval_surjective (u : Fin n → ZMod q) (hu : u ≠ 0) :
    Function.Surjective (columnEval (m := m) u) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hu
  intro v
  refine ⟨Matrix.of (fun k i => if k = j then v i / u j else 0), ?_⟩
  ext i
  change ∑ x, (if x = j then v i / u j else 0) * u x = v i
  simp [ite_mul, hj]

open Classical in
private noncomputable def allowed (e : Fin m → Bool) : Finset (Fin m → ZMod q) :=
  Finset.univ.image fun f : Fin m → Bool => binVec q e - binVec q f

private lemma allowed_card (e : Fin m → Bool) : (allowed (q := q) e).card = 2 ^ m := by
  classical
  rw [allowed, Finset.card_image_of_injective]
  · simp
  · intro f g h
    exact binVec_injective (sub_right_injective h)

private lemma mem_allowed (e : Fin m → Bool) (A : Matrix (Fin n) (Fin m) (ZMod q))
    (u : Fin n → ZMod q) :
    columnEval u A ∈ allowed (q := q) e ↔
      ∃ f, lweSample A u f = lweSample A 0 e := by
  classical
  simp only [allowed, Finset.mem_image, Finset.mem_univ, true_and]
  apply exists_congr
  intro f
  simp only [columnEval, AddMonoidHom.coe_mk, ZeroHom.coe_mk, lweSample, Matrix.mulVec_zero, zero_add]
  change binVec q e - binVec q f = Aᵀ *ᵥ u ↔
    Aᵀ *ᵥ u + binVec q f = binVec q e
  constructor <;> intro h <;> first | linear_combination h | linear_combination -h


open Classical in
private noncomputable def badSet (e : Fin m → Bool) :
    Finset (Matrix (Fin n) (Fin m) (ZMod q)) :=
  Finset.univ.filter fun A => ¬ Good A 0 e

private lemma card_badSet_bound (e : Fin m → Bool) :
    (badSet (q := q) (n := n) e).card * q ^ m ≤ q ^ n * 2 ^ m * q ^ (n * m) := by
  classical
  let U : Finset (Fin n → ZMod q) := Finset.univ.erase 0
  let B : (Fin n → ZMod q) → Finset (Matrix (Fin n) (Fin m) (ZMod q)) :=
    fun u => Finset.univ.filter fun A => columnEval u A ∈ allowed (q := q) e
  have hsub : badSet (q := q) (n := n) e ⊆ U.biUnion B := by
    intro A hA
    have hb : ¬ Good A 0 e := (Finset.mem_filter.mp hA).2
    obtain ⟨u, f, hf, hu⟩ : ∃ u f,
        lweSample A u f = lweSample A 0 e ∧ u ≠ 0 := by
      simpa only [good_iff, not_forall, Classical.not_imp, exists_prop] using hb
    exact Finset.mem_biUnion.mpr
      ⟨u, Finset.mem_erase.mpr ⟨hu, Finset.mem_univ _⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_allowed e A u).mpr ⟨f, hf⟩⟩⟩
  have hfiber (u : Fin n → ZMod q) (hu : u ∈ U) :
      (B u).card * q ^ m = 2 ^ m * q ^ (n * m) := by
    have h := uniform_preimage_card
      (G := Matrix (Fin n) (Fin m) (ZMod q)) (H := Fin m → ZMod q) (columnEval (m := m) u)
      (columnEval_surjective u (Finset.mem_erase.mp hu).1) (allowed (q := q) e)
    simp only [allowed_card, Fintype.card_fun, Fintype.card_fin, ZMod.card, matrix_card] at h
    convert h using 2
    congr 1
    ext A
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
  have hU : U.card ≤ q ^ n := by
    have h := Finset.card_le_card (Finset.erase_subset (0 : Fin n → ZMod q) Finset.univ)
    simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card] using h
  calc
    (badSet (q := q) (n := n) e).card * q ^ m ≤ (U.biUnion B).card * q ^ m :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ (∑ u ∈ U, (B u).card) * q ^ m := Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ u ∈ U, (B u).card * q ^ m := by rw [Finset.sum_mul]
    _ = ∑ u ∈ U, 2 ^ m * q ^ (n * m) := Finset.sum_congr rfl hfiber
    _ = U.card * (2 ^ m * q ^ (n * m)) := by simp
    _ ≤ _ := by
      simpa only [mul_assoc] using Nat.mul_le_mul_right (2 ^ m * q ^ (n * m)) hU

private lemma good_add_bad (e : Fin m → Bool) :
    goodCount (0 : Fin n → ZMod q) e + (badSet (q := q) (n := n) e).card =
      q ^ (n * m) := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Matrix (Fin n) (Fin m) (ZMod q)))) (fun A => Good A 0 e)
  simpa only [goodCount, badSet, Finset.card_univ, matrix_card] using h

private noncomputable def uniqueProb (s : Fin n → ZMod q) (e : Fin m → Bool) : ℝ :=
  (goodCount s e : ℝ) / (q : ℝ) ^ (n * m)

private lemma prob_low_bound (s : Fin n → ZMod q) (e : Fin m → Bool) :
    uniqueProb s e ≤ (q : ℝ) ^ m / ((q : ℝ) ^ n * (2 : ℝ) ^ m) := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
  have h := count_bound_low s e
  have hr : (q : ℝ) ^ n * (2 : ℝ) ^ m * (goodCount s e : ℝ) ≤
      (q : ℝ) ^ (n * m) * (q : ℝ) ^ m := by exact_mod_cast h
  apply (div_le_div_iff₀ (by positivity : 0 < (q : ℝ) ^ (n * m))
    (by positivity : 0 < (q : ℝ) ^ n * (2 : ℝ) ^ m)).mpr
  nlinarith

private lemma prob_high_bound (s : Fin n → ZMod q) (e : Fin m → Bool) :
    1 - (q : ℝ) ^ n * (2 : ℝ) ^ m / (q : ℝ) ^ m ≤ uniqueProb s e := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
  have h := card_badSet_bound (q := q) (n := n) e
  have hc := good_add_bad (q := q) (n := n) e
  have hc' : (goodCount (0 : Fin n → ZMod q) e : ℝ) +
      ((badSet (q := q) (n := n) e).card : ℝ) = (q : ℝ) ^ (n * m) := by exact_mod_cast hc
  have hb : ((badSet (q := q) (n := n) e).card : ℝ) * (q : ℝ) ^ m ≤
      (q : ℝ) ^ n * (2 : ℝ) ^ m * (q : ℝ) ^ (n * m) := by exact_mod_cast h
  have heq : goodCount s e = goodCount (0 : Fin n → ZMod q) e :=
    (goodCount_eq s e).trans (goodCount_eq (0 : Fin n → ZMod q) e).symm
  unfold uniqueProb
  rw [heq]
  apply (le_div_iff₀ (by positivity : 0 < (q : ℝ) ^ (n * m))).mpr
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < (q : ℝ) ^ m)).mp
  field_simp
  have hcMul := congrArg (fun x : ℝ => x * (q : ℝ) ^ m) hc'
  nlinarith only [hcMul, hb]
end

private lemma nat_pow_exp (a : ℝ) (ha : 0 < a) (k : ℕ) :
    a ^ k = Real.exp (Real.log a * k) := by
  rw [← Real.rpow_natCast a k, Real.rpow_def_of_pos ha]

-- A common positive exponent works on both sides of the threshold, for every dimension.
private lemma threshold_exponents (a η : ℝ) (ha : 2 < a) (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ ∀ n m : ℕ,
      ((Real.logb (a / 2) a + η) * n ≤ m →
        a ^ n * (2 : ℝ) ^ m / a ^ m ≤ (2 : ℝ) ^ (-(c * m))) ∧
      ((m : ℝ) ≤ (Real.logb (a / 2) a - η) * n →
        a ^ m / (a ^ n * (2 : ℝ) ^ m) ≤ (2 : ℝ) ^ (-(c * n))) := by
  let L := Real.log (a / 2)
  let k := Real.logb (a / 2) a
  let R := k + η + 1
  let c := η * L / (R * Real.log 2)
  have ha0 : 0 < a := by linarith
  have hL : 0 < L := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk : 0 < k := by
    dsimp only [k, Real.logb]
    exact div_pos (Real.log_pos (by linarith)) hL
  have hR : 0 < R := by dsimp only [R]; positivity
  have hR1 : 1 ≤ R := by dsimp only [R]; linarith
  have hc : 0 < c := by dsimp only [c]; positivity
  have hkL : k * L = Real.log a := by
    dsimp only [k, L, Real.logb]
    exact div_mul_cancel₀ _ hL.ne'
  have hcL : c * Real.log 2 * R = η * L := by
    dsimp only [c]
    field_simp
  have hcsmall : c * Real.log 2 ≤ η * L := by
    have h := mul_le_mul_of_nonneg_left hR1 (mul_nonneg hc.le hlog2.le)
    simpa only [mul_one, hcL] using h
  have h2log : Real.log 2 = (k - 1) * L := by
    have h : L = Real.log a - Real.log 2 := Real.log_div ha0.ne' (by norm_num)
    nlinarith only [h, hkL]
  have highExp (n m : ℕ) :
      a ^ n * (2 : ℝ) ^ m / a ^ m = Real.exp (L * (k * n - m)) := by
    rw [nat_pow_exp a ha0 n, nat_pow_exp 2 (by norm_num) m, nat_pow_exp a ha0 m,
      ← Real.exp_add, ← Real.exp_sub]
    congr 1
    rw [← hkL, h2log]
    ring
  have lowExp (n m : ℕ) :
      a ^ m / (a ^ n * (2 : ℝ) ^ m) = Real.exp (L * (m - k * n)) := by
    rw [nat_pow_exp a ha0 m, nat_pow_exp a ha0 n, nat_pow_exp 2 (by norm_num) m,
      ← Real.exp_add, ← Real.exp_sub]
    congr 1
    rw [← hkL, h2log]
    ring
  refine ⟨c, hc, fun n m => ⟨?_, ?_⟩⟩
  · intro hm
    change (k + η) * (n : ℝ) ≤ m at hm
    have hmargin : η * (m : ℝ) ≤ R * ((m : ℝ) - k * n) := by
      have h := mul_nonneg (show 0 ≤ k + 1 by linarith) (sub_nonneg.mpr hm)
      have hηn := mul_nonneg hη.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      dsimp only [R]
      nlinarith only [h, hηn]
    have hmarginL := mul_le_mul_of_nonneg_right hmargin hL.le
    have hdiff : c * Real.log 2 * (m : ℝ) ≤ L * ((m : ℝ) - k * n) := by
      apply (mul_le_mul_iff_left₀ hR).mp
      calc
        c * Real.log 2 * (m : ℝ) * R = (c * Real.log 2 * R) * m := by ring
        _ = η * L * m := by rw [hcL]
        _ ≤ (R * ((m : ℝ) - k * n)) * L := by
          nlinarith only [hmarginL]
        _ = L * ((m : ℝ) - k * n) * R := by ring
    rw [highExp, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    nlinarith only [hdiff]
  · intro hm
    change (m : ℝ) ≤ (k - η) * n at hm
    have hmul := mul_le_mul_of_nonneg_left hm hL.le
    have hcn := mul_le_mul_of_nonneg_right hcsmall (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    rw [lowExp, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    nlinarith only [hmul, hcn]

end Fact16Proof

open Fact16Proof

open Classical in
theorem solution (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (η : ℝ) (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n m : ℕ) (s : Fin n → ZMod q) (e : Fin m → Bool),
      ((Real.logb ((q : ℝ) / 2) q + η) * n ≤ m →
        1 - (2 : ℝ) ^ (-(c * m)) ≤
          ((Finset.univ.filter fun A : Matrix (Fin n) (Fin m) (ZMod q) =>
            candidates A (lweSample A s e) = {s}).card : ℝ) / (q : ℝ) ^ (n * m)) ∧
      ((m : ℝ) ≤ (Real.logb ((q : ℝ) / 2) q - η) * n →
        ((Finset.univ.filter fun A : Matrix (Fin n) (Fin m) (ZMod q) =>
            candidates A (lweSample A s e) = {s}).card : ℝ) / (q : ℝ) ^ (n * m) ≤
          (2 : ℝ) ^ (-(c * n))) := by
  have hq' : (2 : ℝ) < q := by exact_mod_cast (show 2 < q by omega)
  obtain ⟨c, hc, htail⟩ := threshold_exponents (q : ℝ) η hq' hη
  refine ⟨c, hc, fun n m s e => ⟨?_, ?_⟩⟩
  · intro hm
    have h := prob_high_bound s e
    have ht := (htail n m).1 hm
    change 1 - (2 : ℝ) ^ (-(c * m)) ≤ uniqueProb s e
    linarith
  · intro hm
    exact (prob_low_bound s e).trans ((htail n m).2 hm)
