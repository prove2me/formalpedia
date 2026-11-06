-- Prove2me | solution 1 for FuzzyGames.Values.monomials_dense
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T03:37:33.342315+00:00
-- url     : https://prove2.me/submissions/6a39d729-2ec7-4a2b-b8f8-267b5fa63de8

import Mathlib
import Definitions.Def_FuzzyGames_Values_Basic

open FuzzyGames.Values

namespace FuzzyDenseAux

open Finset

/-- The Bernstein basis function `C(m,k) t^k (1-t)^(m-k)`. -/
noncomputable def bb (m k : ℕ) (t : ℝ) : ℝ := (m.choose k : ℝ) * t ^ k * (1 - t) ^ (m - k)

lemma bb_eq_eval (m k : ℕ) (t : ℝ) : bb m k t = (bernsteinPolynomial ℝ m k).eval t := by
  simp [bb, bernsteinPolynomial]

lemma bb_nonneg (m k : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ bb m k t := by
  unfold bb
  have : 0 ≤ 1 - t := by linarith
  positivity

lemma bb_of_lt {m k : ℕ} (h : m < k) (t : ℝ) : bb m k t = 0 := by
  simp [bb, Nat.choose_eq_zero_of_lt h]

lemma bb_sum (m : ℕ) (t : ℝ) : ∑ k ∈ range (m + 1), bb m k t = 1 := by
  have := congrArg (Polynomial.eval t) (bernsteinPolynomial.sum ℝ m)
  simpa [Polynomial.eval_finset_sum, ← bb_eq_eval] using this

lemma bb_sum_le {m N : ℕ} (h : m ≤ N) (g : ℕ → ℝ) (t : ℝ) :
    ∑ k ∈ range (N + 1), bb m k t * g k = ∑ k ∈ range (m + 1), bb m k t * g k := by
  symm
  apply Finset.sum_subset
  · intro k hk; simp at hk ⊢; omega
  · intro k hk hk'
    simp at hk hk'
    rw [bb_of_lt (by omega), zero_mul]

lemma bb_sum' {m N : ℕ} (h : m ≤ N) (t : ℝ) : ∑ k ∈ range (N + 1), bb m k t = 1 := by
  have := bb_sum_le h (fun _ => 1) t
  simp only [mul_one] at this
  rw [this, bb_sum]

lemma bb_variance {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ∑ k ∈ range (m + 1), bb m k t * ((k : ℝ) / m - t) ^ 2 ≤ 1 / m := by
  have hv := congrArg (Polynomial.eval t) (bernsteinPolynomial.variance ℝ m)
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_smul, Polynomial.eval_X, Polynomial.eval_natCast,
    Polynomial.eval_one, nsmul_eq_mul, ← bb_eq_eval] at hv
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have key : ∑ k ∈ range (m + 1), bb m k t * ((k : ℝ) / m - t) ^ 2 =
      (∑ k ∈ range (m + 1), ((m : ℝ) * t - k) ^ 2 * bb m k t) / (m : ℝ) ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
    ring
  rw [key, hv]
  rw [div_le_div_iff₀ (by positivity) hmpos]
  have : t * (1 - t) ≤ 1 := by nlinarith
  nlinarith

lemma bb_hasDerivAt {m : ℕ} (hm : 1 ≤ m) (k : ℕ) (t : ℝ) :
    HasDerivAt (bb m k)
      ((m : ℝ) * ((if k = 0 then 0 else bb (m - 1) (k - 1) t) - bb (m - 1) k t)) t := by
  have hfun : bb m k = fun t => (bernsteinPolynomial ℝ m k).eval t := by
    funext t; exact bb_eq_eval m k t
  rw [hfun]
  have := (bernsteinPolynomial ℝ m k).hasDerivAt t
  refine this.congr_deriv ?_
  rcases k with _ | k
  · rw [bernsteinPolynomial.derivative_zero]
    simp [Polynomial.eval_mul, ← bb_eq_eval]
  · rw [bernsteinPolynomial.derivative_succ]
    simp [Polynomial.eval_mul, Polynomial.eval_sub, ← bb_eq_eval]


/-! ### Multivariate Bernstein weights -/

/-- The multi-index box `{0,…,m}^n`. -/
def J (n m : ℕ) : Finset (Fin n → ℕ) := Fintype.piFinset fun _ => range (m + 1)

/-- Product Bernstein weight with degrees `μ`. -/
noncomputable def W {n : ℕ} (μ : Fin n → ℕ) (j : Fin n → ℕ) (x : Fin n → ℝ) : ℝ :=
  ∏ l, bb (μ l) (j l) (x l)

lemma W_nonneg {n : ℕ} (μ j : Fin n → ℕ) {x : Fin n → ℝ}
    (hx : x ∈ FuzzyGames.NTUCore.cube n) : 0 ≤ W μ j x :=
  Finset.prod_nonneg fun l _ => bb_nonneg _ _ (hx.1 l) (hx.2 l)

lemma W_sum {n m : ℕ} (μ : Fin n → ℕ) (hμ : ∀ l, μ l ≤ m) (x : Fin n → ℝ) :
    ∑ j ∈ J n m, W μ j x = 1 := by
  unfold W J
  rw [← Finset.prod_univ_sum (fun _ => range (m + 1)) (fun l k => bb (μ l) k (x l))]
  exact Finset.prod_eq_one fun l _ => bb_sum' (hμ l) _

lemma W_sum_mul {n m : ℕ} (μ : Fin n → ℕ) (hμ : ∀ l, μ l ≤ m) (x : Fin n → ℝ) (l : Fin n)
    (h : ℕ → ℝ) :
    ∑ j ∈ J n m, W μ j x * h (j l) = ∑ k ∈ range (m + 1), bb (μ l) k (x l) * h k := by
  have e1 : ∀ j : Fin n → ℕ, W μ j x * h (j l) =
      ∏ l', bb (μ l') (j l') (x l') * (if l' = l then h (j l') else 1) := by
    intro j
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ l]
    simp [W]
  simp_rw [e1]
  unfold J
  rw [← Finset.prod_univ_sum (fun _ => range (m + 1))
    (fun l' k => bb (μ l') k (x l') * (if l' = l then h k else 1))]
  rw [Finset.prod_eq_single l]
  · simp
  · intro l' _ hl'
    simp only [hl', if_false, mul_one]
    exact bb_sum' (hμ l') _
  · intro h'; exact absurd (Finset.mem_univ _) h'

lemma W_var {n m : ℕ} (μ : Fin n → ℕ) (hμ : ∀ l, μ l ≤ m) (hμ1 : ∀ l, 1 ≤ μ l)
    {x : Fin n → ℝ} (hx : x ∈ FuzzyGames.NTUCore.cube n) :
    ∑ j ∈ J n m, W μ j x * ∑ l, ((j l : ℝ) / μ l - x l) ^ 2 ≤ ∑ l, 1 / (μ l : ℝ) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [W_sum_mul μ hμ x l (fun k => ((k : ℝ) / μ l - x l) ^ 2),
    bb_sum_le (hμ l) (fun k => ((k : ℝ) / μ l - x l) ^ 2)]
  exact bb_variance (hμ1 l) (hx.1 l) (hx.2 l)

/-! ### The approximation lemma -/

/-- The common box `[-1,2]^n` containing every node we evaluate at. -/
def S (n : ℕ) : Set (Fin n → ℝ) := Set.Icc (-1) 2

lemma cube_sub_S {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ FuzzyGames.NTUCore.cube n) : x ∈ S n :=
  ⟨fun l => by have := hx.1 l; simp at this ⊢; linarith,
   fun l => by have := hx.2 l; simp at this ⊢; linarith⟩

lemma approx {n : ℕ} (g : (Fin n → ℝ) → ℝ) (hg : Continuous g) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ μ : Fin n → ℕ, (∀ l, m - 1 ≤ μ l ∧ μ l ≤ m) →
      ∀ x ∈ FuzzyGames.NTUCore.cube n, ∀ y : (Fin n → ℕ) → (Fin n → ℝ),
        (∀ j ∈ J n m, W μ j x ≠ 0 →
          y j ∈ S n ∧ ‖y j - fun l => (j l : ℝ) / μ l‖ ≤ 1 / m) →
        |∑ j ∈ J n m, g (y j) * W μ j x - g x| ≤ η := by
  have hS : IsCompact (S n) := isCompact_Icc
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1
    (hS.uniformContinuousOn_of_continuous hg.continuousOn) (η / 2) (by linarith)
  obtain ⟨G, hG⟩ := hS.exists_bound_of_continuousOn hg.continuousOn
  set G' := |G| with hG'
  have hG'0 : 0 ≤ G' := abs_nonneg _
  set c : ℝ := 8 * G' / δ ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  set A : ℝ := 2 / δ + 2 * c * n / η + 3 with hA
  refine ⟨⌈A⌉₊, fun m hm μ hμ x hx y hy => ?_⟩
  have hmA : A ≤ m := le_trans (Nat.le_ceil A) (by exact_mod_cast hm)
  have h2δ : 0 ≤ 2 / δ := by positivity
  have h2c : 0 ≤ 2 * c * n / η := by positivity
  have hm3 : (3 : ℝ) ≤ m := by linarith
  have hm1 : 1 ≤ m - 1 := by
    have : (3 : ℕ) ≤ m := by exact_mod_cast hm3
    omega
  have hmpos : (0 : ℝ) < m := by linarith
  have hmδ : 1 / (m : ℝ) ≤ δ / 2 := by
    rw [div_le_div_iff₀ hmpos (by norm_num)]
    have : 2 / δ ≤ m := by linarith
    rw [div_le_iff₀ hδ] at this
    linarith
  have hμle : ∀ l, μ l ≤ m := fun l => (hμ l).2
  have hμ1 : ∀ l, 1 ≤ μ l := fun l => le_trans hm1 (hμ l).1
  have hxS := cube_sub_S hx
  -- pointwise estimate
  have hpt : ∀ j ∈ J n m, |g (y j) - g x| * W μ j x ≤
      (η / 2 + c * ∑ l, ((j l : ℝ) / μ l - x l) ^ 2) * W μ j x := by
    intro j hj
    have hW0 := W_nonneg μ j hx
    rcases eq_or_ne (W μ j x) 0 with h0 | h0
    · rw [h0, mul_zero, mul_zero]
    refine mul_le_mul_of_nonneg_right ?_ hW0
    obtain ⟨hyS, hyz⟩ := hy j hj h0
    have hsq : 0 ≤ c * ∑ l, ((j l : ℝ) / μ l - x l) ^ 2 :=
      mul_nonneg hc0 (Finset.sum_nonneg fun l _ => sq_nonneg _)
    by_cases hd : dist (y j) x < δ
    · have := hδu (y j) hyS x hxS hd
      rw [Real.dist_eq] at this
      linarith
    · push Not at hd
      rw [dist_eq_norm] at hd
      set z : Fin n → ℝ := fun l => (j l : ℝ) / μ l with hz
      have hzx : δ / 2 ≤ ‖z - x‖ := by
        have : ‖y j - x‖ ≤ ‖y j - z‖ + ‖z - x‖ := by
          calc ‖y j - x‖ = ‖(y j - z) + (z - x)‖ := by congr 1; abel
            _ ≤ _ := norm_add_le _ _
        linarith
      obtain ⟨l0, hl0⟩ : ∃ l, δ / 2 ≤ |z l - x l| := by
        by_contra hcon
        push Not at hcon
        have : ‖z - x‖ < δ / 2 := (pi_norm_lt_iff (by linarith)).2 fun l => by
          simpa [Real.norm_eq_abs] using hcon l
        linarith
      have hsum : δ ^ 2 / 4 ≤ ∑ l, ((j l : ℝ) / μ l - x l) ^ 2 := by
        have h1 : (δ / 2) ^ 2 ≤ (z l0 - x l0) ^ 2 := by
          rw [← sq_abs (z l0 - x l0)]
          exact pow_le_pow_left₀ (by linarith) hl0 2
        have h2 : (z l0 - x l0) ^ 2 ≤ ∑ l, ((j l : ℝ) / μ l - x l) ^ 2 :=
          Finset.single_le_sum (f := fun l => ((j l : ℝ) / μ l - x l) ^ 2)
            (fun l _ => sq_nonneg _) (Finset.mem_univ l0)
        nlinarith
      have hcs : 2 * G' ≤ c * ∑ l, ((j l : ℝ) / μ l - x l) ^ 2 := by
        have : c * (δ ^ 2 / 4) = 2 * G' := by
          rw [hc]; field_simp; ring
        rw [← this]
        exact mul_le_mul_of_nonneg_left hsum hc0
      have hgy : |g (y j)| ≤ G' := le_trans (hG _ hyS) (le_abs_self _)
      have hgx : |g x| ≤ G' := le_trans (hG _ hxS) (le_abs_self _)
      have : |g (y j) - g x| ≤ |g (y j)| + |g x| := abs_sub _ _
      linarith
  have hWs := W_sum μ hμle x
  have hrw : ∑ j ∈ J n m, g (y j) * W μ j x - g x =
      ∑ j ∈ J n m, (g (y j) - g x) * W μ j x := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hWs, mul_one]
  rw [hrw]
  calc |∑ j ∈ J n m, (g (y j) - g x) * W μ j x|
      ≤ ∑ j ∈ J n m, |(g (y j) - g x) * W μ j x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ J n m, |g (y j) - g x| * W μ j x := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (W_nonneg μ j hx)]
    _ ≤ ∑ j ∈ J n m, (η / 2 + c * ∑ l, ((j l : ℝ) / μ l - x l) ^ 2) * W μ j x :=
        Finset.sum_le_sum hpt
    _ = η / 2 * ∑ j ∈ J n m, W μ j x +
          c * ∑ j ∈ J n m, W μ j x * ∑ l, ((j l : ℝ) / μ l - x l) ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ ≤ η / 2 * 1 + c * ∑ l, 1 / (μ l : ℝ) := by
        rw [hWs]
        gcongr
        exact W_var μ hμle hμ1 hx
    _ ≤ η / 2 + c * (n / ((m : ℝ) - 1)) := by
        rw [mul_one]
        gcongr
        have hm1' : (1 : ℝ) ≤ (m : ℝ) - 1 := by linarith
        calc ∑ l, 1 / (μ l : ℝ) ≤ ∑ _l : Fin n, 1 / ((m : ℝ) - 1) := by
              refine Finset.sum_le_sum fun l _ => ?_
              have : (m : ℝ) - 1 ≤ μ l := by
                have := (hμ l).1
                have : ((m - 1 : ℕ) : ℝ) ≤ μ l := by exact_mod_cast this
                rw [Nat.cast_sub (by omega)] at this
                simpa using this
              exact one_div_le_one_div_of_le (by linarith) this
          _ = n / ((m : ℝ) - 1) := by simp [div_eq_mul_inv]
    _ ≤ η := by
        have hm1' : (0 : ℝ) < (m : ℝ) - 1 := by linarith
        have : c * (n / ((m : ℝ) - 1)) ≤ η / 2 := by
          rw [← mul_div_assoc, div_le_iff₀ hm1']
          have h3 : 2 * c * n / η ≤ (m : ℝ) - 1 := by linarith
          rw [div_le_iff₀ hη] at h3
          nlinarith
        linarith


/-! ### Polynomial functions -/

/-- `g` is a finite linear combination of monomials. -/
def IsPolyFn {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (K : Finset (Fin n → ℕ)) (a : (Fin n → ℕ) → ℝ), ∀ x, g x = ∑ k ∈ K, a k * monomial k x

lemma isPoly_zero {n : ℕ} : IsPolyFn (fun _ : Fin n → ℝ => (0 : ℝ)) :=
  ⟨∅, fun _ => 0, fun x => by simp⟩

lemma isPoly_add {n : ℕ} {g h : (Fin n → ℝ) → ℝ} (hg : IsPolyFn g) (hh : IsPolyFn h) :
    IsPolyFn (fun x => g x + h x) := by
  obtain ⟨K, a, ha⟩ := hg
  obtain ⟨K', a', ha'⟩ := hh
  refine ⟨K ∪ K', fun k => (if k ∈ K then a k else 0) + (if k ∈ K' then a' k else 0),
    fun x => ?_⟩
  simp_rw [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.union_inter_cancel_left,
    Finset.union_inter_cancel_right, ha, ha']

lemma isPoly_const_mul {n : ℕ} (c : ℝ) {g : (Fin n → ℝ) → ℝ} (hg : IsPolyFn g) :
    IsPolyFn (fun x => c * g x) := by
  obtain ⟨K, a, ha⟩ := hg
  refine ⟨K, fun k => c * a k, fun x => ?_⟩
  show c * g x = _
  rw [ha, Finset.mul_sum]; simp_rw [mul_assoc]

lemma isPoly_sum {n : ℕ} {ι : Type*} (s : Finset ι) (g : ι → (Fin n → ℝ) → ℝ)
    (hg : ∀ i ∈ s, IsPolyFn (g i)) : IsPolyFn (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isPoly_zero (n := n))
  | insert a s ha ih =>
    have h1 := hg a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have := isPoly_add h1 h2
    simpa [Finset.sum_insert ha] using this

lemma isPoly_prod_coord {n : ℕ} (p : Fin n → Polynomial ℝ) :
    IsPolyFn (fun x => ∏ l, (p l).eval (x l)) := by
  refine ⟨Fintype.piFinset fun l => range ((p l).natDegree + 1),
    fun k => ∏ l, (p l).coeff (k l), fun x => ?_⟩
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [monomial, ← Finset.prod_mul_distrib]

lemma isPoly_contDiff {n : ℕ} {g : (Fin n → ℝ) → ℝ} (hg : IsPolyFn g) : ContDiff ℝ 1 g := by
  obtain ⟨K, a, ha⟩ := hg
  have : g = fun x => ∑ k ∈ K, a k * monomial k x := funext ha
  rw [this]
  refine ContDiff.sum fun k _ => contDiff_const.mul ?_
  unfold monomial
  exact contDiff_prod fun i _ => (contDiff_apply ℝ ℝ i).pow _

/-! ### The Bernstein operator -/

/-- The multivariate Bernstein polynomial of degree `m` in each variable. -/
noncomputable def Bm (n m : ℕ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ j ∈ J n m, f (fun l => (j l : ℝ) / m) * W (fun _ => m) j x

lemma Bm_isPoly (n m : ℕ) (f : (Fin n → ℝ) → ℝ) : IsPolyFn (Bm n m f) := by
  unfold Bm
  refine isPoly_sum _ _ fun j _ => isPoly_const_mul _ ?_
  have hW : W (fun _ => m) j = fun x => ∏ l, (bernsteinPolynomial ℝ m (j l)).eval (x l) := by
    funext x; simp [W, bb_eq_eval]
  rw [hW]
  exact isPoly_prod_coord (fun l => bernsteinPolynomial ℝ m (j l))

/-- Reindexing a multi-index sum by a unit shift in coordinate `i`. -/
lemma sum_shift {n m : ℕ} (i : Fin n) (H : (Fin n → ℕ) → ℝ) :
    ∑ j ∈ J n m, (if j i = 0 then 0 else H j) =
      ∑ j ∈ J n m, (if j i < m then H (Function.update j i (j i + 1)) else 0) := by
  have hne : ∀ j : Fin n → ℕ, (if j i = 0 then 0 else H j) = if j i ≠ 0 then H j else 0 := by
    intro j; split_ifs <;> simp_all
  simp_rw [hne]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun j => Function.update j i (j i + 1))
    (fun j => Function.update j i (j i - 1)) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [J, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hj ⊢
    refine ⟨fun l => ?_, by simp⟩
    by_cases hl : l = i
    · subst hl; simp; omega
    · rw [Function.update_of_ne hl]; exact hj.1 l
  · intro j hj
    simp only [J, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hj ⊢
    refine ⟨fun l => ?_, by simp; have := hj.1 i; omega⟩
    by_cases hl : l = i
    · subst hl; simp; have := hj.1 l; omega
    · rw [Function.update_of_ne hl]; exact hj.1 l
  · intro j hj
    simp
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter] at hj
    simp only [Function.update_self, Function.update_idem]
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hj.2), Function.update_eq_self]
  · intro j _; rfl

lemma Bm_deriv {n m : ℕ} (hm : 1 ≤ m) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (Bm n m f) x (Pi.single i 1) =
      ∑ j ∈ J n m, ((m : ℝ) * (f (fun l => (Function.update j i (j i + 1) l : ℝ) / m) -
        f (fun l => (j l : ℝ) / m))) * W (Function.update (fun _ => m) i (m - 1)) j x := by
  set R : (Fin n → ℕ) → ℝ := fun j => ∏ l ∈ univ.erase i, bb m (j l) (x l) with hR
  have hWline : ∀ (j : Fin n → ℕ) (s : ℝ),
      W (fun _ => m) j (x + s • Pi.single i 1) = bb m (j i) (x i + s) * R j := by
    intro j s
    unfold W
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun l hl => ?_
      have : l ≠ i := Finset.ne_of_mem_erase hl
      simp [Pi.single_apply, this]
  have hWi : ∀ j : Fin n → ℕ,
      W (Function.update (fun _ => m) i (m - 1)) j x = bb (m - 1) (j i) (x i) * R j := by
    intro j
    unfold W
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun l hl => ?_
      have : l ≠ i := Finset.ne_of_mem_erase hl
      rw [Function.update_of_ne this]
  have hRshift : ∀ j : Fin n → ℕ, R (Function.update j i (j i + 1)) = R j := by
    intro j
    refine Finset.prod_congr rfl fun l hl => ?_
    have : l ≠ i := Finset.ne_of_mem_erase hl
    rw [Function.update_of_ne this]
  set D : (Fin n → ℕ) → ℝ := fun j =>
    (m : ℝ) * ((if j i = 0 then 0 else bb (m - 1) (j i - 1) (x i)) - bb (m - 1) (j i) (x i))
    with hD
  have hline : HasDerivAt (fun s : ℝ => Bm n m f (x + s • Pi.single i 1))
      (∑ j ∈ J n m, f (fun l => (j l : ℝ) / m) * (D j * R j)) 0 := by
    have : (fun s : ℝ => Bm n m f (x + s • Pi.single i 1)) =
        fun s => ∑ j ∈ J n m, f (fun l => (j l : ℝ) / m) * (bb m (j i) (x i + s) * R j) := by
      funext s; unfold Bm; simp_rw [hWline]
    rw [this]
    refine HasDerivAt.fun_sum fun j _ => ?_
    refine HasDerivAt.const_mul _ (HasDerivAt.mul_const ?_ _)
    have h1 : HasDerivAt (bb m (j i)) (D j) (x i + 0) := by
      rw [add_zero]; exact bb_hasDerivAt hm (j i) (x i)
    exact h1.comp_const_add (x i) 0
  have hdiff : Differentiable ℝ (Bm n m f) :=
    (isPoly_contDiff (Bm_isPoly n m f)).differentiable (by norm_num)
  have hline2 : HasDerivAt (fun s : ℝ => Bm n m f (x + s • Pi.single i 1))
      (fderiv ℝ (Bm n m f) x (Pi.single i 1)) 0 := by
    have hid : HasDerivAt (fun s : ℝ => x + s • Pi.single i 1) (Pi.single i 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ))).const_add x
    have hv : HasFDerivAt (Bm n m f) (fderiv ℝ (Bm n m f) x) (x + (0 : ℝ) • Pi.single i 1) := by
      rw [zero_smul, add_zero]; exact (hdiff x).hasFDerivAt
    exact HasFDerivAt.comp_hasDerivAt (l := Bm n m f)
      (f := fun s : ℝ => x + s • Pi.single i 1) (0 : ℝ) hv hid
  rw [hline2.unique hline]
  -- algebra
  have e1 : ∀ j ∈ J n m, f (fun l => (j l : ℝ) / m) * (D j * R j) =
      (m : ℝ) * ((if j i = 0 then 0 else
          f (fun l => (j l : ℝ) / m) * bb (m - 1) (j i - 1) (x i) * R j) -
        f (fun l => (j l : ℝ) / m) * bb (m - 1) (j i) (x i) * R j) := by
    intro j _
    simp only [hD]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl e1, ← Finset.mul_sum, Finset.sum_sub_distrib,
    sum_shift i (fun j => f (fun l => (j l : ℝ) / m) * bb (m - 1) (j i - 1) (x i) * R j)]
  have e2 : ∀ j ∈ J n m,
      (if j i < m then f (fun l => (Function.update j i (j i + 1) l : ℝ) / m) *
          bb (m - 1) (Function.update j i (j i + 1) i - 1) (x i) *
          R (Function.update j i (j i + 1)) else 0) =
        f (fun l => (Function.update j i (j i + 1) l : ℝ) / m) * bb (m - 1) (j i) (x i) *
          R j := by
    intro j hj
    split_ifs with h
    · simp [hRshift]
    · have : j i = m := by
        simp only [J, Fintype.mem_piFinset, Finset.mem_range] at hj
        have := hj i; omega
      rw [this, bb_of_lt (by omega)]; ring
  rw [Finset.sum_congr rfl e2, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hWi]; ring


lemma W_ne_zero_le {n : ℕ} {μ j : Fin n → ℕ} {x : Fin n → ℝ} (h : W μ j x ≠ 0) (l : Fin n) :
    j l ≤ μ l := by
  by_contra hlt
  push Not at hlt
  apply h
  exact Finset.prod_eq_zero (Finset.mem_univ l) (bb_of_lt hlt _)

lemma opnorm_le_sum {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i, |L (Pi.single i 1)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ => abs_nonneg _)
    fun y => ?_
  have hlin := L.toLinearMap.pi_apply_eq_sum_univ y
  have hs : ∀ i : Fin n, (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
    intro i; funext j; simp [Pi.single_apply, eq_comm]
  simp only [ContinuousLinearMap.coe_coe, hs] at hlin
  rw [hlin, Real.norm_eq_abs, Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [smul_eq_mul, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have := norm_le_pi_norm y i
  rwa [Real.norm_eq_abs] at this

end FuzzyDenseAux

open FuzzyDenseAux in
theorem solution (n : ℕ) (v : Vn n) (ε : ℝ) (hε : 0 < ε) :
    ∃ (K : Finset (Fin n → ℕ)) (a : (Fin n → ℕ) → ℝ), 0 ∉ K ∧
      c1seminorm (fun τ => v.1 τ - ∑ k ∈ K, a k * monomial k τ) < ε := by
  set f := v.1 with hfdef
  have hf : ContDiff ℝ 1 f := v.2.1
  have hf0 : f 0 = 0 := v.2.2
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hcf : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  set η := ε / (n + 3) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨M0, hM0⟩ := approx f hf.continuous hηpos
  have hMi : ∀ i : Fin n, ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ μ : Fin n → ℕ,
      (∀ l, m - 1 ≤ μ l ∧ μ l ≤ m) →
      ∀ x ∈ FuzzyGames.NTUCore.cube n, ∀ y : (Fin n → ℕ) → (Fin n → ℝ),
        (∀ j ∈ J n m, W μ j x ≠ 0 →
          y j ∈ S n ∧ ‖y j - fun l => (j l : ℝ) / μ l‖ ≤ 1 / m) →
        |∑ j ∈ J n m, fderiv ℝ f (y j) (Pi.single i 1) * W μ j x -
          fderiv ℝ f x (Pi.single i 1)| ≤ η := fun i =>
    approx (fun y => fderiv ℝ f y (Pi.single i 1)) (hcf.clm_apply continuous_const) hηpos
  choose Mi hMi using hMi
  set m : ℕ := M0 + ∑ i, Mi i + 2 with hm
  have hm2 : 2 ≤ m := by omega
  have hmM0 : M0 ≤ m := by omega
  have hmMi : ∀ i, Mi i ≤ m := by
    intro i
    have : Mi i ≤ ∑ i, Mi i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hmpos : (0 : ℝ) < m := by have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
                                 linarith
  set B := Bm n m f with hB
  have hBpoly := Bm_isPoly n m f
  have hBcd : ContDiff ℝ 1 B := isPoly_contDiff hBpoly
  have hdB : Differentiable ℝ B := hBcd.differentiable (by norm_num)
  -- sup estimate
  have hsup : ∀ x ∈ FuzzyGames.NTUCore.cube n, |f x - B x| ≤ η := by
    intro x hx
    have := hM0 m hmM0 (fun _ => m) (fun _ => ⟨Nat.sub_le _ _, le_rfl⟩) x hx
      (fun j l => (j l : ℝ) / m) (by
        intro j _ hW
        refine ⟨⟨fun l => ?_, fun l => ?_⟩, by simp⟩
        · simp only [Pi.neg_apply, Pi.one_apply]
          have : (0 : ℝ) ≤ (j l : ℝ) / m := by positivity
          linarith
        · have hle := W_ne_zero_le hW l
          simp only [Pi.ofNat_apply]
          have : (j l : ℝ) / m ≤ 1 := by
            rw [div_le_one hmpos]; exact_mod_cast hle
          linarith)
    rw [abs_sub_comm]
    exact this
  -- derivative estimate
  have hder : ∀ x ∈ FuzzyGames.NTUCore.cube n, ∀ i : Fin n,
      |fderiv ℝ f x (Pi.single i 1) - fderiv ℝ B x (Pi.single i 1)| ≤ η := by
    intro x hx i
    rw [hB, Bm_deriv (by omega) f x i]
    set jm : (Fin n → ℕ) → (Fin n → ℝ) := fun j l => (j l : ℝ) / m with hjm
    have hmvt : ∀ j : Fin n → ℕ, ∃ θ ∈ Set.Ioo (0 : ℝ) (1 / m),
        fderiv ℝ f (jm j + θ • Pi.single i 1) (Pi.single i 1) =
          (m : ℝ) * (f (fun l => (Function.update j i (j i + 1) l : ℝ) / m) - f (jm j)) := by
      intro j
      have hφ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f (jm j + s • Pi.single i 1))
          (fderiv ℝ f (jm j + s • Pi.single i 1) (Pi.single i 1)) s := by
        intro s
        have hid : HasDerivAt (fun s : ℝ => jm j + s • Pi.single i 1) (Pi.single i 1) s := by
          simpa using ((hasDerivAt_id s).smul_const (Pi.single i (1 : ℝ))).const_add (jm j)
        exact HasFDerivAt.comp_hasDerivAt (l := f)
          (f := fun s : ℝ => jm j + s • Pi.single i 1) s (hdf _).hasFDerivAt hid
      obtain ⟨θ, hθ, hθeq⟩ := exists_hasDerivAt_eq_slope
        (fun s : ℝ => f (jm j + s • Pi.single i 1))
        (fun s => fderiv ℝ f (jm j + s • Pi.single i 1) (Pi.single i 1))
        (by positivity : (0 : ℝ) < 1 / m)
        (fun s _ => (hφ s).continuousAt.continuousWithinAt) (fun s _ => hφ s)
      refine ⟨θ, hθ, ?_⟩
      rw [hθeq]
      have hpt : jm j + (1 / (m : ℝ)) • Pi.single i 1 =
          fun l => (Function.update j i (j i + 1) l : ℝ) / m := by
        funext l
        by_cases hl : l = i
        · subst hl; simp [hjm]; ring
        · simp [hjm, hl, Function.update_of_ne hl]
      simp only [hpt, zero_smul, add_zero]
      field_simp
      ring
    choose θ hθ hθeq using hmvt
    set μi : Fin n → ℕ := Function.update (fun _ => m) i (m - 1) with hμi
    have hμb : ∀ l, m - 1 ≤ μi l ∧ μi l ≤ m := by
      intro l
      by_cases hl : l = i
      · subst hl; simp [hμi]
      · simp [hμi, Function.update_of_ne hl]
    have h := hMi i m (hmMi i) μi hμb x hx (fun j => jm j + θ j • Pi.single i 1) (by
      intro j _ hW
      have hle := W_ne_zero_le hW
      have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      have hji : j i ≤ m - 1 := by
        have := hle i; simpa [hμi] using this
      have hji' : (j i : ℝ) ≤ (m : ℝ) - 1 := by
        rw [← hm1]; exact_mod_cast hji
      obtain ⟨hθ0, hθ1⟩ := hθ j
      refine ⟨⟨fun l => ?_, fun l => ?_⟩, ?_⟩
      · by_cases hl : l = i
        · subst hl; simp [hjm]
          have : (0 : ℝ) ≤ (j l : ℝ) / m := by positivity
          linarith
        · simp [hjm, hl]
          have : (0 : ℝ) ≤ (j l : ℝ) / m := by positivity
          linarith
      · by_cases hl : l = i
        · subst hl; simp [hjm]
          have : (j l : ℝ) / m + θ j ≤ 1 := by
            have : (j l : ℝ) / m ≤ ((m : ℝ) - 1) / m := by gcongr
            have h2 : ((m : ℝ) - 1) / m + 1 / m = 1 := by field_simp; ring
            linarith
          linarith
        · simp [hjm, hl]
          have hl' := hle l
          rw [hμi, Function.update_of_ne hl] at hl'
          have : (j l : ℝ) / m ≤ 1 := by
            rw [div_le_one hmpos]; exact_mod_cast hl'
          linarith
      · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun l => ?_
        by_cases hl : l = i
        · subst hl
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hjm,
            Pi.single_eq_same, mul_one, hμi, Function.update_self, Real.norm_eq_abs]
          rw [hm1]
          have hm1pos : (0 : ℝ) < (m : ℝ) - 1 := by
            have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
            linarith
          have hj0 : (0 : ℝ) ≤ j l := Nat.cast_nonneg _
          have ha : (j l : ℝ) / m ≤ (j l : ℝ) / ((m : ℝ) - 1) :=
            div_le_div_of_nonneg_left hj0 hm1pos (by linarith)
          have hb : (j l : ℝ) / ((m : ℝ) - 1) ≤ ((j l : ℝ) + 1) / m := by
            rw [div_le_div_iff₀ hm1pos hmpos]; nlinarith
          have hc : ((j l : ℝ) + 1) / m = (j l : ℝ) / m + 1 / m := by ring
          rw [abs_le]; constructor <;> linarith
        · simp [hjm, hl, hμi, Function.update_of_ne hl])
    simp only [hθeq] at h
    rw [abs_sub_comm]
    exact h
  -- the operator norm of the derivative of `f - B`
  have hD : ∀ x ∈ FuzzyGames.NTUCore.cube n,
      ‖fderiv ℝ (fun τ => f τ - B τ) x‖ ≤ n * η := by
    intro x hx
    rw [fderiv_fun_sub (hdf x) (hdB x)]
    refine le_trans (opnorm_le_sum _) ?_
    calc ∑ i, |(fderiv ℝ f x - fderiv ℝ B x) (Pi.single i 1)| ≤ ∑ _i : Fin n, η :=
          Finset.sum_le_sum fun i _ => by
            rw [ContinuousLinearMap.sub_apply]; exact hder x hx i
      _ = n * η := by simp
  -- the polynomial without constant term
  obtain ⟨K, a, ha⟩ := hBpoly
  refine ⟨K.erase 0, a, Finset.notMem_erase 0 K, ?_⟩
  have hmono0 : ∀ k : Fin n → ℕ, k ≠ 0 → monomial k 0 = 0 := by
    intro k hk
    obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
      by_contra h; push Not at h; exact hk (funext h)
    unfold monomial
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [zero_pow hi])
  have hsplit : ∀ τ, B τ = ∑ k ∈ K.erase 0, a k * monomial k τ +
      (if (0 : Fin n → ℕ) ∈ K then a 0 else 0) := by
    intro τ
    rw [hB, ha]
    by_cases h0 : (0 : Fin n → ℕ) ∈ K
    · rw [← Finset.add_sum_erase K _ h0, if_pos h0, add_comm]
      simp [monomial]
    · rw [Finset.erase_eq_of_notMem h0, if_neg h0, add_zero]
  have hB0 : B 0 = if (0 : Fin n → ℕ) ∈ K then a 0 else 0 := by
    rw [hsplit 0, Finset.sum_eq_zero, zero_add]
    intro k hk
    rw [hmono0 k (Finset.ne_of_mem_erase hk), mul_zero]
  have hfun : (fun τ => v.1 τ - ∑ k ∈ K.erase 0, a k * monomial k τ) =
      fun τ => (f τ - B τ) + B 0 := by
    funext τ
    rw [hsplit τ, hB0]
    ring
  rw [hfun]
  have h0cube : (0 : Fin n → ℝ) ∈ FuzzyGames.NTUCore.cube n := ⟨le_rfl, zero_le_one⟩
  have : Nonempty (FuzzyGames.NTUCore.cube n) := ⟨⟨0, h0cube⟩⟩
  have hB0η : |B 0| ≤ η := by
    have := hsup 0 h0cube
    rwa [hf0, zero_sub, abs_neg] at this
  have h1 : (⨆ τ : FuzzyGames.NTUCore.cube n, |(f τ - B τ) + B 0|) ≤ 2 * η := by
    refine ciSup_le fun τ => ?_
    have := hsup τ τ.2
    calc |(f τ - B τ) + B 0| ≤ |f τ - B τ| + |B 0| := abs_add_le _ _
      _ ≤ η + η := add_le_add this hB0η
      _ = 2 * η := by ring
  have h2 : (⨆ τ : FuzzyGames.NTUCore.cube n,
      ‖fderiv ℝ (fun τ => (f τ - B τ) + B 0) τ‖) ≤ n * η := by
    refine ciSup_le fun τ => ?_
    rw [fderiv_add_const]
    exact hD τ τ.2
  unfold c1seminorm
  calc _ ≤ 2 * η + n * η := add_le_add h1 h2
    _ < ε := by
      rw [hη, ← add_mul, mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
