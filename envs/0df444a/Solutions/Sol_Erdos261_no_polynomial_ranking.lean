-- Prove2me | solution 1 for Erdos261.no_polynomial_ranking
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:30:28.586495+00:00
-- url     : https://prove2.me/submissions/20604a90-182c-490b-a247-c8f6a93f4c9b

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset


namespace E261P
open Polynomial Filter

noncomputable def ev (P : MvPolynomial (Fin 2) ℝ) (x y : ℝ) : ℝ := MvPolynomial.eval ![x, y] P

lemma ev_eq (P : MvPolynomial (Fin 2) ℝ) (x y : ℝ) :
    ev P x y = ∑ m ∈ P.support, P.coeff m * (x ^ (m 0) * y ^ (m 1)) := by
  unfold ev
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Fin.prod_univ_two]
  simp

noncomputable def T (α β γ : ℝ) (a b : ℕ) : ℝ[X] := (C α * X + C β) ^ a * (C (γ ^ b) * X ^ b)

lemma T_eval (α β γ : ℝ) (a b : ℕ) (M : ℝ) :
    (T α β γ a b).eval M = (α * M + β) ^ a * (γ * M) ^ b := by
  simp [T, mul_pow]

lemma lin_natDegree (α β : ℝ) : (C α * X + C β).natDegree ≤ 1 := by
  apply natDegree_add_le_of_degree_le
  · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  · simp

lemma T_natDegree (α β γ : ℝ) (a b : ℕ) : (T α β γ a b).natDegree ≤ a + b := by
  unfold T
  refine (natDegree_mul_le).trans (add_le_add ?_ ?_)
  · refine natDegree_pow_le.trans ?_
    have := lin_natDegree α β
    nlinarith
  · refine (natDegree_C_mul_le _ _).trans ?_
    simp

lemma T_coeff_top (α β γ : ℝ) (a b : ℕ) : (T α β γ a b).coeff (a + b) = α ^ a * γ ^ b := by
  unfold T
  rw [show (C α * X + C β) ^ a * (C (γ ^ b) * X ^ b) = C (γ ^ b) * ((C α * X + C β) ^ a * X ^ b) by ring,
    coeff_C_mul, coeff_mul_X_pow]
  have h := coeff_pow_of_natDegree_le (m := a) (lin_natDegree α β)
  rw [mul_one] at h
  rw [h]
  simp
  ring

lemma T_coeff_lt (α β γ : ℝ) (a b j : ℕ) (h : a + b < j) : (T α β γ a b).coeff j = 0 :=
  coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (T_natDegree α β γ a b) h)

noncomputable def line (P : MvPolynomial (Fin 2) ℝ) (α β γ : ℝ) : ℝ[X] :=
  ∑ m ∈ P.support, C (P.coeff m) * T α β γ (m 0) (m 1)

lemma line_eval (P : MvPolynomial (Fin 2) ℝ) (α β γ M : ℝ) :
    (line P α β γ).eval M = ev P (α * M + β) (γ * M) := by
  rw [ev_eq, line, eval_finsetSum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [eval_mul, eval_C, T_eval]

lemma deg_le (P : MvPolynomial (Fin 2) ℝ) {m : Fin 2 →₀ ℕ} (hm : m ∈ P.support) :
    m 0 + m 1 ≤ P.totalDegree := by
  have := MvPolynomial.le_totalDegree hm
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at this
  exact this

lemma line_natDegree (P : MvPolynomial (Fin 2) ℝ) (α β γ : ℝ) :
    (line P α β γ).natDegree ≤ P.totalDegree := by
  unfold line
  apply natDegree_sum_le_of_forall_le
  intro m hm
  exact (natDegree_C_mul_le _ _).trans ((T_natDegree _ _ _ _ _).trans (deg_le P hm))

noncomputable def top (P : MvPolynomial (Fin 2) ℝ) (α γ : ℝ) : ℝ :=
  ∑ m ∈ P.support.filter (fun m => m 0 + m 1 = P.totalDegree), P.coeff m * (α ^ (m 0) * γ ^ (m 1))

lemma line_coeff_top (P : MvPolynomial (Fin 2) ℝ) (α β γ : ℝ) :
    (line P α β γ).coeff P.totalDegree = top P α γ := by
  unfold line top
  rw [finsetSum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [coeff_C_mul]
  split_ifs with h
  · rw [← h, T_coeff_top]
  · rw [T_coeff_lt _ _ _ _ _ _ (lt_of_le_of_ne (deg_le P hm) h), mul_zero]

/-- A polynomial of degree `≤ d` that is `≤ 0` at all large naturals has `coeff d ≤ 0`. -/
lemma coeff_nonpos_of_eventually (Q : ℝ[X]) (d : ℕ) (hQ : Q.natDegree ≤ d) (M0 : ℕ)
    (h : ∀ M : ℕ, M0 ≤ M → Q.eval (M : ℝ) ≤ 0) : Q.coeff d ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have hnd : Q.natDegree = d := le_antisymm hQ (le_natDegree_of_ne_zero hpos.ne')
  have hlc : 0 < Q.leadingCoeff := by rw [leadingCoeff, hnd]; exact hpos
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hQc := eq_C_of_natDegree_eq_zero hnd
    have := h M0 le_rfl
    rw [hQc, eval_C] at this
    linarith
  · have hdeg : 0 < Q.degree := by
      rw [degree_eq_natDegree (by intro h0; rw [h0] at hlc; simp at hlc), hnd]
      exact_mod_cast hd
    have ht := (Q.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlc.le).comp tendsto_natCast_atTop_atTop
    have hev := ht.eventually (eventually_gt_atTop 0)
    obtain ⟨M1, hM1⟩ := eventually_atTop.1 hev
    have h1 := hM1 (max M0 M1) (le_max_right _ _)
    have h2 := h (max M0 M1) (le_max_left _ _)
    simp only [Function.comp] at h1
    linarith

/-- The ranking hypothesis: `P ≥ 0` on admissible states with `N ≥ N0`, and `P` strictly decreases
along every greedy transition `(N,R) ↦ (N+1, 2R mod (N+1))` with nonzero result. -/
def Ranking (P : MvPolynomial (Fin 2) ℝ) (N0 : ℕ) : Prop :=
  ∀ N R : ℕ, N0 ≤ N → 2 ≤ N → 1 ≤ R → R < N →
    0 ≤ ev P N R ∧ (0 < 2 * R % (N + 1) → ev P ((N + 1 : ℕ) : ℝ) ((2 * R % (N + 1) : ℕ) : ℝ) < ev P N R)

lemma pow_ge_k (k : ℕ) (hk : 2 ≤ k) : k ≤ 2 ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact Nat.lt_two_pow_self

/-- Doubling steps of the `k`-cycle family. -/
lemma cycle_dbl (P : MvPolynomial (Fin 2) ℝ) (N0 : ℕ) (hP : Ranking P N0) (k M i : ℕ) (hk : 2 ≤ k)
    (hM : 2 ≤ M) (hMN : N0 ≤ M) (hi : i + 1 < k) :
    ev P ((2 ^ k - 1 : ℝ) * M + ((i : ℝ) + 1 - k)) ((2 : ℝ) ^ (i + 1) * M) <
      ev P ((2 ^ k - 1 : ℝ) * M + ((i : ℝ) - k)) ((2 : ℝ) ^ i * M) := by
  set u := 2 ^ (k - 1) with hu
  have hku : 2 ^ k = 2 * u := by rw [hu, ← pow_succ']; congr 1; omega
  have hk_le : k ≤ u := pow_ge_k k hk
  have hiu : 2 ^ (i + 1) ≤ u := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hi0 : 2 ^ i * 2 = 2 ^ (i + 1) := (pow_succ 2 i).symm
  have hu2 : 2 ≤ u := le_trans hk hk_le
  have huM : M + k ≤ u * M := by nlinarith
  have e2 : 2 * u * M = 2 * (u * M) := by ring
  have h1 : 2 ^ (i + 1) * M ≤ u * M := Nat.mul_le_mul_right _ hiu
  have h2 : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  have h3 : M ≤ 2 ^ i * M := Nat.le_mul_of_pos_left _ (by omega)
  have h4 : 2 ^ i * M * 2 = 2 ^ (i + 1) * M := by rw [← hi0]; ring
  set N := 2 * u * M - M - k + i with hN
  have hR : 2 * (2 ^ i * M) < N + 1 := by omega
  obtain ⟨hpos, hdec⟩ := hP N (2 ^ i * M) (by omega) (by omega) (by omega) (by omega)
  have hmod : 2 * (2 ^ i * M) % (N + 1) = 2 ^ (i + 1) * M := by
    rw [Nat.mod_eq_of_lt hR]; omega
  have := hdec (by rw [hmod]; positivity)
  rw [hmod] at this
  have cN : ((N : ℕ) : ℝ) = (2 ^ k - 1 : ℝ) * M + ((i : ℝ) - k) := by
    have : (N : ℕ) + k = (2 ^ k - 1) * M + i := by
      have : (2 ^ k - 1) * M = 2 * u * M - M := by rw [hku, Nat.sub_mul, one_mul]
      omega
    have h' : ((N : ℕ) : ℝ) + k = ((2 ^ k - 1 : ℕ) : ℝ) * M + i := by exact_mod_cast this
    have h'' : ((2 ^ k - 1 : ℕ) : ℝ) = (2 : ℝ) ^ k - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
    rw [h''] at h'; linarith
  have cN1 : ((N + 1 : ℕ) : ℝ) = (2 ^ k - 1 : ℝ) * M + ((i : ℝ) + 1 - k) := by
    push_cast; rw [cN]; ring
  rw [cN1, cN] at this
  push_cast at this
  exact this

/-- Closing (subtracting) step of the `k`-cycle family. -/
lemma cycle_last (P : MvPolynomial (Fin 2) ℝ) (N0 : ℕ) (hP : Ranking P N0) (k M : ℕ) (hk : 2 ≤ k)
    (hM : 2 ≤ M) (hMN : N0 ≤ M) :
    ev P ((2 ^ k - 1 : ℝ) * M + 0) ((1 : ℝ) * M) <
      ev P ((2 ^ k - 1 : ℝ) * M + (((k - 1 : ℕ) : ℝ) - k)) ((2 : ℝ) ^ (k - 1) * M) := by
  set u := 2 ^ (k - 1) with hu
  have hku : 2 ^ k = 2 * u := by rw [hu, ← pow_succ']; congr 1; omega
  have hk_le : k ≤ u := pow_ge_k k hk
  have hu2 : 2 ≤ u := le_trans hk hk_le
  have huM : M + k ≤ u * M := by nlinarith
  have huM2 : 2 * M ≤ u * M := Nat.mul_le_mul_right _ hu2
  have e2 : 2 * u * M = 2 * (u * M) := by ring
  set N := 2 * u * M - M - 1 with hN
  obtain ⟨hpos, hdec⟩ := hP N (u * M) (by omega) (by omega) (by nlinarith) (by omega)
  have hmod : 2 * (u * M) % (N + 1) = M := by
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have := hdec (by rw [hmod]; omega)
  rw [hmod] at this
  have h'' : ((2 ^ k - 1 : ℕ) : ℝ) = (2 : ℝ) ^ k - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  have hNM : N + 1 = (2 ^ k - 1) * M := by
    have : (2 ^ k - 1) * M = 2 * u * M - M := by rw [hku, Nat.sub_mul, one_mul]
    omega
  have cN1 : ((N + 1 : ℕ) : ℝ) = (2 ^ k - 1 : ℝ) * M + 0 := by
    rw [hNM]; push_cast [Nat.cast_sub (Nat.one_le_two_pow : 1 ≤ 2 ^ k)]; ring
  have cN : ((N : ℕ) : ℝ) = (2 ^ k - 1 : ℝ) * M + (((k - 1 : ℕ) : ℝ) - k) := by
    have e1 : ((N : ℕ) : ℝ) + 1 = (2 ^ k - 1 : ℝ) * M + 0 := by rw [← cN1]; push_cast; ring
    rw [Nat.cast_sub (by omega : 1 ≤ k)]; push_cast; linarith
  have cR : ((u * M : ℕ) : ℝ) = (2 : ℝ) ^ (k - 1) * M := by rw [hu]; push_cast; ring
  rw [cN1, cN, cR] at this
  simpa using this

lemma ineq_top (P : MvPolynomial (Fin 2) ℝ) (α β1 γ1 β2 γ2 : ℝ) (M0 : ℕ)
    (h : ∀ M : ℕ, M0 ≤ M → ev P (α * M + β1) (γ1 * M) < ev P (α * M + β2) (γ2 * M)) :
    top P α γ1 ≤ top P α γ2 := by
  have := coeff_nonpos_of_eventually (line P α β1 γ1 - line P α β2 γ2) P.totalDegree
    ((natDegree_sub_le _ _).trans (max_le (line_natDegree _ _ _ _) (line_natDegree _ _ _ _))) M0
    (fun M hM => by rw [eval_sub, line_eval, line_eval]; linarith [h M hM])
  rw [coeff_sub, line_coeff_top, line_coeff_top] at this
  linarith

/-- Leading-order consequence of the `k`-cycles: `top(2^k-1, 2) = top(2^k-1, 1)`. -/
lemma top_cycle (P : MvPolynomial (Fin 2) ℝ) (N0 : ℕ) (hP : Ranking P N0) (k : ℕ) (hk : 2 ≤ k) :
    top P (2 ^ k - 1) 2 = top P (2 ^ k - 1) 1 := by
  have step : ∀ i, i + 1 < k → top P (2 ^ k - 1) (2 ^ (i + 1)) ≤ top P (2 ^ k - 1) (2 ^ i) :=
    fun i hi => ineq_top P _ _ _ _ _ (max 2 N0) (fun M hM =>
      cycle_dbl P N0 hP k M i hk (le_trans (le_max_left _ _) hM) (le_trans (le_max_right _ _) hM) hi)
  have last : top P (2 ^ k - 1) 1 ≤ top P (2 ^ k - 1) (2 ^ (k - 1)) :=
    ineq_top P _ _ _ _ _ (max 2 N0) (fun M hM =>
      cycle_last P N0 hP k M hk (le_trans (le_max_left _ _) hM) (le_trans (le_max_right _ _) hM))
  have chain : ∀ i, 1 ≤ i → i < k → top P (2 ^ k - 1) (2 ^ i) ≤ top P (2 ^ k - 1) 2 := by
    intro i hi1 hik
    induction i, hi1 using Nat.le_induction with
    | base => simp
    | succ i hi ih => exact (step i hik).trans (ih (by omega))
  have h0 := step 0 (by omega)
  simp only [zero_add, pow_one, pow_zero] at h0
  have := chain (k - 1) (by omega) (by omega)
  linarith

lemma sup_ext2 {m m' : Fin 2 →₀ ℕ} (h0 : m 0 = m' 0) (h1 : m 1 = m' 1) : m = m' := by
  ext i; fin_cases i <;> simp [h0, h1]

/-- From `top(c,2) = top(c,1)` for infinitely many `c`: every top-degree monomial is a pure power of `N`. -/
lemma top_pure (P : MvPolynomial (Fin 2) ℝ)
    (h : ∀ k : ℕ, top P (2 ^ (k + 2) - 1) 2 = top P (2 ^ (k + 2) - 1) 1) :
    ∀ m ∈ P.support, m 0 + m 1 = P.totalDegree → m 1 = 0 := by
  set d := P.totalDegree
  set Sd := P.support.filter (fun m => m 0 + m 1 = d) with hSd
  set σ : ℝ[X] := ∑ m ∈ Sd, C (P.coeff m * (2 ^ (m 1) - 1)) * X ^ (m 0) with hσ
  have hev : ∀ x, σ.eval x = top P x 2 - top P x 1 := by
    intro x
    simp only [hσ, top, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp; ring
  have hσ0 : σ = 0 := by
    apply eq_zero_of_infinite_isRoot
    have hinj : Function.Injective (fun k : ℕ => (2 : ℝ) ^ (k + 2) - 1) := by
      intro a b hab
      simp only [sub_left_inj] at hab
      have := (pow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num)) hab
      omega
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective hinj)
    rintro x ⟨k, rfl⟩
    simp only [Set.mem_ofPred_eq, IsRoot, hev, h k, sub_self]
  intro m hm hmd
  have hmS : m ∈ Sd := Finset.mem_filter.2 ⟨hm, hmd⟩
  have hc := congrArg (fun p => p.coeff (m 0)) hσ0
  simp only [hσ, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at hc
  rw [Finset.sum_eq_single m] at hc
  · simp only [if_true] at hc
    have hne : P.coeff m ≠ 0 := MvPolynomial.mem_support_iff.1 hm
    have h2 : (2 : ℝ) ^ (m 1) - 1 = 0 := by
      rcases mul_eq_zero.1 hc with h | h
      · exact absurd h hne
      · exact h
    by_contra h1
    have : (1 : ℝ) < 2 ^ (m 1) := one_lt_pow₀ (by norm_num) h1
    linarith
  · intro m' hm' hne
    rw [if_neg]
    intro he
    apply hne
    have h' := (Finset.mem_filter.1 hm').2
    exact sup_ext2 he.symm (by omega)
  · intro h; exact absurd hmS h

lemma ev_const (P : MvPolynomial (Fin 2) ℝ) (h : ∀ m ∈ P.support, m 0 = 0 ∧ m 1 = 0) (x y : ℝ) :
    ev P x y = ∑ m ∈ P.support, P.coeff m := by
  rw [ev_eq]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [(h m hm).1, (h m hm).2]; simp

lemma coeff_pm2 (d : ℕ) (hd : 1 ≤ d) :
    ((C (3 : ℝ) * X + C (-2)) ^ d).coeff (d - 1) = (3 : ℝ) ^ d * ((-2 / 3) * (d : ℝ)) := by
  rw [show C (3 : ℝ) * X + C (-2) = C 3 * (X + C (-2 / 3)) by
    rw [mul_add, ← C_mul]; norm_num, mul_pow, ← C_pow, coeff_C_mul, coeff_X_add_C_pow,
    Nat.choose_symm_of_eq_add (show d = (d - 1) + 1 by omega), Nat.choose_one_right,
    show d - (d - 1) = 1 by omega, pow_one]

lemma coeff_p0 (d : ℕ) (hd : 1 ≤ d) : ((C (3 : ℝ) * X + C 0) ^ d).coeff (d - 1) = 0 := by
  rw [C_0, add_zero, mul_pow, ← C_pow, coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]

/-- **A2 (no polynomial ranking function).** No real bivariate polynomial `P(N,R)` is nonnegative on
all admissible greedy states `(N,R)` (`N ≥ max(2,N0)`, `1 ≤ R < N`) and strictly decreases along
every greedy transition `(N,R) ↦ (N+1, 2R mod (N+1))` with nonzero result. -/
theorem no_polynomial_ranking (P : MvPolynomial (Fin 2) ℝ) (N0 : ℕ) : ¬ Ranking P N0 := by
  intro hP
  set d := P.totalDegree with hd
  -- trivial case: all monomials constant
  by_cases hconst : ∀ m ∈ P.support, m 0 = 0 ∧ m 1 = 0
  · have := (hP (max N0 2) 1 (le_max_left _ _) (le_max_right _ _) le_rfl (by omega)).2
      (by rw [Nat.mod_eq_of_lt (by omega)]; norm_num)
    rw [ev_const P hconst, ev_const P hconst] at this
    exact lt_irrefl _ this
  push Not at hconst
  obtain ⟨m1, hm1, hm1ne⟩ := hconst
  have hd1 : 1 ≤ d := by
    have := deg_le P hm1
    by_contra h; push Not at h
    exact hm1ne (by omega) (by omega)
  -- a top-degree monomial
  have hne : P.support.Nonempty := ⟨m1, hm1⟩
  obtain ⟨ms, hms, hmsd⟩ := Finset.exists_mem_eq_sup P.support hne (fun s => s.sum fun _ e => e)
  have hmsd' : ms 0 + ms 1 = d := by
    rw [hd, MvPolynomial.totalDegree, hmsd, Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
  have hpure := top_pure P (fun k => top_cycle P N0 hP (k + 2) (by omega))
  have hms1 : ms 1 = 0 := hpure ms hms hmsd'
  have hms0 : ms 0 = d := by omega
  have hSd : ∀ m ∈ P.support, m 0 + m 1 = d → m = ms := by
    intro m hm hmd
    have := hpure m hm hmd
    exact sup_ext2 (by omega) (by omega)
  set a := P.coeff ms with ha
  have hane : a ≠ 0 := MvPolynomial.mem_support_iff.1 hms
  have htop : ∀ α γ : ℝ, top P α γ = a * α ^ d := by
    intro α γ
    unfold top
    rw [Finset.sum_eq_single_of_mem ms (Finset.mem_filter.2 ⟨hms, hmsd'⟩)]
    · rw [hms0, hms1]; simp only [pow_zero, mul_one]; rfl
    · intro m hm hne'
      exact absurd (hSd m (Finset.mem_filter.1 hm).1 (Finset.mem_filter.1 hm).2) hne'
  -- a > 0 from nonnegativity on the states (2M, M)
  have ha0 : 0 ≤ a := by
    have := coeff_nonpos_of_eventually (-(line P 2 0 1)) d
      (by rw [natDegree_neg]; exact line_natDegree _ _ _ _) (max N0 2) (fun M hM => by
        rw [eval_neg, line_eval, neg_nonpos]
        have := (hP (2 * M) M (by omega) (by omega) (by omega) (by omega)).1
        convert this using 2 <;> push_cast <;> ring)
    rw [coeff_neg, hd, line_coeff_top, htop] at this
    have : (0 : ℝ) < 2 ^ d := by positivity
    nlinarith
  have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hane)
  -- second order along the 2-cycle (3M-2, M) → (3M-1, 2M) → (3M, M)
  set G := line P 3 0 1 - line P 3 (-2) 1 with hG
  have hGdeg : G.natDegree ≤ d - 1 := by
    apply natDegree_le_pred ((natDegree_sub_le _ _).trans
      (max_le (line_natDegree _ _ _ _) (line_natDegree _ _ _ _)))
    rw [coeff_sub, line_coeff_top, line_coeff_top, sub_self]
  have hGneg := coeff_nonpos_of_eventually G (d - 1) hGdeg (max 2 N0) (fun M hM => by
    have hM2 : 2 ≤ M := le_trans (le_max_left _ _) hM
    have hMN : N0 ≤ M := le_trans (le_max_right _ _) hM
    have h1 := cycle_dbl P N0 hP 2 M 0 le_rfl hM2 hMN (by norm_num)
    have h2 := cycle_last P N0 hP 2 M le_rfl hM2 hMN
    rw [hG, eval_sub, line_eval, line_eval]
    have e1 : ev P ((2 ^ 2 - 1 : ℝ) * M + ((((0 : ℕ) : ℝ)) + 1 - (2 : ℕ))) ((2 : ℝ) ^ (0 + 1) * M) =
        ev P ((2 ^ 2 - 1 : ℝ) * M + (((2 - 1 : ℕ) : ℝ) - (2 : ℕ))) ((2 : ℝ) ^ (2 - 1) * M) := by
      norm_num
    have e2 : ev P ((2 ^ 2 - 1 : ℝ) * M + 0) ((1 : ℝ) * M) = ev P (3 * M + 0) (1 * M) := by norm_num
    have e3 : ev P ((2 ^ 2 - 1 : ℝ) * M + ((((0 : ℕ) : ℝ)) - (2 : ℕ))) ((2 : ℝ) ^ 0 * M) =
        ev P (3 * M + -2) (1 * M) := by norm_num
    rw [e1] at h1
    rw [e2] at h2
    rw [e3] at h1
    linarith)
  have hcoeff : G.coeff (d - 1) = a * (0 - 3 ^ d * ((-2 / 3) * d)) := by
    rw [hG, coeff_sub, line, line, finsetSum_coeff, finsetSum_coeff, ← Finset.sum_sub_distrib,
      Finset.sum_eq_single_of_mem ms hms]
    · rw [coeff_C_mul, coeff_C_mul, ← mul_sub, ← ha]
      congr 1
      simp only [T, hms0, hms1, pow_zero, C_1, mul_one]
      rw [coeff_p0 d hd1, coeff_pm2 d hd1]
    · intro m hm hmne
      rw [coeff_C_mul, coeff_C_mul, ← mul_sub]
      have hlt : m 0 + m 1 < d := lt_of_le_of_ne (deg_le P hm) (fun h => hmne (hSd m hm h))
      rcases Nat.lt_or_ge (m 0 + m 1) (d - 1) with h | h
      · rw [T_coeff_lt _ _ _ _ _ _ h, T_coeff_lt _ _ _ _ _ _ h, sub_self, mul_zero]
      · have he : d - 1 = m 0 + m 1 := by omega
        rw [he, T_coeff_top, T_coeff_top, sub_self, mul_zero]
  rw [hcoeff] at hGneg
  have : (0 : ℝ) < a * (0 - 3 ^ d * ((-2 / 3) * d)) := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
    have : (0 : ℝ) < 3 ^ d := by positivity
    have : 0 - 3 ^ d * ((-2 / 3) * (d : ℝ)) = 3 ^ d * (2 / 3) * d := by ring
    rw [this]; positivity
  linarith

/-- A2, stated with `MvPolynomial.eval` directly. -/
theorem no_polynomial_ranking' (P : MvPolynomial (Fin 2) ℝ) (N0 : ℕ) :
    ¬ ∀ N R : ℕ, N0 ≤ N → 2 ≤ N → 1 ≤ R → R < N →
      0 ≤ MvPolynomial.eval ![(N : ℝ), (R : ℝ)] P ∧
      (0 < 2 * R % (N + 1) →
        MvPolynomial.eval ![((N + 1 : ℕ) : ℝ), ((2 * R % (N + 1) : ℕ) : ℝ)] P <
          MvPolynomial.eval ![(N : ℝ), (R : ℝ)] P) :=
  no_polynomial_ranking P N0

end E261P



namespace Erdos261

theorem no_polynomial_ranking (P : MvPolynomial (Fin 2) ℝ) (N0 : ℕ) :
    ¬ ∀ N R : ℕ, N0 ≤ N → 2 ≤ N → 1 ≤ R → R < N →
      0 ≤ MvPolynomial.eval ![(N : ℝ), (R : ℝ)] P ∧
      (0 < 2 * R % (N + 1) →
        MvPolynomial.eval ![((N + 1 : ℕ) : ℝ), ((2 * R % (N + 1) : ℕ) : ℝ)] P <
          MvPolynomial.eval ![(N : ℝ), (R : ℝ)] P) :=
  E261P.no_polynomial_ranking' P N0

end Erdos261

open Erdos261 in
theorem solution (P : MvPolynomial (Fin 2) ℝ) (N0 : ℕ) :
    ¬ ∀ N R : ℕ, N0 ≤ N → 2 ≤ N → 1 ≤ R → R < N →
      0 ≤ MvPolynomial.eval ![(N : ℝ), (R : ℝ)] P ∧
      (0 < 2 * R % (N + 1) →
        MvPolynomial.eval ![((N + 1 : ℕ) : ℝ), ((2 * R % (N + 1) : ℕ) : ℝ)] P <
          MvPolynomial.eval ![(N : ℝ), (R : ℝ)] P) :=
  Erdos261.no_polynomial_ranking P N0

#print axioms solution
