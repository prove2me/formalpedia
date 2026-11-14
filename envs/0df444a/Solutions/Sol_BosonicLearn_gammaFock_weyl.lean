-- Prove2me | solution 1 for BosonicLearn.gammaFock_weyl
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T19:40:20.666424+00:00
-- url     : https://prove2.me/submissions/d4582e5a-c4dc-4224-a85a-8f8726b1074e

import Mathlib
import Definitions.Def_BosonicLearn_gammaFock
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open scoped Matrix

open BosonicLearn

noncomputable section

/-!
# `Γ(U)† D(z) Γ(U) = D(U†z)` in the Fock basis

Everything is rescaled so that no square roots occur until the last step:

* `cc R u w = coeff_u (∏ₖ (∑ᵢ R_ik Xᵢ)^(w_k)) = w! · gSum R u w`, so `Γ(R)_uw = √(u!/w!) · cc R u w`;
* `EE x y u v = ∏ⱼ vⱼ! · E2 xⱼ yⱼ uⱼ vⱼ`, so `∏ⱼ D(zⱼ)_{uⱼvⱼ} = e^{-|z|²/2} √(u!/v!) · EE z (-z̄) u v`.

Both kernels satisfy a ladder relation in the row index,
`(u_j + 1) c(u + e_j, w) = ∑ₖ R_jk w_k c(u, w - e_k)` (the derivative `∂/∂X_j` of the polynomial) and
`(u_k + 1) E(u + e_k, v) = v_k E(u, v - e_k) + x_k E(u, v)`.
Hence, for `A * B = 1`, the kernel `L = c_A ∘ E(x, y) ∘ c_B` (sums over photon-number sectors) satisfies
`(u_j + 1) L(u + e_j, v) = v_j L(u, v - e_j) + (A x)_j L(u, v)`, the relation of `E(A x, Bᵀ y)`; the
two agree on the row `u = 0` (evaluate the polynomial `∏ₗ (∑ᵢ B_il Xᵢ)^(v_l)` at `y`), hence everywhere.
-/

/-! ### Photon-number sectors and the index shift `w ↦ w + e_k` -/

/-- The photon-number sector `|w| = N`, written as in the statement. -/
private def sec (n N : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range (N + 1)).filter (fun w => ∑ i, w i = N)

private lemma mem_sec {n N : ℕ} (w : Fin n → ℕ) : w ∈ sec n N ↔ ∑ i, w i = N := by
  unfold sec
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun k => ?_, h⟩
    have h2 : w k ≤ ∑ i, w i :=
      Finset.single_le_sum (f := fun i => w i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    omega

private lemma sum_single_add {n : ℕ} (w : Fin n → ℕ) (k : Fin n) :
    ∑ i, (w + Pi.single k 1 : Fin n → ℕ) i = ∑ i, w i + 1 := by
  simp [Finset.sum_add_distrib]

private lemma sub_single_add {n : ℕ} (w : Fin n → ℕ) (k : Fin n) (hk : w k ≠ 0) :
    w - Pi.single k 1 + Pi.single k 1 = w := by
  funext i
  by_cases hik : i = k
  · subst hik
    show w i - (Pi.single i 1 : Fin n → ℕ) i + (Pi.single i 1 : Fin n → ℕ) i = w i
    rw [Pi.single_eq_same]
    omega
  · show w i - (Pi.single k 1 : Fin n → ℕ) i + (Pi.single k 1 : Fin n → ℕ) i = w i
    rw [Pi.single_eq_of_ne hik]
    omega

private lemma sum_sub_single {n : ℕ} (w : Fin n → ℕ) (k : Fin n) (hk : w k ≠ 0) :
    ∑ i, (w - Pi.single k 1 : Fin n → ℕ) i + 1 = ∑ i, w i := by
  have h := sum_single_add (w - Pi.single k 1) k
  rw [sub_single_add w k hk] at h
  omega

private lemma eq_zero_of_sum_eq_zero {n : ℕ} (w : Fin n → ℕ) (h : ∑ i, w i = 0) (k : Fin n) :
    w k = 0 := by
  have h2 : w k ≤ ∑ i, w i :=
    Finset.single_le_sum (f := fun i => w i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  omega

/-- Reindexing a sector sum along `w ↦ w + e_k`; the summand must vanish where `w k = 0`. -/
private lemma sum_sec_shift {n : ℕ} (N : ℕ) (k : Fin n) (h : (Fin n → ℕ) → ℂ)
    (h0 : ∀ w, w k = 0 → h w = 0) :
    ∑ w ∈ sec n (N + 1), h w = ∑ w ∈ sec n N, h (w + Pi.single k 1) := by
  symm
  refine Finset.sum_of_injOn (fun w => w + Pi.single k 1) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro a _ b _ hab
    exact add_right_cancel hab
  · intro w hw
    rw [Finset.mem_coe, mem_sec] at hw ⊢
    rw [sum_single_add, hw]
  · intro w hw hni
    apply h0
    by_contra hk
    apply hni
    refine ⟨w - Pi.single k 1, ?_, sub_single_add w k hk⟩
    rw [Finset.mem_coe, mem_sec]
    rw [mem_sec] at hw
    have := sum_sub_single w k hk
    omega

private lemma prod_split {n : ℕ} (f : Fin n → ℂ) (k : Fin n) :
    ∏ j, f j = f k * ∏ j ∈ Finset.univ.erase k, f j :=
  (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ k)).symm

/-! ### The unnormalised two-variable matrix element -/

/-- `E2 x y m n = ∑_{j ≤ min m n} x^(m-j) y^(n-j) / (j! (m-j)! (n-j)!)`; the displacement matrix is
`e^{-|z|²/2} √(m! n!) · E2 z (-z̄) m n`. -/
private def E2 (x y : ℂ) (m n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (min m n + 1),
    x ^ (m - j) * y ^ (n - j) /
      ((Nat.factorial j : ℂ) * (Nat.factorial (m - j) : ℂ) * (Nat.factorial (n - j) : ℂ))

/-- The summand of `E2`, extended by zero outside `j ≤ min m n`. -/
private def T2 (x y : ℂ) (m n j : ℕ) : ℂ :=
  if j ≤ m ∧ j ≤ n then
    x ^ (m - j) * y ^ (n - j) /
      ((Nat.factorial j : ℂ) * (Nat.factorial (m - j) : ℂ) * (Nat.factorial (n - j) : ℂ))
  else 0

private lemma E2_eq_sum_T2 (x y : ℂ) (m n N : ℕ) (hN : min m n + 1 ≤ N) :
    E2 x y m n = ∑ j ∈ Finset.range N, T2 x y m n j := by
  calc E2 x y m n = ∑ j ∈ Finset.range (min m n + 1), T2 x y m n j := by
        unfold E2
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : j ≤ min m n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [T2, if_pos ⟨le_trans hj' (min_le_left _ _), le_trans hj' (min_le_right _ _)⟩]
    _ = ∑ j ∈ Finset.range N, T2 x y m n j := by
        refine Finset.sum_subset (Finset.range_subset_range.mpr hN) fun j _ hj => ?_
        have hneg : ¬ (j ≤ m ∧ j ≤ n) := by
          rintro ⟨h1, h2⟩
          exact hj (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_min h1 h2)))
        rw [T2, if_neg hneg]

private lemma T2_succ (x y : ℂ) (m k j : ℕ) :
    ((m : ℂ) + 1) * T2 x y (m + 1) (k + 1) (j + 1) =
      T2 x y m k j + x * T2 x y m (k + 1) (j + 1) := by
  unfold T2
  by_cases hjk : j ≤ k
  · rcases lt_trichotomy j m with h | h | h
    · obtain ⟨d, rfl⟩ : ∃ d, m = j + 1 + d := ⟨m - (j + 1), by omega⟩
      obtain ⟨e, rfl⟩ : ∃ e, k = j + e := ⟨k - j, by omega⟩
      have h1 : j + 1 + d + 1 - (j + 1) = d + 1 := by omega
      have h2 : j + e + 1 - (j + 1) = e := by omega
      have h3 : j + 1 + d - j = d + 1 := by omega
      have h4 : j + e - j = e := by omega
      have h5 : j + 1 + d - (j + 1) = d := by omega
      rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩,
        h1, h2, h3, h4, h5]
      simp only [Nat.factorial_succ]
      push_cast
      have f1 : ((j.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have f2 : ((d.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have f3 : ((e.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have f4 : ((j : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero j
      have f5 : ((d : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero d
      field_simp
      ring
    · subst h
      obtain ⟨e, rfl⟩ : ∃ e, k = j + e := ⟨k - j, by omega⟩
      have h1 : j + 1 - (j + 1) = 0 := by omega
      have h2 : j + e + 1 - (j + 1) = e := by omega
      have h3 : j - j = 0 := by omega
      have h4 : j + e - j = e := by omega
      rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩, if_neg (by omega),
        h1, h2, h3, h4]
      simp only [Nat.factorial_succ, Nat.factorial_zero]
      push_cast
      have f1 : ((j.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have f3 : ((e.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have f4 : ((j : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero j
      field_simp
      ring
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp

private lemma T2_zero_succ (x y : ℂ) (m k : ℕ) :
    ((m : ℂ) + 1) * T2 x y (m + 1) (k + 1) 0 = x * T2 x y m (k + 1) 0 := by
  unfold T2
  rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩]
  simp only [Nat.sub_zero, Nat.factorial_succ, Nat.factorial_zero]
  push_cast
  have f1 : ((m.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f3 : ((k.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f4 : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
  have f5 : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  field_simp
  ring

/-- Row recursion, `k ≥ 1`. -/
private lemma E2_row_succ (x y : ℂ) (m k : ℕ) :
    ((m : ℂ) + 1) * E2 x y (m + 1) (k + 1) = E2 x y m k + x * E2 x y m (k + 1) := by
  have e1 := E2_eq_sum_T2 x y (m + 1) (k + 1) (m + k + 2 + 1) (by omega)
  have e2 := E2_eq_sum_T2 x y m k (m + k + 2) (by omega)
  have e3 := E2_eq_sum_T2 x y m (k + 1) (m + k + 2 + 1) (by omega)
  rw [Finset.sum_range_succ'] at e1 e3
  rw [e1, e2, e3, mul_add, Finset.mul_sum, mul_add, Finset.mul_sum, T2_zero_succ, ← add_assoc,
    ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j _ => T2_succ x y m k j

private lemma E2_zero_right (x y : ℂ) (m : ℕ) : E2 x y m 0 = x ^ m / (m.factorial : ℂ) := by
  simp [E2]

private lemma E2_zero_left (x y : ℂ) (n : ℕ) : E2 x y 0 n = y ^ n / (n.factorial : ℂ) := by
  simp [E2]

/-- Row recursion, `k = 0`. -/
private lemma E2_row_zero (x y : ℂ) (m : ℕ) :
    ((m : ℂ) + 1) * E2 x y (m + 1) 0 = x * E2 x y m 0 := by
  rw [E2_zero_right, E2_zero_right, Nat.factorial_succ]
  push_cast
  have f1 : ((m.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f4 : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
  field_simp
  ring

/-! ### The displacement matrix and the ladder relation in factor form -/

private lemma disp_eq (z : ℂ) (m n : ℕ) :
    displacementMatrix z m n =
      ((Real.exp (-Complex.normSq z / 2) *
        Real.sqrt ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ)) : ℝ) : ℂ) *
        E2 z (-star z) m n := rfl

/-- `E2` with the column factorial included: `Et x y m k = k! · E2 x y m k`. -/
private def Et (x y : ℂ) (m k : ℕ) : ℂ := (k.factorial : ℂ) * E2 x y m k

/-- Single-mode ladder relation in factor form. -/
private lemma Et_row (x y : ℂ) (m k : ℕ) :
    ((m : ℂ) + 1) * Et x y (m + 1) k = (k : ℂ) * Et x y m (k - 1) + x * Et x y m k := by
  unfold Et
  cases k with
  | zero =>
    have h := E2_row_zero x y m
    simp only [Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, zero_mul, zero_add, one_mul]
    linear_combination h
  | succ k =>
    have h := E2_row_succ x y m k
    rw [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    linear_combination ((k : ℂ) + 1) * (k.factorial : ℂ) * h

private lemma Et_zero_left (x y : ℂ) (k : ℕ) : Et x y 0 k = y ^ k := by
  unfold Et
  rw [E2_zero_left]
  have f1 : ((k.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

/-- The multi-mode kernel `∏ⱼ Et (xⱼ) (yⱼ) (uⱼ) (vⱼ)`. -/
private def EE {n : ℕ} (x y : Fin n → ℂ) (u v : Fin n → ℕ) : ℂ :=
  ∏ j, Et (x j) (y j) (u j) (v j)

/-- Multi-mode ladder relation. -/
private lemma EE_row {n : ℕ} (x y : Fin n → ℂ) (u v : Fin n → ℕ) (k : Fin n) :
    ((u k : ℂ) + 1) * EE x y (u + Pi.single k 1) v =
      (v k : ℂ) * EE x y u (v - Pi.single k 1) + x k * EE x y u v := by
  have e1 : EE x y (u + Pi.single k 1) v = Et (x k) (y k) (u k + 1) (v k) *
      ∏ j ∈ Finset.univ.erase k, Et (x j) (y j) (u j) (v j) := by
    unfold EE
    rw [prod_split _ k]
    congr 1
    · simp
    · exact Finset.prod_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
  have e2 : EE x y u (v - Pi.single k 1) = Et (x k) (y k) (u k) (v k - 1) *
      ∏ j ∈ Finset.univ.erase k, Et (x j) (y j) (u j) (v j) := by
    unfold EE
    rw [prod_split _ k]
    congr 1
    · simp
    · exact Finset.prod_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
  have e3 : EE x y u v = Et (x k) (y k) (u k) (v k) *
      ∏ j ∈ Finset.univ.erase k, Et (x j) (y j) (u j) (v j) := by
    unfold EE
    rw [prod_split _ k]
  rw [e1, e2, e3]
  linear_combination (∏ j ∈ Finset.univ.erase k, Et (x j) (y j) (u j) (v j)) *
    Et_row (x k) (y k) (u k) (v k)

private lemma EE_zero_left {n : ℕ} (x y : Fin n → ℂ) (v : Fin n → ℕ) :
    EE x y 0 v = ∏ j, y j ^ v j := by
  unfold EE
  exact Finset.prod_congr rfl fun j _ => Et_zero_left _ _ _

/-! ### The combinatorial sum of `gammaFock` and its polynomial model -/

/-- The index set of `gammaFock`: matrices `M ∈ ℕ^{n×n}` with row sums `u` and column sums `v`. -/
private def gS {n : ℕ} (u v : Fin n → ℕ) : Finset (Fin n → Fin n → ℕ) :=
  (Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin n => Finset.range (u i + 1)).filter
    (fun M => (∀ i, ∑ j, M i j = u i) ∧ ∀ j, ∑ i, M i j = v j)

/-- The box constraint is automatic. -/
private lemma mem_gS {n : ℕ} (u v : Fin n → ℕ) (M : Fin n → Fin n → ℕ) :
    M ∈ gS u v ↔ (∀ i, ∑ j, M i j = u i) ∧ ∀ j, ∑ i, M i j = v j := by
  unfold gS
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i j => ?_, h⟩
    have h1 : M i j ≤ ∑ j, M i j :=
      Finset.single_le_sum (f := fun j => M i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [h.1 i] at h1
    omega

/-- The combinatorial sum in `gammaFock`. -/
private def gSum {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) : ℂ :=
  ∑ M ∈ gS u v, ∏ i, ∏ j, R i j ^ (M i j) / (Nat.factorial (M i j) : ℂ)

private lemma gammaFock_eq {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) :
    gammaFock R u v =
      (Real.sqrt ((∏ i, (Nat.factorial (u i) : ℝ)) * ∏ j, (Nat.factorial (v j) : ℝ)) : ℂ) *
        gSum R u v := rfl

/-- No matrix has row sums `u` and column sums `v` unless the totals agree. -/
private lemma gS_eq_empty {n : ℕ} (u v : Fin n → ℕ) (h : ∑ i, u i ≠ ∑ i, v i) : gS u v = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro M hM
  rw [mem_gS] at hM
  apply h
  calc ∑ i, u i = ∑ i, ∑ j, M i j := Finset.sum_congr rfl fun i _ => (hM.1 i).symm
    _ = ∑ j, ∑ i, M i j := Finset.sum_comm
    _ = ∑ j, v j := Finset.sum_congr rfl fun j _ => hM.2 j

private lemma gSum_eq_zero {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ)
    (h : ∑ i, u i ≠ ∑ i, v i) : gSum R u v = 0 := by
  unfold gSum
  rw [gS_eq_empty u v h, Finset.sum_empty]

/-! ### The polynomial model: `Γ(R)` is `f(y) ↦ f(Rᵀ y)` on polynomials. -/

/-- The linear form `∑ i, R i j * y i`. -/
private def linForm {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : MvPolynomial (Fin n) ℂ :=
  ∑ i, MvPolynomial.C (R i j) * MvPolynomial.X i

/-- `∏ j, (∑ i, R i j * y i) ^ v j`. -/
private def polyP {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℕ) :
    MvPolynomial (Fin n) ℂ :=
  ∏ j, linForm R j ^ v j

/-- Multinomial expansion of `polyP R v` into monomials. -/
private lemma polyP_expand {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℕ) :
    polyP R v =
      ∑ K ∈ Fintype.piFinset (fun j : Fin n => Finset.piAntidiag (Finset.univ : Finset (Fin n)) (v j)),
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => ∑ j, K j i)
          (∏ j, ((Nat.multinomial Finset.univ (K j) : ℕ) : ℂ) * ∏ i, R i j ^ K j i) := by
  unfold polyP linForm
  simp only [Finset.sum_pow_eq_sum_piAntidiag]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero (MvPolynomial.X i))]
  simp only [Finsupp.equivFunOnFinite_symm_apply_apply, mul_pow, Finset.prod_mul_distrib, map_mul,
    map_prod, map_pow, map_natCast]
  rw [← mul_assoc]
  congr 1
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_pow_eq_pow_sum]

/-- Step (a): the coefficients of `polyP R v` are the combinatorial sums of `gammaFock`. -/
private lemma coeff_polyP {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm u) (polyP R v) =
      (∏ j, ((Nat.factorial (v j) : ℕ) : ℂ)) * gSum R u v := by
  classical
  rw [polyP_expand, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Equiv.apply_eq_iff_eq]
  rw [← Finset.sum_filter]
  unfold gSum
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun K i j => K j i) (fun M j i => M i j) ?_ ?_ ?_ ?_ ?_
  · intro K hK
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hK
    rw [mem_gS]
    refine ⟨fun i => congrFun hK.2 i, fun j => ?_⟩
    exact (Finset.mem_piAntidiag.mp (hK.1 j)).1
  · intro M hM
    rw [mem_gS] at hM
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun j => ?_, funext fun i => hM.1 i⟩
    rw [Finset.mem_piAntidiag]
    exact ⟨hM.2 j, fun _ _ => Finset.mem_univ _⟩
  · intro K _
    rfl
  · intro M _
    rfl
  · intro K hK
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hK
    have hcol : ∀ j, ∑ i, K j i = v j := fun j => (Finset.mem_piAntidiag.mp (hK.1 j)).1
    rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin n)) (K j)
    rw [hcol j] at hspec
    have hspec' : (∏ i, ((Nat.factorial (K j i) : ℕ) : ℂ)) *
        ((Nat.multinomial Finset.univ (K j) : ℕ) : ℂ) = ((Nat.factorial (v j) : ℕ) : ℂ) := by
      exact_mod_cast hspec
    have hne : (∏ i, ((Nat.factorial (K j i) : ℕ) : ℂ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [← hspec', Finset.prod_div_distrib]
    field_simp

/-! ### Ladder relation for the coefficients of `polyP` -/

/-- `cc R u w = coeff_u (polyP R w) = w! · gSum R u w`. -/
private def cc {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (u w : Fin n → ℕ) : ℂ :=
  MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm u) (polyP R w)

private lemma cc_eq {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (u w : Fin n → ℕ) :
    cc R u w = (∏ j, ((Nat.factorial (w j) : ℕ) : ℂ)) * gSum R u w :=
  coeff_polyP R u w

private lemma cc_eq_zero {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (u w : Fin n → ℕ)
    (h : ∑ i, u i ≠ ∑ i, w i) : cc R u w = 0 := by
  rw [cc_eq, gSum_eq_zero R u w h, mul_zero]

private lemma cc_zero_zero {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) : cc R 0 0 = 1 := by
  have e : (Finsupp.equivFunOnFinite.symm (0 : Fin n → ℕ)) = 0 := by
    ext i
    simp
  unfold cc polyP
  rw [e]
  simp

private lemma pderiv_linForm {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (j k : Fin n) :
    MvPolynomial.pderiv j (linForm R k) = MvPolynomial.C (R j k) := by
  classical
  unfold linForm
  simp only [map_sum, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · intro h
    exact absurd (Finset.mem_univ j) h

private lemma pderiv_prod {n : ℕ} (j : Fin n) (s : Finset (Fin n))
    (f : Fin n → MvPolynomial (Fin n) ℂ) :
    MvPolynomial.pderiv j (∏ k ∈ s, f k) =
      ∑ k ∈ s, (∏ l ∈ s.erase k, f l) * MvPolynomial.pderiv j (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, MvPolynomial.pderiv_mul, ih, Finset.sum_insert ha,
      Finset.erase_insert ha, Finset.mul_sum]
    refine congrArg₂ (· + ·) (mul_comm _ _) (Finset.sum_congr rfl fun k hk => ?_)
    have hak : a ≠ k := fun h => ha (h ▸ hk)
    rw [Finset.erase_insert_of_ne hak,
      Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    ring

private lemma polyP_sub_single {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℕ)
    (k : Fin n) :
    polyP R (w - Pi.single k 1) =
      linForm R k ^ (w k - 1) * ∏ l ∈ Finset.univ.erase k, linForm R l ^ w l := by
  unfold polyP
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  congr 1
  · simp
  · exact Finset.prod_congr rfl fun l hl => by simp [Finset.ne_of_mem_erase hl]

private lemma pderiv_polyP {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℕ) (j : Fin n) :
    MvPolynomial.pderiv j (polyP R w) =
      ∑ k, MvPolynomial.C (R j k * (w k : ℂ)) * polyP R (w - Pi.single k 1) := by
  conv_lhs => unfold polyP
  rw [pderiv_prod]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MvPolynomial.pderiv_pow, pderiv_linForm, polyP_sub_single, map_mul, map_natCast]
  ring

/-- Ladder relation: `(u_j + 1) c(u + e_j, w) = ∑ₖ R_jk w_k c(u, w - e_k)`. -/
private lemma cc_ladder {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (u w : Fin n → ℕ) (j : Fin n) :
    ((u j : ℂ) + 1) * cc R (u + Pi.single j 1) w =
      ∑ k, R j k * (w k : ℂ) * cc R u (w - Pi.single k 1) := by
  have h := congrArg (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm u)) (pderiv_polyP R w j)
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_sum] at h
  simp only [MvPolynomial.coeff_C_mul] at h
  have e : Finsupp.equivFunOnFinite.symm u + Finsupp.single j 1 =
      Finsupp.equivFunOnFinite.symm (u + Pi.single j 1) := by
    ext i
    simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
  rw [e] at h
  unfold cc
  rw [← h]
  simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
  ring

/-- A sum over the support of `polyP B v` is a sum over the sector of `v`. -/
private lemma sum_support_polyP {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℕ)
    (f : (Fin n → ℕ) → ℂ) :
    ∑ d ∈ (polyP B v).support, MvPolynomial.coeff d (polyP B v) * f d =
      ∑ w ∈ sec n (∑ i, v i), cc B w v * f w := by
  refine Finset.sum_of_injOn (fun d => (d : Fin n → ℕ)) ?_ ?_ ?_ ?_
  · intro a _ b _ h
    exact DFunLike.coe_injective h
  · intro d hd
    rw [Finset.mem_coe, MvPolynomial.mem_support_iff] at hd
    rw [Finset.mem_coe, mem_sec]
    by_contra hne
    apply hd
    have h := cc_eq_zero B (d : Fin n → ℕ) v hne
    unfold cc at h
    rwa [Finsupp.equivFunOnFinite_symm_coe] at h
  · intro w _ hw
    have h : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm w) (polyP B v) = 0 := by
      by_contra hne
      apply hw
      refine ⟨Finsupp.equivFunOnFinite.symm w, ?_, rfl⟩
      rw [Finset.mem_coe, MvPolynomial.mem_support_iff]
      exact hne
    unfold cc
    rw [h, zero_mul]
  · intro d _
    unfold cc
    rw [Finsupp.equivFunOnFinite_symm_coe]


/-! ### The half-transformed kernel `F = c_A ∘ E` and its recursion -/

/-- `FF A x y u w' = ∑_{|w| = |u|} c_A(u, w) · E(x, y)(w, w')`. -/
private def FF {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) (u w' : Fin n → ℕ) : ℂ :=
  ∑ w ∈ sec n (∑ i, u i), cc A u w * EE x y w w'

private lemma FF_rec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ)
    (u w' : Fin n → ℕ) (j : Fin n) :
    ((u j : ℂ) + 1) * FF A x y (u + Pi.single j 1) w' =
      ∑ k, A j k * ((w' k : ℂ) * FF A x y u (w' - Pi.single k 1) + x k * FF A x y u w') := by
  unfold FF
  rw [sum_single_add, Finset.mul_sum]
  have h1 : ∀ w : Fin n → ℕ, ((u j : ℂ) + 1) * (cc A (u + Pi.single j 1) w * EE x y w w') =
      ∑ k, A j k * (w k : ℂ) * cc A u (w - Pi.single k 1) * EE x y w w' := by
    intro w
    rw [← mul_assoc, cc_ladder, Finset.sum_mul]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine (sum_sec_shift _ k _ ?_).trans ?_
  · intro w hw
    simp [hw]
  · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hr := EE_row x y w w' k
    simp only [Pi.add_apply, Pi.single_eq_same, add_tsub_cancel_right, Nat.cast_add, Nat.cast_one]
    linear_combination A j k * cc A u w * hr

private lemma FF_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ)
    (w' : Fin n → ℕ) : FF A x y 0 w' = ∏ j, y j ^ w' j := by
  unfold FF
  have hs : sec n (∑ i, (0 : Fin n → ℕ) i) = {0} := by
    ext w
    rw [mem_sec, Finset.mem_singleton]
    constructor
    · intro h
      funext i
      exact eq_zero_of_sum_eq_zero w (by simpa using h) i
    · intro h
      rw [h]
  rw [hs, Finset.sum_singleton, cc_zero_zero, one_mul, EE_zero_left]

/-! ### The full kernel `L = c_A ∘ E ∘ c_B` and its recursion -/

/-- `LL A B x y u v = ∑_{|w'| = |v|} F(u, w') · c_B(w', v)`. -/
private def LL {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) (u v : Fin n → ℕ) : ℂ :=
  ∑ w' ∈ sec n (∑ i, v i), FF A x y u w' * cc B w' v

private lemma LL_shift {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ)
    (u v : Fin n → ℕ) (k : Fin n) :
    ∑ w' ∈ sec n (∑ i, v i), (w' k : ℂ) * FF A x y u (w' - Pi.single k 1) * cc B w' v =
      ∑ l, B k l * (v l : ℂ) * LL A B x y u (v - Pi.single l 1) := by
  rcases Nat.eq_zero_or_pos (∑ i, v i) with h0 | hpos
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro l _
      simp [eq_zero_of_sum_eq_zero v h0 l]
    · intro w' hw'
      rw [mem_sec, h0] at hw'
      simp [eq_zero_of_sum_eq_zero w' hw' k]
  · obtain ⟨M, hM⟩ : ∃ M, ∑ i, v i = M + 1 := ⟨∑ i, v i - 1, by omega⟩
    rw [hM]
    refine (sum_sec_shift M k _ ?_).trans ?_
    · intro w hw
      simp [hw]
    · have h1 : ∀ w : Fin n → ℕ,
          (((w + Pi.single k 1 : Fin n → ℕ) k : ℕ) : ℂ) *
            FF A x y u (w + Pi.single k 1 - Pi.single k 1) * cc B (w + Pi.single k 1) v =
          ∑ l, B k l * (v l : ℂ) * (FF A x y u w * cc B w (v - Pi.single l 1)) := by
        intro w
        have hl := cc_ladder B w v k
        simp only [Pi.add_apply, Pi.single_eq_same, add_tsub_cancel_right, Nat.cast_add,
          Nat.cast_one]
        calc ((w k : ℂ) + 1) * FF A x y u w * cc B (w + Pi.single k 1) v
            = FF A x y u w * (((w k : ℂ) + 1) * cc B (w + Pi.single k 1) v) := by ring
          _ = _ := by
            rw [hl, Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
      simp only [h1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Finset.mul_sum]
      by_cases hl : v l = 0
      · simp [hl]
      · have hs : ∑ i, (v - Pi.single l 1 : Fin n → ℕ) i = M := by
          have := sum_sub_single v l hl
          omega
        unfold LL
        rw [hs]

private lemma LL_rec {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1)
    (x y : Fin n → ℂ) (u v : Fin n → ℕ) (j : Fin n) :
    ((u j : ℂ) + 1) * LL A B x y (u + Pi.single j 1) v =
      (v j : ℂ) * LL A B x y u (v - Pi.single j 1) + (A *ᵥ x) j * LL A B x y u v := by
  have key : ((u j : ℂ) + 1) * LL A B x y (u + Pi.single j 1) v =
      ∑ k, A j k * ((∑ w' ∈ sec n (∑ i, v i),
        (w' k : ℂ) * FF A x y u (w' - Pi.single k 1) * cc B w' v) + x k * LL A B x y u v) := by
    calc ((u j : ℂ) + 1) * LL A B x y (u + Pi.single j 1) v
        = ∑ w' ∈ sec n (∑ i, v i), ∑ k, A j k *
            ((w' k : ℂ) * FF A x y u (w' - Pi.single k 1) * cc B w' v +
              x k * (FF A x y u w' * cc B w' v)) := by
          unfold LL
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun w' _ => ?_
          rw [← mul_assoc, FF_rec, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          unfold LL
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have T1 : ∑ k, A j k * ∑ l, B k l * (v l : ℂ) * LL A B x y u (v - Pi.single l 1) =
      (v j : ℂ) * LL A B x y u (v - Pi.single j 1) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ l, ∑ k, A j k * (B k l * (v l : ℂ) * LL A B x y u (v - Pi.single l 1)) =
        (A * B) j l * ((v l : ℂ) * LL A B x y u (v - Pi.single l 1)) := by
      intro l
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    simp only [h2, hAB, Matrix.one_apply]
    simp
  have T2 : ∑ k, A j k * (x k * LL A B x y u v) = (A *ᵥ x) j * LL A B x y u v := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [key]
  simp only [LL_shift, mul_add, Finset.sum_add_distrib]
  rw [T1, T2]

private lemma LL_zero {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ)
    (v : Fin n → ℕ) :
    LL A B x y 0 v = ∏ l, (∑ i, B i l * y i) ^ v l := by
  unfold LL
  simp only [FF_zero]
  have h := sum_support_polyP B v (fun w => ∏ j, y j ^ w j)
  have he : MvPolynomial.eval y (polyP B v) = ∏ l, (∑ i, B i l * y i) ^ v l := by
    unfold polyP linForm
    simp [map_prod, map_pow, map_sum]
  rw [← he, MvPolynomial.eval_eq', h]
  exact Finset.sum_congr rfl fun w _ => mul_comm _ _

/-- Uniqueness: `L` and `E(Ax, Bᵀy)` satisfy the same recursion and agree on row zero. -/
private lemma LL_eq {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1)
    (x y : Fin n → ℂ) :
    ∀ (N : ℕ) (u : Fin n → ℕ), ∑ i, u i = N → ∀ v : Fin n → ℕ,
      LL A B x y u v = EE (A *ᵥ x) (fun l => ∑ i, B i l * y i) u v := by
  intro N
  induction N with
  | zero =>
    intro u hu v
    have hu0 : u = 0 := funext fun i => eq_zero_of_sum_eq_zero u hu i
    subst hu0
    rw [LL_zero, EE_zero_left]
  | succ N ih =>
    intro u hu v
    obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have h0 : ∑ i, u i = 0 := Finset.sum_eq_zero fun i _ => hcon i
      omega
    have hu' : ∑ i, (u - Pi.single j 1 : Fin n → ℕ) i = N := by
      have := sum_sub_single u j hj
      omega
    have e := sub_single_add u j hj
    have h1 := LL_rec A B hAB x y (u - Pi.single j 1) v j
    have h2 := EE_row (A *ᵥ x) (fun l => ∑ i, B i l * y i) (u - Pi.single j 1) v j
    rw [e] at h1 h2
    rw [ih _ hu' v, ih _ hu' (v - Pi.single j 1)] at h1
    have hne : (((u - Pi.single j 1 : Fin n → ℕ) j : ℕ) : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
    exact mul_left_cancel₀ hne (h1.trans h2.symm)


/-! ### Back to the normalised matrices -/

/-- `√(u!) = ∏ᵢ √(uᵢ!)`. -/
private def sf {n : ℕ} (u : Fin n → ℕ) : ℝ := ∏ i, Real.sqrt ((u i).factorial : ℝ)

private lemma sf_pos {n : ℕ} (u : Fin n → ℕ) : 0 < sf u :=
  Finset.prod_pos fun _ _ => Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos _))

private lemma sf_mul_self {n : ℕ} (u : Fin n → ℕ) :
    sf u * sf u = ∏ i, ((u i).factorial : ℝ) := by
  unfold sf
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => Real.mul_self_sqrt (Nat.cast_nonneg _)

private lemma sqrt_fact_mul {n : ℕ} (u w : Fin n → ℕ) :
    Real.sqrt ((∏ i, ((u i).factorial : ℝ)) * ∏ j, ((w j).factorial : ℝ)) = sf u * sf w := by
  rw [← sf_mul_self u, ← sf_mul_self w,
    show sf u * sf u * (sf w * sf w) = (sf u * sf w) * (sf u * sf w) by ring]
  exact Real.sqrt_mul_self (mul_nonneg (sf_pos u).le (sf_pos w).le)

private lemma gammaFock_mul_sf {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (u w : Fin n → ℕ) :
    gammaFock R u w * (sf w : ℂ) = (sf u : ℂ) * cc R u w := by
  have h : ((sf w : ℝ) : ℂ) * ((sf w : ℝ) : ℂ) = ∏ j, (((w j).factorial : ℕ) : ℂ) := by
    rw [← Complex.ofReal_mul, sf_mul_self]
    simp
  rw [gammaFock_eq, cc_eq, sqrt_fact_mul, ← h, Complex.ofReal_mul]
  ring

private lemma disp_prod_mul_sf {n : ℕ} (z : Fin n → ℂ) (w w' : Fin n → ℕ) :
    (∏ j, displacementMatrix (z j) (w j) (w' j)) * ((sf w' : ℝ) : ℂ) =
      ((Real.exp (-(∑ j, Complex.normSq (z j)) / 2) : ℝ) : ℂ) * ((sf w : ℝ) : ℂ) *
        EE z (fun j => -star (z j)) w w' := by
  have hexp : ((Real.exp (-(∑ j, Complex.normSq (z j)) / 2) : ℝ) : ℂ) =
      ∏ j, ((Real.exp (-Complex.normSq (z j) / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod, ← Real.exp_sum]
    congr 2
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  unfold sf EE
  rw [hexp, Complex.ofReal_prod, Complex.ofReal_prod, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hk : ((Real.sqrt ((w' j).factorial : ℝ) : ℝ) : ℂ) *
      ((Real.sqrt ((w' j).factorial : ℝ) : ℝ) : ℂ) = ((w' j).factorial : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  rw [disp_eq, Et, Real.sqrt_mul (Nat.cast_nonneg _), ← hk]
  simp only [Complex.ofReal_mul]
  ring

/-- An isometry preserves `∑ⱼ |zⱼ|²`. -/
private lemma normSq_sum_unitary {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * Uᴴ = 1)
    (z : Fin n → ℂ) :
    ∑ j, Complex.normSq ((Uᴴ *ᵥ z) j) = ∑ j, Complex.normSq (z j) := by
  have h : star (Uᴴ *ᵥ z) ⬝ᵥ (Uᴴ *ᵥ z) = star z ⬝ᵥ z := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, hU, Matrix.vecMul_one]
  have h2 : ∀ a : Fin n → ℂ, star a ⬝ᵥ a = ((∑ j, Complex.normSq (a j) : ℝ) : ℂ) := by
    intro a
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    rfl
  rw [h2, h2] at h
  exact_mod_cast h

theorem solution {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) (z : Fin n → ℂ)
    (u v : Occupation (Fin n)) :
    ∑ w ∈ (Fintype.piFinset fun _ : Fin n => Finset.range (∑ i, u i + 1)).filter
        (fun w => ∑ i, w i = ∑ i, u i),
      ∑ w' ∈ (Fintype.piFinset fun _ : Fin n => Finset.range (∑ i, v i + 1)).filter
        (fun w' => ∑ i, w' i = ∑ i, v i),
        gammaFock Uᴴ u w * (∏ j, displacementMatrix (z j) (w j) (w' j)) * gammaFock U w' v =
      ∏ j, displacementMatrix ((Uᴴ *ᵥ z) j) (u j) (v j) := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hsv : ((sf v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sf_pos v).ne'
  have hy : (fun j => -star ((Uᴴ *ᵥ z) j)) = fun l => ∑ i, U i l * (-star (z i)) := by
    funext l
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_sum, star_mul',
      star_star, mul_neg, Finset.sum_neg_distrib]
  apply mul_right_cancel₀ hsv
  rw [disp_prod_mul_sf, normSq_sum_unitary U hU' z, hy,
    ← LL_eq Uᴴ U hU z (fun i => -star (z i)) _ u rfl v]
  calc (∑ w ∈ sec n (∑ i, u i), ∑ w' ∈ sec n (∑ i, v i),
        gammaFock Uᴴ u w * (∏ j, displacementMatrix (z j) (w j) (w' j)) * gammaFock U w' v) *
          ((sf v : ℝ) : ℂ)
      = ∑ w ∈ sec n (∑ i, u i), ∑ w' ∈ sec n (∑ i, v i),
          ((Real.exp (-(∑ j, Complex.normSq (z j)) / 2) : ℝ) : ℂ) * ((sf u : ℝ) : ℂ) *
            (cc Uᴴ u w * EE z (fun i => -star (z i)) w w' * cc U w' v) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun w' _ => ?_
        have g1 := gammaFock_mul_sf Uᴴ u w
        have g2 := disp_prod_mul_sf z w w'
        have g3 := gammaFock_mul_sf U w' v
        linear_combination gammaFock Uᴴ u w * (∏ j, displacementMatrix (z j) (w j) (w' j)) * g3 +
          gammaFock Uᴴ u w * cc U w' v * g2 +
          ((Real.exp (-(∑ j, Complex.normSq (z j)) / 2) : ℝ) : ℂ) *
            EE z (fun i => -star (z i)) w w' * cc U w' v * g1
    _ = _ := by
        unfold LL FF
        rw [Finset.mul_sum, Finset.sum_comm]
        refine Finset.sum_congr rfl fun w' _ => ?_
        rw [Finset.sum_mul, Finset.mul_sum]
