-- Prove2me | solution 1 for BosonicLearn.gammaFock_mul
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T19:11:12.933399+00:00
-- url     : https://prove2.me/submissions/4c2d48d8-6e47-4250-a1ab-18c8b1a5a975

import Mathlib
import Definitions.Def_BosonicLearn_gammaFock

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Matrix

open BosonicLearn

noncomputable section

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

/-! ### Step (b): substitution. -/

private lemma linForm_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    linForm (A * B) j = MvPolynomial.aeval (fun k => linForm A k) (linForm B j) := by
  unfold linForm
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Matrix.mul_apply,
    MvPolynomial.algebraMap_eq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

private lemma polyP_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℕ) :
    polyP (A * B) v = MvPolynomial.aeval (fun k => linForm A k) (polyP B v) := by
  unfold polyP
  simp only [map_prod, map_pow, linForm_mul]

private lemma aeval_monomial_polyP {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (w : Fin n →₀ ℕ)
    (c : ℂ) :
    MvPolynomial.aeval (fun k => linForm A k) (MvPolynomial.monomial w c) =
      MvPolynomial.C c * polyP A w := by
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero (linForm A i)),
    MvPolynomial.algebraMap_eq]
  rfl

private lemma coeff_polyP_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℕ)
    (m : Fin n →₀ ℕ) :
    MvPolynomial.coeff m (polyP (A * B) v) =
      ∑ w ∈ (polyP B v).support,
        MvPolynomial.coeff w (polyP B v) * MvPolynomial.coeff m (polyP A w) := by
  rw [polyP_mul]
  conv_lhs => rw [MvPolynomial.as_sum (polyP B v)]
  simp only [map_sum, aeval_monomial_polyP, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]

/-- The combinatorial form of multiplicativity. -/
private lemma gSum_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) :
    gSum (A * B) u v =
      ∑ w ∈ (Fintype.piFinset fun _ : Fin n => Finset.range (∑ i, u i + 1)).filter
          (fun w => ∑ i, w i = ∑ i, u i),
        (∏ k, ((Nat.factorial (w k) : ℕ) : ℂ)) * gSum A u w * gSum B w v := by
  have hv : (∏ j, ((Nat.factorial (v j) : ℕ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hcoefB : ∀ w : Fin n →₀ ℕ, MvPolynomial.coeff w (polyP B v) =
      (∏ j, ((Nat.factorial (v j) : ℕ) : ℂ)) * gSum B w v := by
    intro w
    rw [← coeff_polyP, Finsupp.equivFunOnFinite_symm_coe]
  have h1 : (∏ j, ((Nat.factorial (v j) : ℕ) : ℂ)) * gSum (A * B) u v =
      (∏ j, ((Nat.factorial (v j) : ℕ) : ℂ)) *
        ∑ w ∈ (polyP B v).support,
          (∏ k, ((Nat.factorial (w k) : ℕ) : ℂ)) * gSum A u w * gSum B w v := by
    rw [← coeff_polyP, coeff_polyP_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hcoefB w, coeff_polyP]
    ring
  rw [mul_left_cancel₀ hv h1]
  refine Finset.sum_bij_ne_zero (fun w _ _ => (w : Fin n → ℕ)) ?_ ?_ ?_ ?_
  · intro w _ hne
    have hsum : ∑ i, u i = ∑ i, w i := by
      by_contra hcon
      apply hne
      rw [gSum_eq_zero A u w hcon, mul_zero, zero_mul]
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun k => ?_, hsum.symm⟩
    rw [Finset.mem_range, hsum]
    have h2 : w k ≤ ∑ i, w i :=
      Finset.single_le_sum (f := fun i => w i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    omega
  · intro w₁ _ _ w₂ _ _ h
    exact DFunLike.coe_injective h
  · intro w _ hne
    refine ⟨Finsupp.equivFunOnFinite.symm w, ?_, ?_, rfl⟩
    · rw [MvPolynomial.mem_support_iff, hcoefB]
      intro hzero
      apply hne
      rcases mul_eq_zero.mp hzero with h0 | h0
      · exact absurd h0 hv
      · rw [Finsupp.coe_equivFunOnFinite_symm] at h0
        rw [h0, mul_zero]
    · simpa using hne
  · intro w _ _
    rfl

theorem solution {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (u v : Occupation (Fin n)) :
    gammaFock (A * B) u v =
      ∑ w ∈ (Fintype.piFinset fun _ : Fin n => Finset.range (∑ i, u i + 1)).filter
          (fun w => ∑ i, w i = ∑ i, u i),
        gammaFock A u w * gammaFock B w v := by
  rw [gammaFock_eq, gSum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [gammaFock_eq, gammaFock_eq]
  have hu : (0 : ℝ) ≤ ∏ i, (Nat.factorial (u i) : ℝ) :=
    Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
  have hw : (0 : ℝ) ≤ ∏ i, (Nat.factorial (w i) : ℝ) :=
    Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
  have hsq : Real.sqrt ((∏ i, (Nat.factorial (u i) : ℝ)) * ∏ j, (Nat.factorial (w j) : ℝ)) *
      Real.sqrt ((∏ i, (Nat.factorial (w i) : ℝ)) * ∏ j, (Nat.factorial (v j) : ℝ)) =
      Real.sqrt ((∏ i, (Nat.factorial (u i) : ℝ)) * ∏ j, (Nat.factorial (v j) : ℝ)) *
        ∏ k, (Nat.factorial (w k) : ℝ) := by
    rw [Real.sqrt_mul hu, Real.sqrt_mul hw, Real.sqrt_mul hu]
    calc Real.sqrt (∏ i, (Nat.factorial (u i) : ℝ)) * Real.sqrt (∏ j, (Nat.factorial (w j) : ℝ)) *
          (Real.sqrt (∏ i, (Nat.factorial (w i) : ℝ)) * Real.sqrt (∏ j, (Nat.factorial (v j) : ℝ)))
        = Real.sqrt (∏ i, (Nat.factorial (u i) : ℝ)) * Real.sqrt (∏ j, (Nat.factorial (v j) : ℝ)) *
          (Real.sqrt (∏ i, (Nat.factorial (w i) : ℝ)) * Real.sqrt (∏ j, (Nat.factorial (w j) : ℝ))) := by
          ring
      _ = _ := by rw [Real.mul_self_sqrt hw]
  have hsqC := congrArg (fun x : ℝ => (x : ℂ)) hsq
  simp only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_natCast] at hsqC
  calc _ = ((Real.sqrt ((∏ i, (Nat.factorial (u i) : ℝ)) * ∏ j, (Nat.factorial (v j) : ℝ)) : ℂ) *
          ∏ k, ((Nat.factorial (w k) : ℕ) : ℂ)) * (gSum A u w * gSum B w v) := by ring
    _ = _ := by rw [← hsqC]; ring
