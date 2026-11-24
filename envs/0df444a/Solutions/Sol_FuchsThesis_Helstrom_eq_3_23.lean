-- Prove2me | solution 1 for FuchsThesis.Helstrom.eq_3_23
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T20:53:07.857885+00:00
-- url     : https://prove2.me/submissions/aa4cc8bf-59e8-4da4-9f73-32b944834c6a

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_FuchsThesis_Helstrom_bayesError
import Definitions.Def_FuchsThesis_Helstrom_qErrorProb
import Definitions.Def_FuchsThesis_Helstrom_gammaOp

set_option autoImplicit false

open scoped ComplexOrder
open FuchsThesis.Helstrom

/-- `re tr(A F) = ∑ γ_j re (Uᴴ F U)_{jj}` in the eigenbasis of the Hermitian `A`. -/
private lemma re_trace_mul_eigen {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (F : Matrix n n ℂ) :
    (A * F).trace.re = ∑ j, hA.eigenvalues j *
      ((star (hA.eigenvectorUnitary : Matrix n n ℂ) * F *
        (hA.eigenvectorUnitary : Matrix n n ℂ)) j j).re := by
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  set D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  conv_lhs => rw [h]
  rw [show U * D * star U * F = (U * D) * (star U * F) by simp [Matrix.mul_assoc],
    Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp only [hD, Matrix.trace, Matrix.diag, Matrix.mul_diagonal, Complex.re_sum,
    Function.comp_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re, mul_comm]

/-- Diagonal entries of `Uᴴ E U` have nonnegative real part when `E` is PSD. -/
private lemma diag_re_nonneg {n : Type} [Fintype n] {E : Matrix n n ℂ} (U : Matrix n n ℂ)
    (hE : E.PosSemidef) (j : n) : 0 ≤ ((star U * E * U) j j).re := by
  have h := (hE.conjTranspose_mul_mul_same U).diag_nonneg (i := j)
  rw [Matrix.star_eq_conjTranspose]
  simpa using (Complex.le_def.1 h).1

private lemma sum_re_trace {n : Type} [Fintype n] [DecidableEq n] {m : ℕ} (ρ : Matrix n n ℂ)
    (hρ : ρ.trace = 1) (E : Fin m → Matrix n n ℂ) (hE : ∑ b, E b = 1) :
    ∑ b, (ρ * E b).trace.re = 1 := by
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum, hE, Matrix.mul_one, hρ,
    Complex.one_re]

private lemma sum_diag_re {n : Type} [Fintype n] [DecidableEq n] {m : ℕ} (U : Matrix n n ℂ)
    (hU : star U * U = 1) (E : Fin m → Matrix n n ℂ) (hE : ∑ b, E b = 1) (j : n) :
    ∑ b, ((star U * E b * U) j j).re = 1 := by
  have h : ∑ b, star U * E b * U = 1 := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hE, Matrix.mul_one, hU]
  have := congrArg (fun M : Matrix n n ℂ => (M j j).re) h
  simpa [Matrix.sum_apply, Complex.re_sum] using this

private lemma gamma_re {n : Type} [Fintype n] (π0 π1 : ℝ) (ρ0 ρ1 F : Matrix n n ℂ) :
    (gammaOp π0 π1 ρ0 ρ1 * F).trace.re =
      π1 * (ρ1 * F).trace.re - π0 * (ρ0 * F).trace.re := by
  simp [gammaOp, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_smul]

/-- Step 1: every POVM has Bayes error at least `π₀ + ∑ min(γ_j, 0)`. -/
private lemma lower_bound {n : Type} [Fintype n] [DecidableEq n] {π0 π1 : ℝ}
    {ρ0 ρ1 : Matrix n n ℂ} (h0 : WildeQIT.IsDensityOperator ρ0)
    (hΓ : (gammaOp π0 π1 ρ0 ρ1).IsHermitian) {m : ℕ} (E : Fin m → Matrix n n ℂ)
    (hE : FuchsVdGraaf.IsPOVM E) :
    π0 + ∑ j, min (hΓ.eigenvalues j) 0 ≤ bayesError π0 π1 ρ0 ρ1 E := by
  have hU : star (hΓ.eigenvectorUnitary : Matrix n n ℂ) * hΓ.eigenvectorUnitary = 1 := by
    rw [← Unitary.coe_star]; exact Unitary.coe_star_mul_self _
  obtain ⟨g, hg⟩ : ∃ g : Fin m → n → ℝ, ∀ b j, g b j =
      ((star (hΓ.eigenvectorUnitary : Matrix n n ℂ) * E b *
        (hΓ.eigenvectorUnitary : Matrix n n ℂ)) j j).re := ⟨_, fun _ _ => rfl⟩
  have hg0 : ∀ b j, 0 ≤ g b j := fun b j => by rw [hg]; exact diag_re_nonneg _ (hE.1 b) j
  have hg1 : ∀ j, ∑ b, g b j = 1 := fun j => by
    simp only [hg]; exact sum_diag_re _ hU E hE.2 j
  have ha : ∑ b, π0 * FuchsVdGraaf.outcomeDist ρ0 E b = π0 := by
    rw [← Finset.mul_sum]
    simp only [FuchsVdGraaf.outcomeDist]
    rw [sum_re_trace ρ0 h0.2 E hE.2, mul_one]
  have hc : ∀ b, π1 * FuchsVdGraaf.outcomeDist ρ1 E b =
      π0 * FuchsVdGraaf.outcomeDist ρ0 E b + ∑ j, hΓ.eigenvalues j * g b j := by
    intro b
    have := re_trace_mul_eigen hΓ (E b)
    rw [gamma_re] at this
    simp only [← hg] at this
    simp only [FuchsVdGraaf.outcomeDist]
    linarith
  have key : ∀ b, π0 * FuchsVdGraaf.outcomeDist ρ0 E b +
      ∑ j, min (hΓ.eigenvalues j) 0 * g b j ≤
      min (π0 * FuchsVdGraaf.outcomeDist ρ0 E b) (π1 * FuchsVdGraaf.outcomeDist ρ1 E b) := by
    intro b
    refine le_min ?_ ?_
    · have : ∑ j, min (hΓ.eigenvalues j) 0 * g b j ≤ 0 := Finset.sum_nonpos fun j _ =>
        mul_nonpos_of_nonpos_of_nonneg (min_le_right _ _) (hg0 b j)
      linarith
    · rw [hc b]
      have : ∑ j, min (hΓ.eigenvalues j) 0 * g b j ≤ ∑ j, hΓ.eigenvalues j * g b j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (min_le_left _ _) (hg0 b j)
      linarith
  calc π0 + ∑ j, min (hΓ.eigenvalues j) 0
      = ∑ b, (π0 * FuchsVdGraaf.outcomeDist ρ0 E b +
          ∑ j, min (hΓ.eigenvalues j) 0 * g b j) := by
        rw [Finset.sum_add_distrib, ha, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.mul_sum, hg1, mul_one]
    _ ≤ _ := Finset.sum_le_sum fun b _ => key b

/-- Step 2: the two-outcome POVM `{P, 1 - P}`, `P` the projector on the negative eigenspace
of `Γ`, has Bayes error at most `π₀ + ∑ min(γ_j, 0)`. -/
private lemma attain {n : Type} [Fintype n] [DecidableEq n] {π0 π1 : ℝ}
    {ρ0 ρ1 : Matrix n n ℂ} (h0 : WildeQIT.IsDensityOperator ρ0)
    (hΓ : (gammaOp π0 π1 ρ0 ρ1).IsHermitian) :
    ∃ E : Fin 2 → Matrix n n ℂ, FuchsVdGraaf.IsPOVM E ∧
      bayesError π0 π1 ρ0 ρ1 E ≤ π0 + ∑ j, min (hΓ.eigenvalues j) 0 := by
  have hU : star (hΓ.eigenvectorUnitary : Matrix n n ℂ) * hΓ.eigenvectorUnitary = 1 := by
    rw [← Unitary.coe_star]; exact Unitary.coe_star_mul_self _
  have hU' : (hΓ.eigenvectorUnitary : Matrix n n ℂ) * star (hΓ.eigenvectorUnitary : Matrix n n ℂ)
      = 1 := by
    rw [← Unitary.coe_star]; exact Unitary.coe_mul_star_self _
  have hc0 := re_trace_mul_eigen hΓ
  set U : Matrix n n ℂ := (hΓ.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set d : n → ℂ := fun j => if hΓ.eigenvalues j < 0 then 1 else 0 with hd
  set d' : n → ℂ := fun j => if hΓ.eigenvalues j < 0 then 0 else 1 with hd'
  set P := U * Matrix.diagonal d * star U with hP
  set Q := U * Matrix.diagonal d' * star U with hQ
  have hdd : Matrix.diagonal d + Matrix.diagonal d' = 1 := by
    rw [Matrix.diagonal_add, ← Matrix.diagonal_one]
    congr 1
    funext j
    simp only [hd, hd']
    split_ifs <;> simp
  have hPQ : P + Q = 1 := by
    rw [hP, hQ, ← Matrix.add_mul, ← Matrix.mul_add, hdd, Matrix.mul_one, hU']
  have hpsd : ∀ e : n → ℂ, (∀ j, 0 ≤ e j) → (U * Matrix.diagonal e * star U).PosSemidef := by
    intro e he
    rw [Matrix.star_eq_conjTranspose]
    exact (Matrix.posSemidef_diagonal_iff.2 he).mul_mul_conjTranspose_same U
  have hE : FuchsVdGraaf.IsPOVM ![P, Q] := by
    refine ⟨?_, ?_⟩
    · intro x
      fin_cases x
      · exact hpsd d fun j => by simp only [hd]; split_ifs <;> simp
      · exact hpsd d' fun j => by simp only [hd']; split_ifs <;> simp
    · simpa [Fin.sum_univ_two] using hPQ
  refine ⟨![P, Q], hE, ?_⟩
  have ha := sum_re_trace ρ0 h0.2 ![P, Q] hE.2
  rw [Fin.sum_univ_two] at ha
  have hc := hc0 P
  rw [gamma_re] at hc
  have hdiag : star U * P * U = Matrix.diagonal d := by
    rw [hP, show star U * (U * Matrix.diagonal d * star U) * U
        = (star U * U) * Matrix.diagonal d * (star U * U) by simp [Matrix.mul_assoc],
      hU, Matrix.one_mul, Matrix.mul_one]
  rw [hdiag] at hc
  have hsum : ∑ j, hΓ.eigenvalues j * (Matrix.diagonal d j j).re =
      ∑ j, min (hΓ.eigenvalues j) 0 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.diagonal_apply_eq, hd]
    split_ifs with h
    · simp [min_eq_left h.le]
    · simp [min_eq_right (not_lt.1 h)]
  unfold bayesError
  rw [Fin.sum_univ_two]
  simp only [FuchsVdGraaf.outcomeDist, Matrix.cons_val_zero, Matrix.cons_val_one] at ha ⊢
  have h1 := min_le_right (π0 * (ρ0 * P).trace.re) (π1 * (ρ1 * P).trace.re)
  have h2 := min_le_left (π0 * (ρ0 * Q).trace.re) (π1 * (ρ1 * Q).trace.re)
  have h3 : π0 * (ρ0 * Q).trace.re = π0 * 1 - π0 * (ρ0 * P).trace.re := by
    rw [← ha]; ring
  linarith

theorem solution {n : Type} [Fintype n] [DecidableEq n] (π0 π1 : ℝ) (hπ0 : 0 ≤ π0)
    (hπ1 : 0 ≤ π1) (hπ : π0 + π1 = 1) (ρ0 ρ1 : Matrix n n ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1) :
    qErrorProb π0 π1 ρ0 ρ1 =
        π0 + ∑ j, min ((gammaOp_isHermitian (π0 := π0) (π1 := π1) h0.1.isHermitian
          h1.1.isHermitian).eigenvalues j) 0 ∧
      ∃ (m : ℕ) (E : Fin m → Matrix n n ℂ), FuchsVdGraaf.IsPOVM E ∧
        bayesError π0 π1 ρ0 ρ1 E =
          π0 + ∑ j, min ((gammaOp_isHermitian (π0 := π0) (π1 := π1) h0.1.isHermitian
            h1.1.isHermitian).eigenvalues j) 0 := by
  set hΓ := gammaOp_isHermitian (π0 := π0) (π1 := π1) h0.1.isHermitian h1.1.isHermitian
  obtain ⟨E, hE, hle⟩ := attain h0 hΓ
  have heq : bayesError π0 π1 ρ0 ρ1 E = π0 + ∑ j, min (hΓ.eigenvalues j) 0 :=
    le_antisymm hle (lower_bound h0 hΓ E hE)
  refine ⟨?_, ⟨2, E, hE, heq⟩⟩
  unfold qErrorProb
  refine IsLeast.csInf_eq ⟨⟨2, E, hE, heq.symm⟩, ?_⟩
  rintro v ⟨m, F, hF, rfl⟩
  exact lower_bound h0 hΓ F hF
