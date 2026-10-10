-- Prove2me | solution 1 for ConleyZehnder.czIndex_signature
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-10T06:40:43.809374+00:00
-- url     : https://prove2.me/submissions/6f9b1a94-11b5-43ed-b763-74d43686e206

import Definitions.Def_ConleyZehnder_Setting
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.Dimension.Constructions
import Theorems.Thm_ConleyZehnder_czIndex_two_mul_eq_neg_signature
import Theorems.Thm_ConleyZehnder_symplectic_cayley_isHermitian
import Theorems.Thm_ConleyZehnder_czIndex_eq_of_family
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace CZSig

open ConleyZehnder Matrix NormedSpace

noncomputable section

variable {n : ℕ}

local instance : NormedAddCommGroup (Mat n) := Matrix.linftyOpNormedAddCommGroup
local instance : NormedSpace ℝ (Mat n) := Matrix.linftyOpNormedSpace
local instance : NormedRing (Mat n) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra

lemma hermitian_transpose {S : Mat n} (hS : S.IsHermitian) : Sᵀ = S := by
  simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hS

lemma infSymm (S : Mat n) (hS : S.IsHermitian) :
    (J₀ n * S) * J₀ n + J₀ n * (J₀ n * S)ᵀ = 0 := by
  have hST : Sᵀ = S := hermitian_transpose hS
  simp only [transpose_mul, J_transpose, hST, Matrix.mul_neg, Matrix.mul_assoc]
  abel

lemma exp_transpose_smul (X : Mat n) (u : ℝ) : (exp (u • X))ᵀ = exp (u • Xᵀ) := by
  rw [← exp_transpose, transpose_smul]

/-- `exp (t • J₀ S)` is symplectic. -/
lemma exp_smul_isSymplectic (S : Mat n) (hS : S.IsHermitian) (t : ℝ) :
    IsSymplectic (exp (t • (J₀ n * S))) := by
  let X : Mat n := J₀ n * S
  have hX : X * J₀ n + J₀ n * Xᵀ = 0 := by simpa [X] using infSymm S hS
  have hX' : X * J₀ n = -(J₀ n * Xᵀ) := (add_eq_zero_iff_eq_neg).1 hX
  let f : ℝ → Mat n := fun u => exp (u • X) * J₀ n * exp (u • Xᵀ)
  have hzero : ∀ u, HasDerivAt f 0 u := by
    intro u
    have h1 : HasDerivAt (fun v : ℝ => exp (v • X)) (exp (u • X) * X) u :=
      hasDerivAt_exp_smul_const X u
    have h1' : HasDerivAt (fun v : ℝ => exp (v • Xᵀ)) (exp (u • Xᵀ) * Xᵀ) u :=
      hasDerivAt_exp_smul_const Xᵀ u
    have ha : HasDerivAt (fun v => exp (v • X) * J₀ n) ((exp (u • X) * X) * J₀ n) u :=
      h1.mul_const _
    have hmul : HasDerivAt f
        ((exp (u • X) * X) * J₀ n * exp (u • Xᵀ) +
          exp (u • X) * J₀ n * (exp (u • Xᵀ) * Xᵀ)) u :=
      ha.mul h1'
    have hFX : exp (u • Xᵀ) * Xᵀ = Xᵀ * exp (u • Xᵀ) :=
      ((Commute.refl Xᵀ).smul_left u).exp_left.eq
    set E : Mat n := exp (u • X)
    set F : Mat n := exp (u • Xᵀ)
    have hJX : J₀ n * Xᵀ = -(X * J₀ n) := by
      have hneg : -(J₀ n * Xᵀ) = X * J₀ n := hX'.symm
      calc
        J₀ n * Xᵀ = -(-(J₀ n * Xᵀ)) := by rw [neg_neg]
        _ = -(X * J₀ n) := by rw [hneg]
    have hsum :
        (E * X) * J₀ n * F + E * J₀ n * (F * Xᵀ) = 0 := by
      calc
        (E * X) * J₀ n * F + E * J₀ n * (F * Xᵀ)
          = E * (X * J₀ n) * F + E * J₀ n * (Xᵀ * F) := by
            rw [hFX]; simp only [Matrix.mul_assoc]
        _ = E * (X * J₀ n) * F + E * (J₀ n * Xᵀ) * F := by
            simp only [Matrix.mul_assoc]
        _ = E * (X * J₀ n) * F + E * (-(X * J₀ n)) * F := by rw [hJX]
        _ = E * (X * J₀ n) * F + -(E * (X * J₀ n) * F) := by
            simp [Matrix.mul_assoc]
        _ = 0 := add_neg_cancel _
    exact hmul.congr_deriv hsum
  have hconst : f t = f 0 := by
    have hle := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f) (f' := fun _ : ℝ => (0 : Mat n)) (s := Set.univ) (C := 0) (x := t) (y := 0)
      (fun x _ => (hzero x).hasDerivWithinAt) (fun _ _ => by simp) (by trivial) (by trivial)
    exact (sub_eq_zero.1 (norm_le_zero_iff.1 (by simpa using hle))).symm
  have h0 : f 0 = J₀ n := by simp [f, exp_zero]
  rw [IsSymplectic, SymplecticGroup.mem_iff]
  calc
    exp (t • X) * J₀ n * (exp (t • X))ᵀ = exp (t • X) * J₀ n * exp (t • Xᵀ) := by
      rw [exp_transpose_smul]
    _ = f t := rfl
    _ = f 0 := hconst
    _ = J₀ n := h0

end

end CZSig

/-!
# Spectral mapping for the matrix exponential

Every root of `charpoly (exp A)` is `exp` of a root of `charpoly A`.
-/

namespace CZSpec

open Matrix Polynomial NormedSpace

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Columns: the `i₀` column is `v`, and every other column is a standard basis vector. -/
def pivot (v : ι → ℂ) (i0 : ι) : Matrix ι ι ℂ :=
  of fun i j => if j = i0 then v i else if i = j then 1 else 0

lemma pivot_mulVec (v : ι → ℂ) (i0 : ι) (x : ι → ℂ) :
    pivot v i0 *ᵥ x = fun i => x i0 * v i + if i = i0 then 0 else x i := by
  ext i
  simp only [mulVec, dotProduct, pivot, of_apply]
  have hfun : ∀ j,
      (if j = i0 then v i else if i = j then 1 else 0) * x j =
        (if j = i0 then v i * x j else 0) + (if j ≠ i0 ∧ i = j then x j else 0) := by
    intro j
    by_cases hj : j = i0 <;> by_cases hij : i = j <;> simp [hj, hij]
  simp_rw [hfun, Finset.sum_add_distrib]
  have h1 : ∑ j, (if j = i0 then v i * x j else 0) = v i * x i0 := by
    rw [Finset.sum_eq_single i0 (fun j _ hj => by simp [hj]) (by simp)]
    simp
  have h2 : ∑ j, (if j ≠ i0 ∧ i = j then x j else 0) = if i = i0 then 0 else x i := by
    by_cases hi : i = i0
    · simp only [hi, if_pos rfl]
      exact Finset.sum_eq_zero fun j _ => by
        split_ifs with h
        · exact absurd h.2 (Ne.symm h.1)
        · rfl
    · rw [Finset.sum_eq_single i
        (fun j _ hji => by
          simp only [ite_eq_right_iff]
          rintro ⟨_, hij⟩
          exact absurd hij hji.symm)
        (by simp)]
      simp [hi, Ne.symm hi]
  rw [h1, h2, mul_comm]

lemma pivot_mulVec_single (v : ι → ℂ) (i0 : ι) :
    pivot v i0 *ᵥ Pi.single i0 (1 : ℂ) = v := by
  rw [pivot_mulVec]
  ext i
  simp [Pi.single_apply]

lemma pivot_ker (v : ι → ℂ) (i0 : ι) (hv : v i0 ≠ 0) {x : ι → ℂ}
    (hx : pivot v i0 *ᵥ x = 0) : x = 0 := by
  ext i
  have hx' : ∀ i, x i0 * v i + (if i = i0 then 0 else x i) = 0 := by
    rw [pivot_mulVec] at hx
    exact congrFun hx
  have h0 : x i0 = 0 := by
    have h := hx' i0
    rw [if_pos rfl, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hv
  by_cases hi : i = i0
  · exact hi ▸ h0
  · have h := hx' i
    rw [if_neg hi, h0, zero_mul, zero_add] at h
    exact h

lemma pivot_isUnit (v : ι → ℂ) (i0 : ι) (hv : v i0 ≠ 0) : IsUnit (pivot v i0) := by
  rw [← mulVec_injective_iff_isUnit]
  intro x y hxy
  have hsub : pivot v i0 *ᵥ (x - y) = 0 := by
    rw [mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (pivot_ker v i0 hv hsub)

lemma toSquareBlock_one {b : ι → ℕ} (a : ℕ) :
    ((1 : Matrix ι ι ℂ).toSquareBlock b a) = 1 := by
  ext i j
  simp [toSquareBlock_def, one_apply, Subtype.ext_iff]

lemma sum_subtype_univ {p : ι → Prop} [DecidablePred p] (f : ι → ℂ) :
    ∑ x : {k // p k}, f x = ∑ k ∈ Finset.univ.filter p, f k := by
  rw [← Finset.sum_subtype_eq_sum_filter (s := Finset.univ) (p := p) (f := f)]
  apply Finset.sum_congr
  · ext x
    simp [Finset.mem_subtype, x.2]
  · intro _ _
    rfl

lemma BlockTriangular.toSquareBlock_mul {b : ι → ℕ} {M N : Matrix ι ι ℂ}
    (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) (a : ℕ) :
    ((M * N).toSquareBlock b a) = M.toSquareBlock b a * N.toSquareBlock b a := by
  ext i j
  simp only [toSquareBlock_def, of_apply, mul_apply]
  let p : ι → Prop := fun k => b k = a
  have hvanish :
      ∑ k, M i k * N k j = ∑ k ∈ Finset.univ.filter p, M i k * N k j := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro k _ hk
    rw [Finset.mem_filter, Decidable.not_and_iff_or_not] at hk
    have hk' : ¬p k := by
      rcases hk with hk | hk
      · exact absurd (Finset.mem_univ k) hk
      · exact hk
    have hk'' : b k ≠ a := hk'
    rcases lt_trichotomy (b k) a with hlt | heq | hgt
    · have hMk : M i k = 0 := hM (by simpa [i.2] using hlt)
      rw [hMk, zero_mul]
    · exact absurd heq hk''
    · have hNk : N k j = 0 := hN (by simpa [j.2] using hgt)
      rw [hNk, mul_zero]
  rw [hvanish]
  exact (sum_subtype_univ (fun k => M i.1 k * N k j.1)).symm

lemma BlockTriangular.toSquareBlock_pow {b : ι → ℕ} {M : Matrix ι ι ℂ}
    (hM : M.BlockTriangular b) (k : ℕ) (a : ℕ) :
    ((M ^ k).toSquareBlock b a) = (M.toSquareBlock b a) ^ k := by
  induction k with
  | zero => simp [toSquareBlock_one]
  | succ k ih =>
    rw [pow_succ, pow_succ,
      BlockTriangular.toSquareBlock_mul (BlockTriangular.pow hM k) hM a, ih]

/-- A crude bound `‖(M ^ n)ᵢⱼ‖ ≤ ((card ι) ∑ ‖M‖) ^ n`. -/
lemma pow_entry_norm_le (M : Matrix ι ι ℂ) (n : ℕ) (i j : ι) :
    ‖(M ^ n) i j‖ ≤
      ((Fintype.card ι : ℝ) * ∑ p : ι × ι, ‖M p.1 p.2‖) ^ n := by
  let C : ℝ := (Fintype.card ι : ℝ) * ∑ p : ι × ι, ‖M p.1 p.2‖
  let S : ℝ := ∑ p : ι × ι, ‖M p.1 p.2‖
  change ‖(M ^ n) i j‖ ≤ C ^ n
  have hS : ∀ p q, ‖M p q‖ ≤ S := by
    intro p q
    exact Finset.single_le_sum (f := fun r : ι × ι => ‖M r.1 r.2‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (p, q))
  induction n generalizing i j with
  | zero =>
    simp only [pow_zero, one_apply]
    split_ifs <;> simp
  | succ n ih =>
    rw [pow_succ', mul_apply]
    calc
      ‖∑ k, M i k * (M ^ n) k j‖ ≤ ∑ k, ‖M i k * (M ^ n) k j‖ := norm_sum_le _ _
      _ ≤ ∑ k, S * C ^ n := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul]
        exact mul_le_mul (hS i k) (ih k j) (norm_nonneg _) (le_trans (norm_nonneg _) (hS i k))
      _ = C ^ (n + 1) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, C, S]
        ring

def toSquareBlockAddHom (b : ι → ℕ) (a : ℕ) :
    Matrix ι ι ℂ →+ Matrix {x // b x = a} {x // b x = a} ℂ where
  toFun N := N.toSquareBlock b a
  map_zero' := by ext; simp [toSquareBlock_def]
  map_add' _ _ := by ext; simp [toSquareBlock_def]

lemma continuous_toSquareBlockAddHom (b : ι → ℕ) (a : ℕ) :
    Continuous (toSquareBlockAddHom b a) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hcoord : Continuous fun N : Matrix ι ι ℂ => N i.1 j.1 :=
    (continuous_apply j.1).comp (continuous_apply i.1)
  simpa [toSquareBlockAddHom, toSquareBlock_def] using hcoord

lemma toSquareBlock_smul (b : ι → ℕ) (a : ℕ) (c : ℚ) (N : Matrix ι ι ℂ) :
    (c • N).toSquareBlock b a = c • N.toSquareBlock b a := by
  ext; simp [toSquareBlock_def]

/-- Diagonal blocks of a block-triangular matrix pass through the exponential. -/
lemma BlockTriangular.toSquareBlock_exp {b : ι → ℕ} {M : Matrix ι ι ℂ}
    (hM : M.BlockTriangular b) (a : ℕ) :
    ((exp M).toSquareBlock b a) = exp (M.toSquareBlock b a) := by
  let coeff : ℕ → ℚ := fun n => (n.factorial⁻¹ : ℚ)
  let C : ℝ := (Fintype.card ι : ℝ) * ∑ p : ι × ι, ‖M p.1 p.2‖
  have hC : 0 ≤ C := by
    refine mul_nonneg (Nat.cast_nonneg _) ?_
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hseries : Summable fun n : ℕ => (n.factorial⁻¹ : ℝ) * C ^ n := by
    have hs := norm_expSeries_summable' (𝕂 := ℂ) (𝔸 := ℂ) (C : ℂ)
    refine Summable.congr hs ?_
    intro n
    simp only [norm_smul, norm_pow, norm_inv, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hC]
  have hsumM : Summable fun n : ℕ => coeff n • M ^ n := by
    refine (Pi.summable.mpr fun i => Pi.summable.mpr fun j => ?_)
    refine Summable.of_norm_bounded hseries fun n => ?_
    have hsmul : (coeff n • M ^ n) i j =
        ((n.factorial⁻¹ : ℝ) : ℂ) * (M ^ n) i j := by
      simp [Matrix.smul_apply, Algebra.smul_def, coeff]
    have hfac : 0 ≤ (n.factorial⁻¹ : ℝ) := inv_nonneg.mpr (Nat.cast_nonneg _)
    have hscalar : ‖((n.factorial⁻¹ : ℝ) : ℂ)‖ = (n.factorial⁻¹ : ℝ) := by
      rw [Complex.norm_real, Real.norm_of_nonneg hfac]
    rw [hsmul, norm_mul, hscalar]
    gcongr
    simpa [C] using pow_entry_norm_le M n i j
  have hsumB : Summable fun n : ℕ => coeff n • (M.toSquareBlock b a) ^ n := by
    refine (Pi.summable.mpr fun i => Pi.summable.mpr fun j => ?_)
    have hcoord : Summable fun n : ℕ => ((coeff n • M ^ n) i.1 j.1) :=
      (Pi.summable.mp ((Pi.summable.mp hsumM) i.1)) j.1
    refine Summable.congr hcoord ?_
    intro n
    simp only [Matrix.smul_apply]
    rw [← BlockTriangular.toSquareBlock_pow hM n a]
    simp [toSquareBlock_def]
  rw [exp_eq_tsum_rat, exp_eq_tsum_rat]
  have hmap := (hsumM).map_tsum (toSquareBlockAddHom b a) (continuous_toSquareBlockAddHom b a)
  simp only [toSquareBlockAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, coeff] at hmap
  rw [hmap]
  refine tsum_congr fun n => ?_
  rw [toSquareBlock_smul, BlockTriangular.toSquareBlock_pow hM n a]

lemma charpoly_conj (U A : Matrix ι ι ℂ) (hU : IsUnit U) :
    (U⁻¹ * A * U).charpoly = A.charpoly := by
  have hdet : IsUnit U.det := (isUnit_iff_isUnit_det U).mp hU
  calc
    (U⁻¹ * A * U).charpoly = (U⁻¹ * (A * U)).charpoly := by simp [Matrix.mul_assoc]
    _ = ((A * U) * U⁻¹).charpoly := charpoly_mul_comm _ _
    _ = A.charpoly := by
      have hUU : U * U⁻¹ = 1 := mul_nonsing_inv U hdet
      rw [mul_assoc, hUU, Matrix.mul_one]

lemma exp_const (r : ℂ) (i : ι) : exp (fun _ : ι => r) i = Complex.exp r := by
  have hs : Summable fun n : ℕ => (n.factorial⁻¹ : ℚ) • (fun _ : ι => r) ^ n := by
    rw [Pi.summable]
    intro j
    simpa [Pi.pow_apply, Pi.smul_apply] using expSeries_summable' r
  rw [exp_eq_tsum_rat]
  dsimp
  rw [tsum_apply hs]
  simp only [Pi.smul_apply, Pi.pow_apply]
  have hscalar := congrFun (exp_eq_tsum_rat (𝔸 := ℂ)) r
  rw [← hscalar, ← Complex.exp_eq_exp_ℂ]

lemma exp_scalar (r : ℂ) :
    exp (algebraMap ℂ (Matrix ι ι ℂ) r) = algebraMap ℂ (Matrix ι ι ℂ) (Complex.exp r) := by
  rw [algebraMap_eq_diagonal, exp_diagonal]
  have hconst : (algebraMap ℂ (ι → ℂ) r) = fun _ => r := by
    ext i
    simp
  rw [hconst, algebraMap_eq_diagonal]
  ext i j
  by_cases hij : i = j
  · simp [hij, diagonal_apply_eq, ← Complex.exp_eq_exp_ℂ]
  · simp [hij, diagonal_apply_ne _ hij, algebraMap_matrix_apply]

lemma charpoly_of_subsingleton [Subsingleton ι] [Nonempty ι] (M : Matrix ι ι ℂ) :
    M.charpoly = X - C (M (Classical.arbitrary ι) (Classical.arbitrary ι)) := by
  have hM : M = diagonal fun i => M i i := by
    ext i j
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp [diagonal_apply_eq]
  rw [hM, charpoly_diagonal]
  have hcard : (Finset.univ : Finset ι) = {Classical.arbitrary ι} := by
    ext i
    simp [Subsingleton.elim i (Classical.arbitrary ι)]
  simp [hcard, Finset.prod_singleton]

/-- Roots of `charpoly (exp A)` are exponentials of roots of `charpoly A`. -/
theorem isRoot_charpoly_exp (n : ℕ) :
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ],
      Fintype.card κ = n →
      ∀ (A : Matrix κ κ ℂ) (z : ℂ),
        (exp A).charpoly.IsRoot z →
        ∃ w : ℂ, A.charpoly.IsRoot w ∧ Complex.exp w = z := by
  induction n with
  | zero =>
    intro κ _ _ hcard A z hz
    haveI : IsEmpty κ := Fintype.card_eq_zero_iff.mp hcard
    rw [charpoly_isEmpty, IsRoot, Polynomial.eval_one] at hz
    exact (one_ne_zero hz).elim
  | succ n ih =>
    intro κ _ _ hcard A z hz
    haveI : Nonempty κ := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (A.mulVecLin)
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hAv : A *ᵥ v = μ • v := by simpa [mulVecLin_apply] using hv.apply_eq_smul
    have hv0 : v ≠ 0 := hv.2
    obtain ⟨i0, hi0⟩ : ∃ i0, v i0 ≠ 0 := by
      contrapose! hv0
      ext i
      exact hv0 i
    let P := pivot v i0
    have hP : IsUnit P := pivot_isUnit v i0 hi0
    set B := P⁻¹ * A * P with hBdef
    have hBexp : exp B = P⁻¹ * exp A * P := by
      rw [hBdef, Matrix.exp_conj' P A hP]
    have hcharB : B.charpoly = A.charpoly := charpoly_conj P A hP
    have hcharE : (exp B).charpoly = (exp A).charpoly := by
      rw [hBexp, charpoly_conj P (exp A) hP]
    have hPdet : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP
    have hPv : P *ᵥ Pi.single i0 (1 : ℂ) = v := pivot_mulVec_single v i0
    have hcol : B *ᵥ Pi.single i0 (1 : ℂ) = μ • Pi.single i0 (1 : ℂ) := by
      calc
        B *ᵥ Pi.single i0 1 = (P⁻¹ * A * P) *ᵥ Pi.single i0 1 := by rw [hBdef]
        _ = (P⁻¹ * A) *ᵥ (P *ᵥ Pi.single i0 1) :=
          (mulVec_mulVec (Pi.single i0 1) (P⁻¹ * A) P).symm
        _ = P⁻¹ *ᵥ (A *ᵥ (P *ᵥ Pi.single i0 1)) :=
          (mulVec_mulVec (P *ᵥ Pi.single i0 1) P⁻¹ A).symm
        _ = P⁻¹ *ᵥ (A *ᵥ v) := by rw [hPv]
        _ = P⁻¹ *ᵥ (μ • v) := by rw [hAv]
        _ = μ • (P⁻¹ *ᵥ v) := by rw [mulVec_smul]
        _ = μ • (P⁻¹ *ᵥ (P *ᵥ Pi.single i0 1)) := by rw [hPv]
        _ = μ • ((P⁻¹ * P) *ᵥ Pi.single i0 1) := by rw [← mulVec_mulVec]
        _ = μ • Pi.single i0 1 := by
          rw [nonsing_inv_mul P hPdet, one_mulVec]
    have hcol' : ∀ i, B i i0 = if i = i0 then μ else 0 := by
      intro i
      have hmul : (B *ᵥ Pi.single i0 (1 : ℂ)) i = B i i0 := by
        simp only [mulVec, dotProduct, Pi.single_apply]
        rw [Finset.sum_eq_single i0 (fun j _ hj => by simp [hj]) (by simp)]
        simp
      rw [← hmul, hcol, Pi.smul_apply, Pi.single_apply]
      simp
    let b : κ → ℕ := fun i => if i = i0 then 0 else 1
    have htri : B.BlockTriangular b := by
      intro i j hij
      have hj : j = i0 := by
        by_contra hj
        simp only [b, hj, ↓reduceIte] at hij
        split_ifs at hij with hi
        · simp at hij
        · omega
      have hi : i ≠ i0 := by
        intro hi
        simp [b, hj, hi] at hij
      simpa [hcol', hj, hi]
    have hzB : (exp B).charpoly.IsRoot z := by simpa [hcharE] using hz
    rw [BlockTriangular.charpoly (exp B) (BlockTriangular.exp htri), isRoot_prod] at hzB
    obtain ⟨a, ha, ha0⟩ := hzB
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp ha
    have hba : b i = a := hi
    by_cases hi0' : i = i0
    · have ha0b : a = 0 := by simpa [b, hi0'] using hba.symm
      subst ha0b
      let s0 := {x : κ // b x = 0}
      have hsub : Subsingleton s0 := ⟨fun x y => by
        have hx : x.1 = i0 := by simpa [b] using x.2
        have hy : y.1 = i0 := by simpa [b] using y.2
        exact Subtype.ext (hx.trans hy.symm)⟩
      haveI : Nonempty s0 := ⟨⟨i0, by simp [b]⟩⟩
      set E : Matrix s0 s0 ℂ := B.toSquareBlock b 0 with hEdef
      have hentry : E (Classical.arbitrary s0) (Classical.arbitrary s0) = μ := by
        have hu : Classical.arbitrary s0 = ⟨i0, by simp [b]⟩ := Subsingleton.elim _ _
        rw [hu]
        simp [E, toSquareBlock_def, hcol']
      have hEalg : E = algebraMap ℂ (Matrix s0 s0 ℂ) μ := by
        ext x y
        have hxy : x = y := Subsingleton.elim x y
        subst hxy
        have hx : x = ⟨i0, by simp [b]⟩ := Subsingleton.elim _ _
        subst hx
        simp [E, toSquareBlock_def, hcol', algebraMap_matrix_apply]
      have hexpE : exp E = algebraMap ℂ (Matrix s0 s0 ℂ) (Complex.exp μ) := by
        rw [hEalg, exp_scalar]
      have hrootμ : A.charpoly.IsRoot μ := by
        rw [← hcharB, BlockTriangular.charpoly B htri, isRoot_prod]
        refine ⟨0, by simpa [b] using Finset.mem_image_of_mem b (Finset.mem_univ i0), ?_⟩
        rw [charpoly_of_subsingleton E, hentry, IsRoot, eval_sub, eval_X, eval_C, sub_self]
      refine ⟨μ, hrootμ, ?_⟩
      have hzE : (exp E).charpoly.IsRoot z := by
        have hblock := BlockTriangular.toSquareBlock_exp htri 0
        rw [← hEdef] at hblock
        rw [hblock] at ha0
        exact ha0
      rw [hexpE, charpoly_of_subsingleton, IsRoot, eval_sub, eval_X, eval_C, sub_eq_zero] at hzE
      simpa [algebraMap_matrix_apply] using hzE.symm
    · have ha1 : a = 1 := by simpa [b, hi0'] using hba.symm
      subst ha1
      let s1 := {x : κ // b x = 1}
      have hcard1 : Fintype.card s1 = n := by
        let e : s1 ≃ {x : κ // x ≠ i0} :=
          { toFun := fun x => ⟨x.1, by
              intro hx
              have : b x.1 = 0 := by simp [b, hx]
              simp [x.2] at this⟩
            invFun := fun x => ⟨x.1, by simp [b, x.2]⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        have hcompl : Fintype.card κ = 1 + Fintype.card {x : κ // x ≠ i0} := by
          rw [← Fintype.card_congr (Equiv.sumCompl (fun x : κ => x = i0)), Fintype.card_sum,
            Fintype.card_subtype_eq]
        have hne : Fintype.card {x : κ // x ≠ i0} = n := by
          rw [hcompl] at hcard
          omega
        rw [← hne, ← Fintype.card_congr e]
      have hz1 : (exp (B.toSquareBlock b 1)).charpoly.IsRoot z := by
        rw [BlockTriangular.toSquareBlock_exp htri 1] at ha0
        exact ha0
      obtain ⟨w, hw, hexpw⟩ := ih s1 hcard1 (B.toSquareBlock b 1) z hz1
      refine ⟨w, ?_, hexpw⟩
      rw [← hcharB, BlockTriangular.charpoly B htri, isRoot_prod]
      refine ⟨1, ha, ?_⟩
      simpa [IsRoot] using hw

end

end CZSpec

/-!
# Nondegeneracy of `exp(t J₀ S)`

If `S` is real symmetric, invertible, and every eigenvalue satisfies `|λ| < 2π`, then
`exp(t J₀ S)` does not have eigenvalue `1` for `t ≠ 0` with `|t| ≤ 1`.
-/

namespace CZNondeg

open ConleyZehnder Matrix NormedSpace Complex Polynomial
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {n : ℕ}

local notation "ι" => Fin n ⊕ Fin n

/-- Entrywise inclusion of a real matrix into a complex matrix. -/
def ofRealM : Mat n →+* Matrix ι ι ℂ :=
  (algebraMap ℝ ℂ).mapMatrix

lemma ofRealM_apply (A : Mat n) (i j : ι) : ofRealM A i j = (A i j : ℂ) := rfl

lemma continuous_ofRealM : Continuous (ofRealM : Mat n → Matrix ι ι ℂ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  change Continuous fun A : Mat n => (A i j : ℂ)
  exact Complex.continuous_ofReal.comp ((continuous_apply j).comp (continuous_apply i))

lemma map_exp_ofReal (A : Mat n) : ofRealM (exp A) = exp (ofRealM A) := by
  letI : NormedAlgebra ℚ (Mat n) := NormedAlgebra.restrictScalars ℚ ℝ (Mat n)
  letI : NormedAlgebra ℚ (Matrix ι ι ℂ) := NormedAlgebra.restrictScalars ℚ ℂ (Matrix ι ι ℂ)
  exact map_exp ofRealM continuous_ofRealM A

lemma ofRealM_smul (t : ℝ) (A : Mat n) : ofRealM (t • A) = (t : ℂ) • ofRealM A := by
  ext i j
  rw [Algebra.smul_def, Algebra.smul_def]
  simp [ofRealM, RingHom.mapMatrix_apply, mul_apply, algebraMap_matrix_apply]

lemma isHermitian_ofReal {S : Mat n} (hS : S.IsHermitian) : (ofRealM S).IsHermitian := by
  ext i j
  simp only [IsHermitian, conjTranspose_apply, ofRealM_apply, RCLike.star_def, Complex.conj_ofReal]
  exact congrArg (algebraMap ℝ ℂ)
    (by simpa [IsHermitian, conjTranspose_apply] using (congrFun (congrFun hS j) i).symm)

lemma det_J_ne_zero : (J₀ n).det ≠ 0 := by
  have hJ : J₀ n * J₀ n = -1 := J_squared (Fin n) ℝ
  have hdet : (J₀ n).det * (J₀ n).det = (-1 : Mat n).det := by
    simpa [det_mul] using congrArg det hJ
  have hsign : (-1 : Mat n).det = 1 := by
    rw [det_neg, det_one]
    simp [Fintype.card_sum, Fintype.card_fin]
  rw [hsign] at hdet
  exact fun h => by simp [h] at hdet

lemma J_ofReal_unitary : ofRealM (J₀ n) ∈ unitaryGroup ι ℂ := by
  rw [mem_unitaryGroup_iff]
  have hreal : J₀ n * (J₀ n)ᴴ = 1 := by
    rw [conjTranspose_eq_transpose_of_trivial, J_transpose, mul_neg, J_squared, neg_neg]
  have hstar : star (ofRealM (J₀ n)) = ofRealM (star (J₀ n)) := by
    ext i j
    simp [ofRealM_apply, Complex.conj_ofReal]
  calc
    ofRealM (J₀ n) * star (ofRealM (J₀ n))
        = ofRealM (J₀ n) * ofRealM (star (J₀ n)) := by rw [hstar]
    _ = ofRealM (J₀ n * (J₀ n)ᴴ) := (ofRealM.map_mul _ _).symm
    _ = ofRealM 1 := by rw [hreal]
    _ = 1 := ofRealM.map_one

/-- `‖S‖ < 2π` for the Euclidean operator norm, when every eigenvalue is strictly inside that range. -/
lemma norm_ofReal_S_lt {S : Mat n} (hS : S.IsHermitian) (hn : 0 < n)
    (heig : ∀ i, |hS.eigenvalues i| < 2 * Real.pi) :
    ‖ofRealM S‖ < 2 * Real.pi := by
  have hSA : IsSelfAdjoint (ofRealM S) := (isHermitian_ofReal hS).isSelfAdjoint
  haveI : Nonempty ι := ⟨Sum.inl ⟨0, hn⟩⟩
  haveI : Nontrivial (Matrix ι ι ℂ) := inferInstance
  let r : NNReal := ⟨2 * Real.pi, by positivity⟩
  have hroot : ∀ z : ℂ, (ofRealM S).charpoly.IsRoot z → ‖z‖₊ < r := by
    intro z hz
    rw [ofRealM, RingHom.mapMatrix_apply, charpoly_map, hS.charpoly_eq, Polynomial.map_prod] at hz
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, isRoot_prod,
      Finset.mem_univ, true_and] at hz
    obtain ⟨i, hi⟩ := hz
    rw [IsRoot, eval_sub, eval_X, eval_C, sub_eq_zero] at hi
    rw [← NNReal.coe_lt_coe, coe_nnnorm, hi]
    simp [Complex.norm_real, Real.norm_eq_abs, r]
    exact heig i
  have hne : (spectrum ℂ (ofRealM S)).Nonempty := by
    have hdeg0 : (ofRealM S).charpoly.degree ≠ 0 := by
      intro h0
      rw [Polynomial.degree_eq_natDegree (charpoly_monic _).ne_zero, charpoly_natDegree_eq_dim,
        Fintype.card_sum, Fintype.card_fin] at h0
      simp at h0
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (ofRealM S).charpoly hdeg0
    exact ⟨z, mem_spectrum_iff_isRoot_charpoly.mpr hz⟩
  have hspec : ∀ z ∈ spectrum ℂ (ofRealM S), ‖z‖₊ < r := by
    intro z hz
    exact hroot z (mem_spectrum_iff_isRoot_charpoly.mp hz)
  have hrad := spectrum.spectralRadius_lt_of_forall_lt_of_nonempty (𝕜 := ℂ) hne hspec
  rw [← hSA.toReal_spectralRadius_complex_eq_norm]
  have hfin : spectralRadius ℂ (ofRealM S) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (spectrum.spectralRadius_le_nnnorm _)
  have hlt : (spectralRadius ℂ (ofRealM S)).toReal < r := by
    rw [← ENNReal.coe_toReal]
    exact (ENNReal.toReal_lt_toReal hfin ENNReal.coe_ne_top).mpr hrad
  simpa [r, NNReal.coe_mk, show (r : ℝ) = 2 * Real.pi from rfl] using hlt

lemma exp_eq_zero_of_norm_lt {w : ℂ} (hw : Complex.exp w = 1) (hnorm : ‖w‖ < 2 * Real.pi) :
    w = 0 := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hw
  have hI : ‖(2 : ℂ) * (Real.pi : ℂ) * I‖ = 2 * Real.pi := by
    simp [norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hkabs : ‖(k : ℂ)‖ = |(k : ℝ)| := by
    simp [Complex.norm_intCast]
  rw [hk, norm_mul, hI, hkabs] at hnorm
  have hklt : |(k : ℝ)| < 1 := by
    have h2 : 0 < 2 * Real.pi := by positivity
    exact (mul_lt_iff_lt_one_left h2).mp (by simpa [mul_comm] using hnorm)
  have hkzero : k = 0 := by
    cases k with
    | ofNat m =>
      cases m with
      | zero => rfl
      | succ m =>
        have hcoe : ((Int.ofNat (m + 1) : ℤ) : ℝ) = (m : ℝ) + 1 := by
          simp [Int.ofNat_eq_coe, Nat.cast_succ]
        have hpos : (0 : ℝ) ≤ (m : ℝ) + 1 := add_nonneg (Nat.cast_nonneg _) zero_le_one
        rw [hcoe, abs_of_nonneg hpos] at hklt
        have hge : (1 : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
        linarith
    | negSucc m =>
      have habs : |((Int.negSucc m : ℤ) : ℝ)| = (m + 1 : ℝ) := by
        rw [Int.cast_negSucc, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
        norm_cast
      rw [habs] at hklt
      have hge : (1 : ℝ) ≤ m + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      linarith
  simp [hk, hkzero]

/-- `exp(t J₀ S)` has no eigenvalue `1` when `t ≠ 0` and `|t| ≤ 1`. -/
lemma det_one_sub_exp_ne_zero {S : Mat n} (hS : S.IsHermitian) (hdet : S.det ≠ 0)
    (heig : ∀ i, |hS.eigenvalues i| < 2 * Real.pi) {t : ℝ} (ht0 : t ≠ 0) (ht : |t| ≤ 1) :
    (1 - exp (t • (J₀ n * S))).det ≠ 0 := by
  by_cases hn : n = 0
  · subst hn
    simp [det_isEmpty]
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    haveI : Nonempty ι := ⟨Sum.inl ⟨0, hn'⟩⟩
    haveI : Nontrivial (Matrix ι ι ℂ) := inferInstance
    intro hzero
    let B : Matrix ι ι ℂ := (t : ℂ) • (ofRealM (J₀ n) * ofRealM S)
    have hBdef : B = ofRealM (t • (J₀ n * S)) := by
      simp [B, ofRealM_smul, ofRealM.map_mul]
    have hBexp : exp B = ofRealM (exp (t • (J₀ n * S))) := by
      rw [hBdef, map_exp_ofReal]
    have hdetC : (1 - exp B).det = 0 := by
      have hsub : ofRealM (1 - exp (t • (J₀ n * S))) =
          1 - ofRealM (exp (t • (J₀ n * S))) := by
        simp [ofRealM, map_sub, map_one]
      have hdetmap : (ofRealM (1 - exp (t • (J₀ n * S)))).det =
          (algebraMap ℝ ℂ) ((1 - exp (t • (J₀ n * S))).det) := by
        simpa [ofRealM, RingHom.mapMatrix_apply] using
          ((algebraMap ℝ ℂ).map_det (1 - exp (t • (J₀ n * S)))).symm
      rw [hsub, ← hBexp, hzero, map_zero] at hdetmap
      exact hdetmap
    have hroot : (exp B).charpoly.IsRoot 1 := by
      rw [IsRoot, eval_charpoly]
      simpa [algebraMap_matrix_apply] using hdetC
    obtain ⟨w, hw, hexpw⟩ :=
      CZSpec.isRoot_charpoly_exp (Fintype.card ι) ι rfl B 1 hroot
    have hnormB : ‖B‖ < 2 * Real.pi := by
      have hU : ‖ofRealM (J₀ n) * ofRealM S‖ = ‖ofRealM S‖ :=
        CStarRing.norm_mem_unitary_mul (ofRealM S) (J_ofReal_unitary (n := n))
      have hSlt := norm_ofReal_S_lt hS hn' heig
      calc
        ‖B‖ = ‖(t : ℂ)‖ * ‖ofRealM (J₀ n) * ofRealM S‖ := by
          simp [B, norm_smul]
        _ = |t| * ‖ofRealM S‖ := by
          rw [hU, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ‖ofRealM S‖ := mul_le_of_le_one_left (norm_nonneg _) ht
        _ < 2 * Real.pi := hSlt
    have hwlt : ‖w‖ < 2 * Real.pi :=
      lt_of_le_of_lt (spectrum.norm_le_norm_of_mem
        (mem_spectrum_iff_isRoot_charpoly.mpr hw)) hnormB
    have hw0 : w = 0 := exp_eq_zero_of_norm_lt hexpw hwlt
    have hdetB : B.det = 0 := by
      have hroot0 : B.charpoly.IsRoot 0 := by simpa [hw0] using hw
      rw [IsRoot, eval_charpoly] at hroot0
      have hscalar : (scalar ι (0 : ℂ) - B) = -B := by
        ext i j
        simp [scalar, algebraMap_matrix_apply]
      rw [hscalar, det_neg] at hroot0
      exact (mul_eq_zero.mp hroot0).resolve_left (pow_ne_zero _ (by norm_num))
    have hfactor : B.det = (t : ℂ) ^ Fintype.card ι * (ofRealM (J₀ n)).det * (ofRealM S).det := by
      have hB' : B = (t : ℂ) • (ofRealM (J₀ n) * ofRealM S) := rfl
      rw [hB', det_smul, det_mul]
      ring
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    have hJ : (ofRealM (J₀ n)).det ≠ 0 := by
      have hmap := (algebraMap ℝ ℂ).map_det (J₀ n)
      have : (ofRealM (J₀ n)).det = (J₀ n).det := by
        simpa [ofRealM, RingHom.mapMatrix_apply] using hmap.symm
      simpa [this] using det_J_ne_zero
    have hSdet : (ofRealM S).det ≠ 0 := by
      have hmap := (algebraMap ℝ ℂ).map_det S
      have : (ofRealM S).det = S.det := by
        simpa [ofRealM, RingHom.mapMatrix_apply] using hmap.symm
      simpa [this] using hdet
    simp [hfactor, htC, hJ, hSdet, pow_ne_zero] at hdetB

/-- The straight exponential path of a symmetric matrix. -/
def expPath (S : Mat n) : C(unitInterval, Mat n) :=
  ⟨fun t => exp ((t : ℝ) • (J₀ n * S)), by
    letI : NormedAlgebra ℚ (Mat n) := NormedAlgebra.restrictScalars ℚ ℝ (Mat n)
    fun_prop⟩

lemma expPath_apply (S : Mat n) (t : unitInterval) :
    expPath S t = exp ((t : ℝ) • (J₀ n * S)) := rfl

/-- For `|eigenvalues of S| < 2π` and `det S ≠ 0`, the exponential path lies in `SP`. -/
lemma expPath_mem_SP {S : Mat n} (hS : S.IsHermitian) (hdet : S.det ≠ 0)
    (heig : ∀ i, |hS.eigenvalues i| < 2 * Real.pi) :
    expPath S ∈ SP n := by
  refine ⟨fun t => ?_, ?_, ?_⟩
  · simpa [expPath_apply] using CZSig.exp_smul_isSymplectic S hS (t : ℝ)
  · simp [expPath_apply, exp_zero]
  · simpa [expPath_apply] using
      det_one_sub_exp_ne_zero hS hdet heig (t := (1 : ℝ)) one_ne_zero (by simp)

end

end CZNondeg

/-!
# Inertia of real symmetric matrices

`Sign` counts positive eigenvalues minus negative ones. It is unchanged by a
perturbation smaller than the spectral gap, and scaling by a positive real
does not change it.
-/

namespace CZInertia

open ConleyZehnder Matrix
open _root_.QuadraticMap hiding sq
open QuadraticForm
open scoped InnerProductSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {n : ℕ}

local notation "ι" => Fin n ⊕ Fin n

/-- Orthogonal eigenvector matrix of a real symmetric matrix. -/
def evU {S : Mat n} (hS : S.IsHermitian) : Mat n :=
  (hS.eigenvectorUnitary : Mat n)

lemma evU_spec {S : Mat n} (hS : S.IsHermitian) :
    S = evU hS * diagonal hS.eigenvalues * (evU hS)ᵀ ∧
      (evU hS)ᵀ * evU hS = 1 ∧ evU hS * (evU hS)ᵀ = 1 := by
  have h1 := hS.spectral_theorem
  have hs : star (hS.eigenvectorUnitary : Mat n) = (evU hS)ᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · conv_lhs => rw [h1]
    rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp, hs]
    rfl
  · rw [← hs]
    exact Unitary.coe_star_mul_self _
  · rw [← hs]
    exact Unitary.coe_mul_star_self _

lemma dotProduct_mulVec_transpose (M : Mat n) (v w : ι → ℝ) :
    v ⬝ᵥ (M *ᵥ w) = (Mᵀ *ᵥ v) ⬝ᵥ w := by
  classical
  simp only [dotProduct, mulVec, transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma quad_apply (M : Mat n) (v : ι → ℝ) :
    M.toQuadraticForm' v = v ⬝ᵥ (M *ᵥ v) := by
  simp [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']

lemma quad_eigen {S : Mat n} (hS : S.IsHermitian) (v : ι → ℝ) :
    v ⬝ᵥ (S *ᵥ v) =
      ∑ i, hS.eigenvalues i * ((evU hS)ᵀ *ᵥ v) i * ((evU hS)ᵀ *ᵥ v) i := by
  obtain ⟨hdec, -, -⟩ := evU_spec hS
  have hSv : S *ᵥ v =
      evU hS *ᵥ (diagonal hS.eigenvalues *ᵥ ((evU hS)ᵀ *ᵥ v)) := by
    nth_rw 1 [hdec]
    rw [mul_assoc]
    rw [(mulVec_mulVec v (evU hS) (diagonal hS.eigenvalues * (evU hS)ᵀ)).symm]
    congr 1
    rw [(mulVec_mulVec v (diagonal hS.eigenvalues) ((evU hS)ᵀ)).symm]
  rw [hSv, dotProduct_mulVec_transpose, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mulVec_diagonal, mul_assoc, mul_left_comm, mul_comm]

/-- Change of basis identifying the quadratic form of `S` with its eigenvalues. -/
def eigenIsometry {S : Mat n} (hS : S.IsHermitian) :
    S.toQuadraticForm'.IsometryEquiv (weightedSumSquares ℝ hS.eigenvalues) where
  toLinearEquiv := ((evU hS)ᵀ).toLinearEquiv' <| by
    obtain ⟨-, hUTU, hUUT⟩ := evU_spec hS
    exact ⟨evU hS, hUUT, hUTU⟩
  map_app' v := by
    rw [weightedSumSquares_apply, Matrix.toLinearEquiv'_apply]
    have hlin : (Matrix.toLin' ((evU hS)ᵀ)).toFun v = (evU hS)ᵀ *ᵥ v := by
      simpa using Matrix.toLin'_apply ((evU hS)ᵀ) v
    simp only [hlin, smul_eq_mul]
    simpa [mul_assoc] using ((quad_apply S v).trans (quad_eigen hS v)).symm

lemma pos_ncard {S : Mat n} (hS : S.IsHermitian) :
    {i | 0 < hS.eigenvalues i}.ncard =
      (Finset.univ.filter fun i => 0 < hS.eigenvalues i).card := by
  classical
  rw [show {i | 0 < hS.eigenvalues i} =
      (Finset.univ.filter fun i => 0 < hS.eigenvalues i : Set ι) from by ext; simp]
  exact Set.ncard_coe_finset _

lemma neg_ncard {S : Mat n} (hS : S.IsHermitian) :
    {i | hS.eigenvalues i < 0}.ncard =
      (Finset.univ.filter fun i => hS.eigenvalues i < 0).card := by
  classical
  rw [show {i | hS.eigenvalues i < 0} =
      (Finset.univ.filter fun i => hS.eigenvalues i < 0 : Set ι) from by ext; simp]
  exact Set.ncard_coe_finset _

lemma signature_eq_sig {S : Mat n} (hS : S.IsHermitian) :
    signature S hS =
      (sigPos S.toQuadraticForm' : ℤ) - sigNeg S.toQuadraticForm' := by
  classical
  rw [signature, sigPos_of_equiv_weightedSumSquares ⟨eigenIsometry hS⟩,
    sigNeg_of_equiv_weightedSumSquares ⟨eigenIsometry hS⟩, pos_ncard, neg_ncard]

lemma toQuadraticForm'_smul (c : ℝ) (M : Mat n) :
    (c • M).toQuadraticForm' = c • M.toQuadraticForm' := by
  ext v
  simp [quad_apply, smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma isHermitian_real_smul (c : ℝ) {S : Mat n} (hS : S.IsHermitian) :
    (c • S).IsHermitian := by
  rw [IsHermitian, conjTranspose_smul, hS, RCLike.star_def]
  simp

lemma sigPos_smul_pos {c : ℝ} (hc : 0 < c) (Q : QuadraticForm ℝ (ι → ℝ)) :
    sigPos (c • Q) = sigPos Q := by
  classical
  apply le_antisymm
  · obtain ⟨V, hfin, hpd⟩ := exists_finrank_eq_sigPos_and_posDef (c • Q)
    have hpd' : (Q.restrict V).PosDef := by
      intro x hx
      have h := hpd x hx
      rw [restrict_apply, _root_.smul_apply, smul_eq_mul] at h
      rw [restrict_apply]
      exact (mul_pos_iff_of_pos_left hc).mp h
    simpa [hfin] using le_sigPos_of_posDef Q hpd'
  · obtain ⟨V, hfin, hpd⟩ := exists_finrank_eq_sigPos_and_posDef Q
    have hpd' : ((c • Q).restrict V).PosDef := by
      intro x hx
      rw [restrict_apply]
      rw [_root_.smul_apply, smul_eq_mul]
      exact mul_pos hc (by simpa [restrict_apply] using hpd x hx)
    simpa [hfin] using le_sigPos_of_posDef (c • Q) hpd'

lemma signature_smul_pos {c : ℝ} (hc : 0 < c) {S : Mat n} (hS : S.IsHermitian) :
    signature (c • S) (isHermitian_real_smul c hS) = signature S hS := by
  rw [signature_eq_sig, signature_eq_sig hS, toQuadraticForm'_smul]
  have hpos := sigPos_smul_pos hc S.toQuadraticForm'
  have hneg : sigNeg (c • S.toQuadraticForm') = sigNeg S.toQuadraticForm' := by
    have hcomm : -(c • S.toQuadraticForm') = c • (-S.toQuadraticForm') := by
      ext v
      simp [_root_.smul_apply, smul_eq_mul]
    rw [sigNeg, sigNeg, hcomm]
    exact sigPos_smul_pos hc (-S.toQuadraticForm')
  rw [hpos, hneg]

lemma signature_smul_neg {c : ℝ} (hc : c < 0) {S : Mat n} (hS : S.IsHermitian) :
    signature (c • S) (isHermitian_real_smul c hS) = -signature S hS := by
  classical
  rw [signature_eq_sig (isHermitian_real_smul c hS), signature_eq_sig hS, toQuadraticForm'_smul]
  have hswap : sigPos (c • S.toQuadraticForm') = sigNeg S.toQuadraticForm' := by
    apply le_antisymm
    · obtain ⟨V, hfin, hpd⟩ := exists_finrank_eq_sigPos_and_posDef (c • S.toQuadraticForm')
      have hpd' : ((-S.toQuadraticForm').restrict V).PosDef := by
        intro x hx
        have h := hpd x hx
        rw [restrict_apply, _root_.smul_apply, smul_eq_mul] at h
        rw [restrict_apply]
        have hQ : S.toQuadraticForm' x < 0 := by
          rcases lt_trichotomy (S.toQuadraticForm' x) 0 with hlt | heq | hgt
          · exact hlt
          · simp [heq, smul_eq_mul] at h
          · have hnonpos : c * S.toQuadraticForm' x ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg hc.le hgt.le
            exact absurd h (not_lt.mpr hnonpos)
        simpa [_root_.smul_apply, smul_eq_mul] using neg_pos.mpr hQ
      simpa [hfin] using le_sigNeg_of_negDef S.toQuadraticForm' hpd'
    · obtain ⟨V, hfin, hpd⟩ := exists_finrank_eq_sigNeg_and_negDef S.toQuadraticForm'
      have hpd' : ((c • S.toQuadraticForm').restrict V).PosDef := by
        intro x hx
        have h := hpd x hx
        rw [restrict_apply] at h
        rw [restrict_apply, _root_.smul_apply, smul_eq_mul]
        have hQ : S.toQuadraticForm' x < 0 := by simpa [smul_eq_mul] using h
        exact mul_pos_of_neg_of_neg hc hQ
      simpa [hfin] using le_sigPos_of_posDef (c • S.toQuadraticForm') hpd'
  have hswap' : sigNeg (c • S.toQuadraticForm') = sigPos S.toQuadraticForm' := by
    have hc' : 0 < -c := neg_pos.mpr hc
    have hsmul : -(c • S.toQuadraticForm') = (-c) • S.toQuadraticForm' := by
      ext v
      simp [_root_.smul_apply, smul_eq_mul]
    rw [sigNeg, hsmul, sigPos_smul_pos hc']
  rw [hswap, hswap']
  ring

/-- Minimum of `|eigenvalue|`. Positive when `S` is invertible and `n > 0`. -/
def spectralGap {S : Mat n} (hS : S.IsHermitian) (hn : 0 < n) : ℝ :=
  Finset.min' (Finset.univ.image fun i : ι => |hS.eigenvalues i|) <| by
    refine ⟨|hS.eigenvalues (Sum.inl ⟨0, hn⟩)|, ?_⟩
    simp

lemma eigenvalue_ne_zero {S : Mat n} (hS : S.IsHermitian) (hdet : S.det ≠ 0) (i : ι) :
    hS.eigenvalues i ≠ 0 := by
  intro hzero
  have hdet' := hS.det_eq_prod_eigenvalues
  rw [Finset.prod_eq_zero (Finset.mem_univ i)] at hdet'
  · exact hdet hdet'
  · exact_mod_cast hzero

lemma spectralGap_pos {S : Mat n} (hS : S.IsHermitian) (hdet : S.det ≠ 0) (hn : 0 < n) :
    0 < spectralGap hS hn := by
  unfold spectralGap
  have hmem := Finset.min'_mem (Finset.univ.image fun i : ι => |hS.eigenvalues i|)
    ⟨|hS.eigenvalues (Sum.inl ⟨0, hn⟩)|, by simp⟩
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  rw [← hi]
  exact abs_pos.mpr (eigenvalue_ne_zero hS hdet i)

lemma spectralGap_le {S : Mat n} (hS : S.IsHermitian) (hn : 0 < n) (i : ι) :
    spectralGap hS hn ≤ |hS.eigenvalues i| := by
  unfold spectralGap
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

lemma euclid_norm_sq (v : ι → ℝ) :
    ‖WithLp.toLp 2 v‖ ^ 2 = ∑ i, v i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, pow_two]

lemma abs_quad_le (M : Mat n) (v : ι → ℝ) :
    |v ⬝ᵥ (M *ᵥ v)| ≤ ‖M‖ * ‖WithLp.toLp 2 v‖ ^ 2 := by
  have hinner : inner ℝ (WithLp.toLp 2 v) (WithLp.toLp 2 (M *ᵥ v)) = v ⬝ᵥ (M *ᵥ v) := by
    simpa [dotProduct_comm] using EuclideanSpace.inner_toLp_toLp v (M *ᵥ v)
  refine le_trans (le_of_eq_of_le (congrArg abs hinner.symm) (abs_real_inner_le_norm _ _)) ?_
  have hmul := M.l2_opNorm_mulVec (WithLp.toLp 2 v)
  have hcoe : (EuclideanSpace.equiv ι ℝ).symm (M *ᵥ (WithLp.toLp 2 v : EuclideanSpace ℝ ι)) =
      WithLp.toLp 2 (M *ᵥ v) := by
    simp [EuclideanSpace.equiv, PiLp.coe_symm_continuousLinearEquiv]
  rw [hcoe] at hmul
  calc
    ‖WithLp.toLp 2 v‖ * ‖WithLp.toLp 2 (M *ᵥ v)‖ ≤ ‖WithLp.toLp 2 v‖ * (‖M‖ * ‖WithLp.toLp 2 v‖) := by
      gcongr
    _ = ‖M‖ * ‖WithLp.toLp 2 v‖ ^ 2 := by ring

/-- Pad a function on the positive-eigenvalue coordinates by zero. -/
def padPos {S : Mat n} (hS : S.IsHermitian) :
    ({i // 0 < hS.eigenvalues i} → ℝ) →ₗ[ℝ] ι → ℝ where
  toFun x i := if h : 0 < hS.eigenvalues i then x ⟨i, h⟩ else 0
  map_add' x y := by
    ext i
    by_cases h : 0 < hS.eigenvalues i <;> simp [h]
  map_smul' c x := by
    ext i
    by_cases h : 0 < hS.eigenvalues i <;> simp [h]

def padNeg {S : Mat n} (hS : S.IsHermitian) :
    ({i // hS.eigenvalues i < 0} → ℝ) →ₗ[ℝ] ι → ℝ where
  toFun x i := if h : hS.eigenvalues i < 0 then x ⟨i, h⟩ else 0
  map_add' x y := by
    ext i
    by_cases h : hS.eigenvalues i < 0 <;> simp [h]
  map_smul' c x := by
    ext i
    by_cases h : hS.eigenvalues i < 0 <;> simp [h]

def posIncl {S : Mat n} (hS : S.IsHermitian) :
    ({i // 0 < hS.eigenvalues i} → ℝ) →ₗ[ℝ] ι → ℝ :=
  (mulVecLin (evU hS)).comp (padPos hS)

def negIncl {S : Mat n} (hS : S.IsHermitian) :
    ({i // hS.eigenvalues i < 0} → ℝ) →ₗ[ℝ] ι → ℝ :=
  (mulVecLin (evU hS)).comp (padNeg hS)

lemma padPos_injective {S : Mat n} (hS : S.IsHermitian) :
    Function.Injective (padPos hS) := by
  intro x y h
  ext ⟨i, hi⟩
  have := congrFun h i
  simpa [padPos, hi] using this

lemma padNeg_injective {S : Mat n} (hS : S.IsHermitian) :
    Function.Injective (padNeg hS) := by
  intro x y h
  ext ⟨i, hi⟩
  have := congrFun h i
  simpa [padNeg, hi] using this

lemma mulVecLin_evU_injective {S : Mat n} (hS : S.IsHermitian) :
    Function.Injective (mulVecLin (evU hS)) := by
  obtain ⟨-, hUTU, -⟩ := evU_spec hS
  intro x y h
  have h' := congrArg (fun z => (evU hS)ᵀ *ᵥ z) h
  simpa [mulVec_mulVec, hUTU, one_mulVec] using h'

lemma posIncl_injective {S : Mat n} (hS : S.IsHermitian) :
    Function.Injective (posIncl hS) :=
  (mulVecLin_evU_injective hS).comp (padPos_injective hS)

lemma negIncl_injective {S : Mat n} (hS : S.IsHermitian) :
    Function.Injective (negIncl hS) :=
  (mulVecLin_evU_injective hS).comp (padNeg_injective hS)

lemma pos_card {S : Mat n} (hS : S.IsHermitian) :
    Module.finrank ℝ (LinearMap.range (posIncl hS)) =
      (Finset.univ.filter fun i => 0 < hS.eigenvalues i).card := by
  classical
  rw [LinearMap.finrank_range_of_inj (posIncl_injective hS), Module.finrank_pi,
    Fintype.card_subtype]

lemma neg_card {S : Mat n} (hS : S.IsHermitian) :
    Module.finrank ℝ (LinearMap.range (negIncl hS)) =
      (Finset.univ.filter fun i => hS.eigenvalues i < 0).card := by
  classical
  rw [LinearMap.finrank_range_of_inj (negIncl_injective hS), Module.finrank_pi,
    Fintype.card_subtype]

lemma coord_posIncl {S : Mat n} (hS : S.IsHermitian)
    (y : {i // 0 < hS.eigenvalues i} → ℝ) :
    (evU hS)ᵀ *ᵥ posIncl hS y = padPos hS y := by
  obtain ⟨-, hUTU, -⟩ := evU_spec hS
  simp [posIncl, mulVecLin_apply, mulVec_mulVec, hUTU, one_mulVec]

lemma coord_negIncl {S : Mat n} (hS : S.IsHermitian)
    (y : {i // hS.eigenvalues i < 0} → ℝ) :
    (evU hS)ᵀ *ᵥ negIncl hS y = padNeg hS y := by
  obtain ⟨-, hUTU, -⟩ := evU_spec hS
  simp [negIncl, mulVecLin_apply, mulVec_mulVec, hUTU, one_mulVec]

lemma sum_sq_coord {S : Mat n} (hS : S.IsHermitian) (v : ι → ℝ) :
    ∑ i, ((evU hS)ᵀ *ᵥ v) i ^ 2 = ‖WithLp.toLp 2 v‖ ^ 2 := by
  obtain ⟨-, -, hUUT⟩ := evU_spec hS
  have hdot : ((evU hS)ᵀ *ᵥ v) ⬝ᵥ ((evU hS)ᵀ *ᵥ v) = v ⬝ᵥ v := by
    rw [dotProduct_mulVec_transpose, transpose_transpose]
    rw [mulVec_mulVec v (evU hS) ((evU hS)ᵀ), hUUT, one_mulVec]
  have hsum : ∑ i, ((evU hS)ᵀ *ᵥ v) i ^ 2 = ((evU hS)ᵀ *ᵥ v) ⬝ᵥ ((evU hS)ᵀ *ᵥ v) := by
    simp [dotProduct, pow_two]
  rw [hsum, hdot]
  have hv : v ⬝ᵥ v = ∑ i, v i ^ 2 := by simp [dotProduct, pow_two]
  rw [hv]
  exact (euclid_norm_sq v).symm

lemma quad_pos_ge {S : Mat n} (hS : S.IsHermitian) (hn : 0 < n)
    (y : {i // 0 < hS.eigenvalues i} → ℝ) :
    spectralGap hS hn * ‖WithLp.toLp 2 (posIncl hS y)‖ ^ 2 ≤
      (posIncl hS y) ⬝ᵥ (S *ᵥ posIncl hS y) := by
  rw [quad_eigen, coord_posIncl, ← sum_sq_coord, coord_posIncl]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : 0 < hS.eigenvalues i
  · have hgap : spectralGap hS hn ≤ hS.eigenvalues i := by
      have habs := spectralGap_le hS hn i
      rwa [abs_of_pos hi] at habs
    have hsq : 0 ≤ (padPos hS y) i ^ 2 := sq_nonneg _
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hgap hsq
  · have hz : padPos hS y i = 0 := by simp [padPos, hi]
    simp [hz]

lemma quad_neg_le {S : Mat n} (hS : S.IsHermitian) (hn : 0 < n)
    (y : {i // hS.eigenvalues i < 0} → ℝ) :
    (negIncl hS y) ⬝ᵥ (S *ᵥ negIncl hS y) ≤
      -spectralGap hS hn * ‖WithLp.toLp 2 (negIncl hS y)‖ ^ 2 := by
  rw [quad_eigen, coord_negIncl, ← sum_sq_coord hS (negIncl hS y), coord_negIncl]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : hS.eigenvalues i < 0
  · have hgap : hS.eigenvalues i ≤ -spectralGap hS hn := by
      have habs := spectralGap_le hS hn i
      rw [abs_of_neg hi] at habs
      linarith
    have hsq : 0 ≤ (padNeg hS y) i ^ 2 := sq_nonneg _
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hgap hsq
  · have hz : padNeg hS y i = 0 := by simp [padNeg, hi]
    simp [hz]

lemma pos_neg_card {S : Mat n} (hS : S.IsHermitian) (hdet : S.det ≠ 0) :
    (Finset.univ.filter fun i : ι => 0 < hS.eigenvalues i).card +
      (Finset.univ.filter fun i : ι => hS.eigenvalues i < 0).card = Fintype.card ι := by
  classical
  let pos := Finset.univ.filter fun i : ι => 0 < hS.eigenvalues i
  let neg := Finset.univ.filter fun i : ι => hS.eigenvalues i < 0
  have hdisj : Disjoint pos neg := by
    rw [Finset.disjoint_filter]
    intro i _ hp hn
    linarith
  have huniv : pos ∪ neg = Finset.univ := by
    ext i
    constructor
    · intro _; exact Finset.mem_univ _
    · intro _
      have hne := eigenvalue_ne_zero hS hdet i
      rcases lt_trichotomy (hS.eigenvalues i) 0 with h | h | h
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      · exact absurd h hne
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  rw [← Finset.card_union_of_disjoint hdisj, huniv, Finset.card_univ]

lemma norm_sq_pos_of_ne_zero {v : ι → ℝ} (hv : v ≠ 0) : 0 < ‖WithLp.toLp 2 v‖ ^ 2 := by
  rw [euclid_norm_sq]
  by_contra h
  have h0 : ∑ i, v i ^ 2 = 0 :=
    le_antisymm (not_lt.mp h) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hzero : ∀ i, v i = 0 := by
    intro i
    have hi : v i ^ 2 = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp h0 i
      (Finset.mem_univ _)
    exact sq_eq_zero_iff.mp hi
  apply hv
  ext i
  exact hzero i

lemma quad_sub (A B : Mat n) (v : ι → ℝ) :
    v ⬝ᵥ (B *ᵥ v) = v ⬝ᵥ (A *ᵥ v) + v ⬝ᵥ ((B - A) *ᵥ v) := by
  rw [← dotProduct_add, ← add_mulVec]
  congr 1
  simp

lemma signature_eq_of_close {A B : Mat n} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hdet : A.det ≠ 0) (hn : 0 < n) (hclose : ‖B - A‖ < spectralGap hA hn) :
    signature B hB = signature A hA := by
  classical
  rw [signature_eq_sig hB, signature_eq_sig hA]
  have hposDef : ((B.toQuadraticForm').restrict (LinearMap.range (posIncl hA))).PosDef := by
    intro x hx
    obtain ⟨y, hy⟩ := x.2
    have hv : posIncl hA y = (x : ι → ℝ) := hy
    have hv0 : ¬ (x : ι → ℝ) = (0 : ι → ℝ) := by
      intro hzero
      exact hx (Subtype.ext hzero)
    rw [restrict_apply, quad_apply, ← hv, quad_sub]
    have hlow := quad_pos_ge hA hn y
    have habs := abs_quad_le (B - A) (posIncl hA y)
    have hperturb : -(‖B - A‖ * ‖WithLp.toLp 2 (posIncl hA y)‖ ^ 2) ≤
        (posIncl hA y) ⬝ᵥ ((B - A) *ᵥ posIncl hA y) :=
      neg_le_of_abs_le habs
    have hgap : 0 < spectralGap hA hn - ‖B - A‖ := sub_pos.mpr hclose
    have hnorm := norm_sq_pos_of_ne_zero hv0
    have hsum : 0 < (spectralGap hA hn - ‖B - A‖) * ‖WithLp.toLp 2 (posIncl hA y)‖ ^ 2 :=
      mul_pos hgap (by simpa [← hv] using hnorm)
    have hbound : (spectralGap hA hn - ‖B - A‖) * ‖WithLp.toLp 2 (posIncl hA y)‖ ^ 2 ≤
        (posIncl hA y) ⬝ᵥ (A *ᵥ posIncl hA y) +
          (posIncl hA y) ⬝ᵥ ((B - A) *ᵥ posIncl hA y) := by
      have hfac : (spectralGap hA hn - ‖B - A‖) * ‖WithLp.toLp 2 (posIncl hA y)‖ ^ 2 =
          spectralGap hA hn * ‖WithLp.toLp 2 (posIncl hA y)‖ ^ 2 +
            -(‖B - A‖ * ‖WithLp.toLp 2 (posIncl hA y)‖ ^ 2) := by ring
      rw [hfac]
      exact add_le_add hlow hperturb
    exact lt_of_lt_of_le hsum hbound
  have hnegDef : (((-B.toQuadraticForm').restrict (LinearMap.range (negIncl hA)))).PosDef := by
    intro x hx
    obtain ⟨y, hy⟩ := x.2
    have hv : negIncl hA y = (x : ι → ℝ) := hy
    have hv0 : ¬ (x : ι → ℝ) = (0 : ι → ℝ) := by
      intro hzero
      exact hx (Subtype.ext hzero)
    have hnegQ : (-B.toQuadraticForm') (negIncl hA y) =
        -((negIncl hA y) ⬝ᵥ (B *ᵥ negIncl hA y)) := by
      simp [quad_apply, _root_.smul_apply, smul_eq_mul]
    rw [restrict_apply, ← hv, hnegQ]
    have hhigh := quad_neg_le hA hn y
    have habs := abs_quad_le (B - A) (negIncl hA y)
    have hperturb : (negIncl hA y) ⬝ᵥ ((B - A) *ᵥ negIncl hA y) ≤
        ‖B - A‖ * ‖WithLp.toLp 2 (negIncl hA y)‖ ^ 2 :=
      le_trans (le_abs_self _) habs
    have hBA : (negIncl hA y) ⬝ᵥ (B *ᵥ negIncl hA y) ≤
        -spectralGap hA hn * ‖WithLp.toLp 2 (negIncl hA y)‖ ^ 2 +
          ‖B - A‖ * ‖WithLp.toLp 2 (negIncl hA y)‖ ^ 2 := by
      rw [quad_sub]
      exact add_le_add hhigh hperturb
    have hgap : 0 < spectralGap hA hn - ‖B - A‖ := sub_pos.mpr hclose
    have hy0 : negIncl hA y ≠ 0 := by
      intro hzero
      apply hv0
      simpa [hv] using hzero
    have hnorm := norm_sq_pos_of_ne_zero hy0
    have hsum : 0 < (spectralGap hA hn - ‖B - A‖) * ‖WithLp.toLp 2 (negIncl hA y)‖ ^ 2 :=
      mul_pos hgap hnorm
    -- -Q_B x = -(v ⬝ B v) > 0
    have hnegquad : (negIncl hA y) ⬝ᵥ (B *ᵥ negIncl hA y) < 0 := by
      have hfac : -spectralGap hA hn * ‖WithLp.toLp 2 (negIncl hA y)‖ ^ 2 +
          ‖B - A‖ * ‖WithLp.toLp 2 (negIncl hA y)‖ ^ 2 =
          -((spectralGap hA hn - ‖B - A‖) * ‖WithLp.toLp 2 (negIncl hA y)‖ ^ 2) := by ring
      rw [hfac] at hBA
      exact lt_of_le_of_lt hBA (neg_neg_of_pos hsum)
    simpa [smul_eq_mul] using neg_pos.mpr hnegquad
  have hposLe : sigPos A.toQuadraticForm' ≤ sigPos B.toQuadraticForm' := by
    have hcard : sigPos A.toQuadraticForm' =
        Module.finrank ℝ (LinearMap.range (posIncl hA)) := by
      rw [pos_card, ← pos_ncard, ← sigPos_of_equiv_weightedSumSquares ⟨eigenIsometry hA⟩]
    rw [hcard]
    exact le_sigPos_of_posDef B.toQuadraticForm' hposDef
  have hnegLe : sigNeg A.toQuadraticForm' ≤ sigNeg B.toQuadraticForm' := by
    have hcard : sigNeg A.toQuadraticForm' =
        Module.finrank ℝ (LinearMap.range (negIncl hA)) := by
      rw [neg_card, ← neg_ncard, ← sigNeg_of_equiv_weightedSumSquares ⟨eigenIsometry hA⟩]
    rw [hcard]
    exact le_sigNeg_of_negDef B.toQuadraticForm' hnegDef
  have hfin : sigPos B.toQuadraticForm' + sigNeg B.toQuadraticForm' ≤ Fintype.card ι := by
    have hrad := sigPos_add_sigNeg_add_radical (Q := B.toQuadraticForm')
    simp only [Module.finrank_pi] at hrad
    omega
  have hsplit := pos_neg_card hA hdet
  have hAsum : sigPos A.toQuadraticForm' + sigNeg A.toQuadraticForm' = Fintype.card ι := by
    rw [sigPos_of_equiv_weightedSumSquares ⟨eigenIsometry hA⟩,
      sigNeg_of_equiv_weightedSumSquares ⟨eigenIsometry hA⟩, pos_ncard, neg_ncard, hsplit]
  have hposEq : sigPos B.toQuadraticForm' = sigPos A.toQuadraticForm' := by
    have hnegEq : sigNeg B.toQuadraticForm' = sigNeg A.toQuadraticForm' := by
      have hBsum : sigPos A.toQuadraticForm' + sigNeg A.toQuadraticForm' ≤
          sigPos B.toQuadraticForm' + sigNeg B.toQuadraticForm' := by
        exact Nat.add_le_add hposLe hnegLe
      have hEqSum : sigPos B.toQuadraticForm' + sigNeg B.toQuadraticForm' =
          sigPos A.toQuadraticForm' + sigNeg A.toQuadraticForm' := by
        apply le_antisymm
        · simpa [hAsum] using hfin
        · exact hBsum
      omega
    omega
  rw [hposEq]
  have hnegEq : sigNeg B.toQuadraticForm' = sigNeg A.toQuadraticForm' := by
    have hBsum : sigPos A.toQuadraticForm' + sigNeg A.toQuadraticForm' ≤
        sigPos B.toQuadraticForm' + sigNeg B.toQuadraticForm' := Nat.add_le_add hposLe hnegLe
    have hEqSum : sigPos B.toQuadraticForm' + sigNeg B.toQuadraticForm' =
        sigPos A.toQuadraticForm' + sigNeg A.toQuadraticForm' := by
      apply le_antisymm
      · simpa [hAsum] using hfin
      · exact hBsum
    omega
  rw [hnegEq]

end

end CZInertia

/-!
# The signature axiom for the Conley–Zehnder index

`2 μ(exp(t J₀ S)) = Sign(S)` when `S` is symmetric, invertible, and every eigenvalue
lies in `(-2π, 2π)`. The Cayley transform of a short path `exp(u J₀ S)` is a small
positive multiple of a matrix near `-S/2`, so the two matrices have the same signature.
A straight homotopy in the scale removes the shortening.
-/

namespace CZSignature

open ConleyZehnder Matrix NormedSpace Filter Polynomial
open scoped Matrix.Norms.L2Operator Topology

noncomputable section

variable {n : ℕ}

local notation "ι" => Fin n ⊕ Fin n

local instance : NormedAlgebra ℚ (Mat n) := NormedAlgebra.restrictScalars ℚ ℝ (Mat n)

local instance : NormedAlgebra ℚ (Matrix ι ι ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ (Matrix ι ι ℂ)

/-- `exp w = -1` forces `‖w‖ ≥ π`. -/
lemma pi_le_norm_of_exp_neg_one {w : ℂ} (hw : Complex.exp w = -1) : Real.pi ≤ ‖w‖ := by
  have hsub : Complex.exp (w - Real.pi * Complex.I) = 1 := by
    rw [sub_eq_add_neg, Complex.exp_add, hw, Complex.exp_neg, Complex.exp_pi_mul_I]
    simp
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hsub
  have hw' : w = (((2 * k + 1 : ℤ) : ℝ) : ℂ) * (Real.pi : ℂ) * Complex.I := by
    have hk' : w = k * (2 * (Real.pi : ℂ) * Complex.I) + Real.pi * Complex.I := by
      rw [← hk]
      abel
    rw [hk']
    push_cast
    ring
  have hne : (2 * k + 1 : ℤ) ≠ 0 := by omega
  have hone : (1 : ℝ) ≤ |(2 * k + 1 : ℤ)| := by
    have honeZ : (1 : ℤ) ≤ |(2 * k + 1 : ℤ)| := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hne)
    exact_mod_cast honeZ
  rw [hw']
  have hcoeff : ‖(((2 * k + 1 : ℤ) : ℝ) : ℂ)‖ = |(2 * k + 1 : ℤ)| := by
    rw [Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs]
  rw [norm_mul, norm_mul, hcoeff, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  exact le_mul_of_one_le_left Real.pi_pos.le hone

/-- `(2 : Mat n)⁻¹ = 2⁻¹ I`. -/
lemma inv_two : (2 : Mat n)⁻¹ = (2⁻¹ : ℝ) • (1 : Mat n) := by
  apply inv_eq_right_inv
  have h2 : (2 : Mat n) = (2 : ℝ) • (1 : Mat n) := by
    rw [show (2 : Mat n) = (1 : Mat n) + 1 from one_add_one_eq_two.symm, two_smul]
  rw [h2, smul_mul_assoc, mul_smul_comm, mul_one, smul_smul]
  simp

/-- `J (J S) (2I)⁻¹ = -S/2`. -/
lemma neg_half_target (S : Mat n) :
    J₀ n * (J₀ n * S) * (2 : Mat n)⁻¹ = (-(1 / 2 : ℝ)) • S := by
  rw [inv_two]
  have hJJ : J₀ n * J₀ n = -1 := J_squared (Fin n) ℝ
  calc
    J₀ n * (J₀ n * S) * ((2⁻¹ : ℝ) • (1 : Mat n))
        = (J₀ n * J₀ n) * S * ((2⁻¹ : ℝ) • 1) := by simp [Matrix.mul_assoc]
    _ = (-1) * S * ((2⁻¹ : ℝ) • 1) := by rw [hJJ]
    _ = (-(2⁻¹ : ℝ)) • S := by
          rw [neg_one_mul, mul_smul_comm, mul_one, smul_neg]
          simp [neg_smul]
    _ = (-(1 / 2 : ℝ)) • S := by
          congr 1
          norm_num

/-- The Cayley quotient of `exp(u J₀ S)` tends to `-S/2` as `u ↓ 0`. -/
lemma tendsto_cayley_quotient (S : Mat n) :
    Tendsto (fun u : ℝ =>
        u⁻¹ • (J₀ n * (exp (u • (J₀ n * S)) - 1) * (exp (u • (J₀ n * S)) + 1)⁻¹))
      (𝓝[>] 0) (nhds ((-(1 / 2 : ℝ)) • S)) := by
  let A : Mat n := J₀ n * S
  have hslope : Tendsto (fun t : ℝ => t⁻¹ • (exp (t • A) - 1)) (𝓝[>] 0) (nhds A) := by
    have hderiv : HasDerivAt (fun u : ℝ => exp (u • A)) A 0 := by
      simpa [zero_smul, exp_zero, one_mul] using hasDerivAt_exp_smul_const A (0 : ℝ)
    simpa [zero_add, exp_zero] using hderiv.tendsto_slope_zero_right
  have hinv : Tendsto (fun t : ℝ => (exp (t • A) + 1)⁻¹) (𝓝[>] 0)
      (nhds ((2 : Mat n)⁻¹)) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    have hAt : (fun t : ℝ => exp (t • A) + 1) 0 = (2 : Mat n) := by
      simp [zero_smul, exp_zero, one_add_one_eq_two]
    have hdet : (2 : Mat n).det ≠ 0 := by
      rw [show (2 : Mat n) = (2 : ℝ) • (1 : Mat n) by
        rw [show (2 : Mat n) = (1 : Mat n) + 1 from one_add_one_eq_two.symm, two_smul],
        det_smul, det_one]
      exact mul_ne_zero (pow_ne_zero _ two_ne_zero) one_ne_zero
    have hInv : ContinuousAt Inv.inv (2 : Mat n) := by
      apply continuousAt_matrix_inv
      exact NormedRing.inverse_continuousAt (Units.mk0 ((2 : Mat n).det) hdet)
    have hmap : ContinuousAt (fun t : ℝ => exp (t • A) + 1) 0 :=
      (exp_continuous.continuousAt.comp
        (continuous_id.smul continuous_const).continuousAt).add continuous_const.continuousAt
    have htend := (hInv.comp_of_eq hmap hAt).tendsto
    simp only [Function.comp_def] at htend
    simpa [zero_smul, exp_zero, one_add_one_eq_two] using htend
  have hprod : Tendsto
      (fun t : ℝ => J₀ n * (t⁻¹ • (exp (t • A) - 1)) * (exp (t • A) + 1)⁻¹)
      (𝓝[>] 0) (nhds (J₀ n * A * (2 : Mat n)⁻¹)) :=
    (tendsto_const_nhds.mul hslope).mul hinv
  have hfun : ∀ u : ℝ,
      u⁻¹ • (J₀ n * (exp (u • A) - 1) * (exp (u • A) + 1)⁻¹) =
        J₀ n * (u⁻¹ • (exp (u • A) - 1)) * (exp (u • A) + 1)⁻¹ := by
    intro u
    rw [(smul_mul_assoc (u⁻¹) (J₀ n * (exp (u • A) - 1)) ((exp (u • A) + 1)⁻¹)).symm,
      (mul_smul_comm (u⁻¹) (J₀ n) (exp (u • A) - 1)).symm]
  rw [show (fun u : ℝ =>
        u⁻¹ • (J₀ n * (exp (u • A) - 1) * (exp (u • A) + 1)⁻¹)) =
      fun u => J₀ n * (u⁻¹ • (exp (u • A) - 1)) * (exp (u • A) + 1)⁻¹ from funext hfun]
  simpa [neg_half_target S, A] using hprod

/-- `exp(t J₀ S)` does not have eigenvalue `-1` when the complexified argument is shorter than `π`. -/
lemma det_one_add_exp_ne_zero {S : Mat n} (hn : 0 < n) {t : ℝ}
    (ht : |t| * ‖CZNondeg.ofRealM (J₀ n * S)‖ < Real.pi) :
    (1 + exp (t • (J₀ n * S))).det ≠ 0 := by
  haveI : Nonempty ι := ⟨Sum.inl ⟨0, hn⟩⟩
  haveI : Nontrivial (Matrix ι ι ℂ) := inferInstance
  intro hzero
  let B : Matrix ι ι ℂ := CZNondeg.ofRealM (t • (J₀ n * S))
  have hBexp : exp B = CZNondeg.ofRealM (exp (t • (J₀ n * S))) :=
    (CZNondeg.map_exp_ofReal _).symm
  have hdetC : (1 + exp B).det = 0 := by
    have hadd : CZNondeg.ofRealM (1 + exp (t • (J₀ n * S))) =
        1 + CZNondeg.ofRealM (exp (t • (J₀ n * S))) := by
      simp [CZNondeg.ofRealM, map_add, map_one]
    have hdetmap : (CZNondeg.ofRealM (1 + exp (t • (J₀ n * S)))).det =
        (algebraMap ℝ ℂ) ((1 + exp (t • (J₀ n * S))).det) := by
      simpa [CZNondeg.ofRealM, RingHom.mapMatrix_apply] using
        ((algebraMap ℝ ℂ).map_det (1 + exp (t • (J₀ n * S)))).symm
    rw [hadd, ← hBexp, hzero, map_zero] at hdetmap
    exact hdetmap
  have hroot : (exp B).charpoly.IsRoot (-1) := by
    rw [IsRoot, eval_charpoly]
    have hscalar : (scalar ι (-1 : ℂ) - exp B) = -(1 + exp B) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [sub_eq_add_neg, add_comm]
        simp [scalar, algebraMap_matrix_apply, Matrix.one_apply, neg_add]
      · simp [scalar, algebraMap_matrix_apply, Matrix.one_apply, hij]
    rw [hscalar, det_neg, hdetC]
    simp
  obtain ⟨w, hw, hexpw⟩ :=
    CZSpec.isRoot_charpoly_exp (Fintype.card ι) ι rfl B (-1) hroot
  have hnormB : ‖B‖ < Real.pi := by
    have hBsmul : B = (t : ℂ) • CZNondeg.ofRealM (J₀ n * S) := by
      simp [B, CZNondeg.ofRealM_smul]
    rw [hBsmul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact ht
  have hwlt : ‖w‖ < Real.pi :=
    lt_of_le_of_lt (spectrum.norm_le_norm_of_mem
      (mem_spectrum_iff_isRoot_charpoly.mpr hw)) hnormB
  exact (not_lt_of_ge (pi_le_norm_of_exp_neg_one hexpw)) hwlt

lemma signature_proof_irrel {S : Mat n} (h₁ h₂ : S.IsHermitian) :
    signature S h₁ = signature S h₂ := by
  have : h₁ = h₂ := Subsingleton.elim _ _
  subst this
  rfl

lemma signature_cast {A B : Mat n} (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    signature A hA = signature B hB := by
  subst h
  exact signature_proof_irrel hA hB

/-- Coefficient of the straight homotopy from scale `c` to scale `1`. -/
def scaleCoeff (c s : ℝ) : ℝ := (1 - s) * c + s

lemma scaleCoeff_bounds {c s : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < scaleCoeff c s ∧ scaleCoeff c s ≤ 1 := by
  constructor
  · have hdiff : scaleCoeff c s - c = s * (1 - c) := by
      unfold scaleCoeff
      ring
    have hnonneg : 0 ≤ scaleCoeff c s - c := by
      rw [hdiff]
      exact mul_nonneg hs0 (sub_nonneg.mpr hc1)
    linarith
  · have hdiff : scaleCoeff c s - 1 = (1 - s) * (c - 1) := by
      unfold scaleCoeff
      ring
    have hnonpos : scaleCoeff c s - 1 ≤ 0 := by
      rw [hdiff]
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hs1) (sub_nonpos.mpr hc1)
    linarith

lemma scaled_path_mem_SP {S : Mat n} (hS : S.IsHermitian) (hdet : S.det ≠ 0)
    (heig : ∀ i, |hS.eigenvalues i| < 2 * Real.pi) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    CZNondeg.expPath (c • S) ∈ SP n := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    have hmul : J₀ n * (c • S) = c • (J₀ n * S) := by simp [mul_smul]
    simpa [CZNondeg.expPath_apply, hmul, smul_smul, mul_comm] using
      CZSig.exp_smul_isSymplectic S hS ((t : ℝ) * c)
  · simp [CZNondeg.expPath_apply, zero_smul, exp_zero]
  · have hmul : J₀ n * (c • S) = c • (J₀ n * S) := by simp [mul_smul]
    simpa [CZNondeg.expPath_apply, hmul, smul_smul, mul_comm] using
      CZNondeg.det_one_sub_exp_ne_zero hS hdet heig (t := c) (ne_of_gt hc0)
        (by simpa [abs_of_pos hc0] using hc1)

/-- Homotopy through scales between `c` and `1`. -/
def scaleFamily (S : Mat n) (c : ℝ) : C(unitInterval × unitInterval, Mat n) :=
  ⟨fun st => exp ((scaleCoeff c (st.1 : ℝ) * (st.2 : ℝ)) • (J₀ n * S)), by
    have hcoeff : Continuous fun st : unitInterval × unitInterval =>
        scaleCoeff c (st.1 : ℝ) * (st.2 : ℝ) := by
      unfold scaleCoeff
      continuity
    exact exp_continuous.comp (hcoeff.smul continuous_const)⟩

lemma scaleFamily_symplectic {S : Mat n} (hS : S.IsHermitian) (c : ℝ) :
    ∀ s t, IsSymplectic (scaleFamily S c (s, t)) := by
  intro s t
  simpa [scaleFamily, scaleCoeff] using
    CZSig.exp_smul_isSymplectic S hS (scaleCoeff c (s : ℝ) * (t : ℝ))

lemma scaleFamily_zero {S : Mat n} (c : ℝ) : ∀ s, scaleFamily S c (s, 0) = 1 := by
  intro s
  simp [scaleFamily, zero_smul, exp_zero]

lemma scaleFamily_endpoint {S : Mat n} (hS : S.IsHermitian) (hdet : S.det ≠ 0)
    (heig : ∀ i, |hS.eigenvalues i| < 2 * Real.pi) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∀ s, (1 - scaleFamily S c (s, 1)).det ≠ 0 := by
  intro s
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  obtain ⟨hpos, hle⟩ := scaleCoeff_bounds hc0 hc1 hs0 hs1
  simpa [scaleFamily, scaleCoeff, one_mul] using
    CZNondeg.det_one_sub_exp_ne_zero hS hdet heig (t := scaleCoeff c (s : ℝ))
      (ne_of_gt hpos) (by simpa [abs_of_pos hpos] using hle)

theorem czIndex_signature (n : ℕ) : SignatureAxiom (czIndex (n := n)) := by
  intro S hS hdet heig ψ hψ
  have hψeq : ψ = CZNondeg.expPath S := by
    apply ContinuousMap.ext
    intro t
    rw [hψ t, CZNondeg.expPath_apply]
  by_cases hn : n = 0
  · subst hn
    have hsig : signature S hS = 0 := by
      classical
      simp [signature, Finset.card_eq_zero, Finset.univ_eq_empty]
    rw [hsig, hψeq]
    have hmem := CZNondeg.expPath_mem_SP hS hdet heig
    have hneg : ∀ t, (1 + CZNondeg.expPath S t).det ≠ 0 := by
      intro t
      simp [CZNondeg.expPath_apply, det_isEmpty]
    have hsym : IsSymplectic (CZNondeg.expPath S 1) := hmem.1 1
    have hd : ((CZNondeg.expPath S 1) + 1).det ≠ 0 := hneg 1
    have hN := symplectic_cayley_isHermitian (CZNondeg.expPath S 1) hsym hd
    have htwo := czIndex_two_mul_eq_neg_signature (CZNondeg.expPath S) hmem hneg hN
    have hsigC : signature (J₀ 0 * (CZNondeg.expPath S 1 - 1) * (CZNondeg.expPath S 1 + 1)⁻¹) hN = 0 := by
      classical
      simp [signature, Finset.card_eq_zero, Finset.univ_eq_empty]
    rw [hsigC] at htwo
    simpa using htwo
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    let Ahalf : Mat n := (-(1 / 2 : ℝ)) • S
    have hA : Ahalf.IsHermitian := CZInertia.isHermitian_real_smul _ hS
    have hdetA : Ahalf.det ≠ 0 := by
      rw [show Ahalf = (-(1 / 2 : ℝ)) • S from rfl, det_smul]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdet
    have hgap : 0 < CZInertia.spectralGap hA hn' := CZInertia.spectralGap_pos hA hdetA hn'
    have hlim := tendsto_cayley_quotient S
    rw [Metric.tendsto_nhds] at hlim
    have hev := hlim (CZInertia.spectralGap hA hn') hgap
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, hclose⟩ := hev
    let N : ℝ := ‖CZNondeg.ofRealM (J₀ n * S)‖
    let c : ℝ := min (δ / 2) (min 1 (Real.pi / (N + 1)))
    have hc0 : 0 < c := by
      have hN : 0 < N + 1 := by positivity
      have hdiv : 0 < Real.pi / (N + 1) := div_pos Real.pi_pos hN
      have hδ2 : 0 < δ / 2 := by linarith
      exact lt_min hδ2 (lt_min zero_lt_one hdiv)
    have hc1 : c ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hcδ : |c| < δ := by
      have hle : c ≤ δ / 2 := min_le_left _ _
      have habs : |c| = c := abs_of_pos hc0
      rw [habs]
      linarith
    have hcpi : |c| * N < Real.pi := by
      have habs : |c| = c := abs_of_pos hc0
      rw [habs]
      have hle : c ≤ Real.pi / (N + 1) := le_trans (min_le_right _ _) (min_le_right _ _)
      have hN : 0 ≤ N := norm_nonneg _
      have hprod : c * N ≤ Real.pi / (N + 1) * N := mul_le_mul_of_nonneg_right hle hN
      have hlt : Real.pi / (N + 1) * N < Real.pi := by
        have hden : 0 < N + 1 := by positivity
        rw [div_mul_eq_mul_div]
        have : Real.pi * N / (N + 1) < Real.pi * (N + 1) / (N + 1) := by
          refine div_lt_div_of_pos_right ?_ hden
          exact mul_lt_mul_of_pos_left (lt_add_one N) Real.pi_pos
        have hcancel : Real.pi * (N + 1) / (N + 1) = Real.pi := by
          rw [mul_div_cancel_right₀ _ (ne_of_gt hden)]
        linarith
      exact lt_of_le_of_lt hprod hlt
    have hball := hclose (y := c) (by simpa [Real.dist_eq, sub_zero] using hcδ) hc0
    let Q : Mat n := c⁻¹ • (J₀ n * (exp (c • (J₀ n * S)) - 1) * (exp (c • (J₀ n * S)) + 1)⁻¹)
    have hQclose : ‖Q - Ahalf‖ < CZInertia.spectralGap hA hn' := by
      have hdist : dist Q (-((2⁻¹ : ℝ) • S)) < CZInertia.spectralGap hA hn' := by
        simpa [Q] using hball
      rw [dist_eq_norm] at hdist
      have hAeq : Ahalf = -((2⁻¹ : ℝ) • S) := by
        simp [Ahalf, neg_smul, one_div]
      simpa [hAeq, sub_eq_add_neg, neg_neg] using hdist
    have hneg_end : (1 + exp (c • (J₀ n * S))).det ≠ 0 :=
      det_one_add_exp_ne_zero hn' (by simpa [N] using hcpi)
    have hsym_end : IsSymplectic (exp (c • (J₀ n * S))) :=
      CZSig.exp_smul_isSymplectic S hS c
    have hCay : (J₀ n * (exp (c • (J₀ n * S)) - 1) * (exp (c • (J₀ n * S)) + 1)⁻¹).IsHermitian :=
      symplectic_cayley_isHermitian _ hsym_end (by simpa [add_comm] using hneg_end)
    have hQ : Q.IsHermitian := CZInertia.isHermitian_real_smul _ hCay
    have hsigQ : signature Q hQ = -signature S hS := by
      have hcloseSig := CZInertia.signature_eq_of_close hA hQ hdetA hn' hQclose
      have hneg := CZInertia.signature_smul_neg (c := -(1 / 2 : ℝ)) (by norm_num) hS
      have hneg' : signature Ahalf hA = -signature S hS := by
        simpa [Ahalf, signature_proof_irrel] using hneg
      rw [hcloseSig, hneg']
    let ψc : C(unitInterval, Mat n) := CZNondeg.expPath (c • S)
    have hmem := scaled_path_mem_SP hS hdet heig hc0 hc1
    have hnegPath : ∀ t, (1 + ψc t).det ≠ 0 := by
      intro t
      have hmul : J₀ n * (c • S) = c • (J₀ n * S) := by simp [mul_smul]
      have ht : |(t : ℝ) * c| * N < Real.pi := by
        have ht0 : 0 ≤ (t : ℝ) := t.2.1
        have ht1 : (t : ℝ) ≤ 1 := t.2.2
        have htc : |(t : ℝ) * c| ≤ |c| := by
          rw [abs_mul, abs_of_nonneg ht0, abs_of_pos hc0]
          exact mul_le_of_le_one_left hc0.le ht1
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right htc (norm_nonneg _)) hcpi
      rw [CZNondeg.expPath_apply, hmul, smul_smul]
      rw [mul_comm (t : ℝ) c]
      exact det_one_add_exp_ne_zero hn' (by simpa [N, mul_comm, mul_left_comm, mul_assoc] using ht)
    have hN := symplectic_cayley_isHermitian (ψc 1) (hmem.1 1)
      (by simpa [add_comm] using hnegPath 1)
    have htwo := czIndex_two_mul_eq_neg_signature ψc hmem hnegPath hN
    have hCayEq : J₀ n * (ψc 1 - 1) * (ψc 1 + 1)⁻¹ =
        c • Q := by
      have hcinv : c * c⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hc0)
      simp [ψc, CZNondeg.expPath_apply, Q, mul_smul, smul_smul, hcinv, one_smul]
    have hsigC : signature (J₀ n * (ψc 1 - 1) * (ψc 1 + 1)⁻¹) hN = -signature S hS := by
      have hpos := CZInertia.signature_smul_pos hc0 hQ
      exact (signature_cast hCayEq hN (CZInertia.isHermitian_real_smul c hQ)).trans
        (hpos.trans hsigQ)
    rw [hsigC, neg_neg] at htwo
    have hH0 : ∀ t, ψc t = scaleFamily S c (0, t) := by
      intro t
      dsimp [ψc, scaleFamily, scaleCoeff, CZNondeg.expPath]
      have hcoe : ((0 : unitInterval) : ℝ) = 0 := rfl
      congr 1
      rw [hcoe, sub_zero, add_zero, one_mul, Matrix.mul_smul, smul_smul, mul_comm]
    have hH1 : ∀ t, CZNondeg.expPath S t = scaleFamily S c (1, t) := by
      intro t
      simp [scaleFamily, scaleCoeff, CZNondeg.expPath_apply]
    have hfamily := czIndex_eq_of_family (scaleFamily S c)
      (scaleFamily_symplectic hS c) (scaleFamily_zero c)
      (scaleFamily_endpoint hS hdet heig hc0 hc1)
      ψc (CZNondeg.expPath S) hH0 hH1
    rw [hψeq, hfamily]
    exact htwo

end

end CZSignature

open ConleyZehnder

theorem solution (n : ℕ) : SignatureAxiom (czIndex (n := n)) :=
  CZSignature.czIndex_signature n
