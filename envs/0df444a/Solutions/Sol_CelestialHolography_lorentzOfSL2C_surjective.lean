-- Prove2me | solution 1 for CelestialHolography.lorentzOfSL2C_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T18:19:44.767376+00:00
-- url     : https://prove2.me/submissions/d8724ef1-9b49-4775-9794-5503e85409e0

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

/-! 32eca090 CelestialHolography.lorentzOfSL2C_surjective.
Reduction to the SL(2,C) -> SO+(1,3) surjectivity proved for 00751584 (ChatterjeeQFT conventions,
reproduced locally below): with `D = diag(1,1,-1,-1)`, `toHermitian x = hermOfVec (D x)` and
`fromHermitian (hermOfVec y) = D y`, so `lorentzOfSL2C M = D ∘ kappa M ∘ D`.  Apply surjectivity
to `L' = D L D`, which is restricted Lorentz in the `(+,-,-,-)` convention. -/

namespace ChatterjeeQFT

open Matrix

def minkowskiInner (x y : Fin 4 → ℝ) : ℝ :=
  x 0 * y 0 - (x 1 * y 1 + x 2 * y 2 + x 3 * y 3)

def minkowskiSq (x : Fin 4 → ℝ) : ℝ := minkowskiInner x x

def IsLorentz (L : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ x y : Fin 4 → ℝ, minkowskiInner (L *ᵥ x) (L *ᵥ y) = minkowskiInner x y

def IsRestrictedLorentz (L : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  IsLorentz L ∧ L.det = 1 ∧ 0 < L 0 0

def hermOfVec (x : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x 0 : ℂ) + (x 3 : ℂ), (x 1 : ℂ) - Complex.I * (x 2 : ℂ);
     (x 1 : ℂ) + Complex.I * (x 2 : ℂ), (x 0 : ℂ) - (x 3 : ℂ)]

noncomputable def vecOfHerm (H : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℝ :=
  ![((H 0 0 + H 1 1) / 2).re, ((H 0 1 + H 1 0) / 2).re,
    ((H 1 0 - H 0 1) / (2 * Complex.I)).re, ((H 0 0 - H 1 1) / 2).re]

noncomputable def kappa (A : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  vecOfHerm (A * hermOfVec x * Aᴴ)

end ChatterjeeQFT

set_option autoImplicit false
set_option linter.all false

open Matrix
open scoped ComplexOrder

namespace ChatterjeeQFTKappa

open ChatterjeeQFT

theorem hermOfVec_conjTranspose (x : Fin 4 → ℝ) : (hermOfVec x)ᴴ = hermOfVec x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermOfVec, Matrix.conjTranspose_apply, Complex.ext_iff]

theorem vecOfHerm_hermOfVec (x : Fin 4 → ℝ) : vecOfHerm (hermOfVec x) = x := by
  ext i
  fin_cases i <;> simp [vecOfHerm, hermOfVec, Complex.div_re, Complex.normSq] <;> ring_nf

theorem hermOfVec_vecOfHerm (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : Hᴴ = H) :
    hermOfVec (vecOfHerm H) = H := by
  have h00 : (H 0 0).im = 0 := by
    have := congrFun (congrFun hH 0) 0
    simp [Matrix.conjTranspose_apply, Complex.ext_iff] at this
    linarith
  have h11 : (H 1 1).im = 0 := by
    have := congrFun (congrFun hH 1) 1
    simp [Matrix.conjTranspose_apply, Complex.ext_iff] at this
    linarith
  have h10 := congrFun (congrFun hH 1) 0
  simp [Matrix.conjTranspose_apply, Complex.ext_iff] at h10
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermOfVec, vecOfHerm, Complex.ext_iff, Complex.div_re, Complex.div_im,
      Complex.normSq] <;> constructor <;> linarith

theorem det_hermOfVec (x : Fin 4 → ℝ) :
    (hermOfVec x).det = ((minkowskiSq x : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  simp only [hermOfVec, minkowskiSq, minkowskiInner, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.head_fin_const]
  push_cast
  linear_combination (x 2 : ℂ) ^ 2 * Complex.I_sq

theorem hermOfVec_kappa (B : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    hermOfVec (kappa B x) = B * hermOfVec x * Bᴴ := by
  unfold kappa
  apply hermOfVec_vecOfHerm
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hermOfVec_conjTranspose, Matrix.mul_assoc]

theorem kappa_kappa (B C : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    kappa B (kappa C x) = kappa (B * C) x := by
  rw [kappa, hermOfVec_kappa, kappa, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem kappa_of_herm (A : Matrix (Fin 2) (Fin 2) ℂ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∀ x, A * hermOfVec x * Aᴴ = hermOfVec (L *ᵥ x)) (x : Fin 4 → ℝ) :
    kappa A x = L *ᵥ x := by
  unfold kappa
  rw [h x, vecOfHerm_hermOfVec]

theorem hermOfVec_e0 : hermOfVec ![1, 0, 0, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOfVec]

/-! ## The kernel -/

theorem kappa_neg (B : Matrix (Fin 2) (Fin 2) ℂ) : kappa (-B) = kappa B := by
  funext x
  simp [kappa, Matrix.conjTranspose_neg]

theorem kernel_mp (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) (hB : B.det = 1)
    (h : kappa A = kappa B) : A = B ∨ A = -B := by
  have hBu : IsUnit B.det := by rw [hB]; exact isUnit_one
  have hBHu : IsUnit Bᴴ.det := by rw [Matrix.det_conjTranspose, hB, star_one]; exact isUnit_one
  set C := B⁻¹ * A with hCdef
  have hBC : B * C = A := by
    rw [hCdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBu, Matrix.one_mul]
  have hC : ∀ x, C * hermOfVec x * Cᴴ = hermOfVec x := by
    intro x
    have h1 : A * hermOfVec x * Aᴴ = B * hermOfVec x * Bᴴ := by
      rw [← hermOfVec_kappa, ← hermOfVec_kappa, h]
    rw [← hBC, Matrix.conjTranspose_mul] at h1
    have h2 : B * (C * hermOfVec x * Cᴴ) * Bᴴ = B * hermOfVec x * Bᴴ := by
      rw [← h1]; simp only [Matrix.mul_assoc]
    calc C * hermOfVec x * Cᴴ = B⁻¹ * (B * (C * hermOfVec x * Cᴴ) * Bᴴ) * Bᴴ⁻¹ := by
          rw [Matrix.mul_assoc B, Matrix.nonsing_inv_mul_cancel_left _ _ hBu,
            Matrix.mul_nonsing_inv_cancel_right _ _ hBHu]
      _ = B⁻¹ * (B * hermOfVec x * Bᴴ) * Bᴴ⁻¹ := by rw [h2]
      _ = hermOfVec x := by
          rw [Matrix.mul_assoc B, Matrix.nonsing_inv_mul_cancel_left _ _ hBu,
            Matrix.mul_nonsing_inv_cancel_right _ _ hBHu]
  have hCC : C * Cᴴ = 1 := by
    have := hC ![1, 0, 0, 0]
    rwa [hermOfVec_e0, Matrix.mul_one] at this
  have hCC' : Cᴴ * C = 1 := mul_eq_one_comm.mp hCC
  have hcomm : ∀ x, C * hermOfVec x = hermOfVec x * C := by
    intro x
    calc C * hermOfVec x = C * hermOfVec x * (Cᴴ * C) := by rw [hCC', Matrix.mul_one]
      _ = (C * hermOfVec x * Cᴴ) * C := by simp only [Matrix.mul_assoc]
      _ = hermOfVec x * C := by rw [hC x]
  have h3 := hcomm ![0, 0, 0, 1]
  have h1 := hcomm ![0, 1, 0, 0]
  have a01 := congrFun (congrFun h3 0) 1
  have a10 := congrFun (congrFun h3 1) 0
  have b01 := congrFun (congrFun h1 0) 1
  simp [hermOfVec, Matrix.mul_apply, Fin.sum_univ_two] at a01 a10 b01
  have hdC : C.det = 1 := by
    rw [hCdef, Matrix.det_mul, Matrix.det_nonsing_inv, hB, hA]
    simp
  rw [Matrix.det_fin_two] at hdC
  have c01 : C 0 1 = 0 := by linear_combination (-1 / 2 : ℂ) * a01
  have c10 : C 1 0 = 0 := by linear_combination (1 / 2 : ℂ) * a10
  have hsq : C 0 0 * C 0 0 = 1 := by
    rw [c01, c10, ← b01] at hdC
    linear_combination hdC
  rcases mul_self_eq_one_iff.mp hsq with h0 | h0
  · left
    have hC1 : C = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [c01, c10, ← b01, h0]
    rw [← hBC, hC1, Matrix.mul_one]
  · right
    have hC1 : C = -1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [c01, c10, ← b01, h0]
    rw [← hBC, hC1, Matrix.mul_neg, Matrix.mul_one]

theorem kernel (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) (hB : B.det = 1) :
    kappa A = kappa B ↔ (A = B ∨ A = -B) := by
  refine ⟨kernel_mp A B hA hB, ?_⟩
  rintro (rfl | rfl)
  · rfl
  · exact kappa_neg B

/-! ## The Minkowski metric -/

theorem minkowskiInner_polar (x y : Fin 4 → ℝ) :
    minkowskiInner x y = (minkowskiSq (x + y) - minkowskiSq (x - y)) / 4 := by
  simp only [minkowskiSq, minkowskiInner, Pi.add_apply, Pi.sub_apply]
  ring

theorem lorentz_inner (N : Matrix (Fin 4) (Fin 4) ℝ)
    (hN : ∀ x, minkowskiSq (N *ᵥ x) = minkowskiSq x) (x y : Fin 4 → ℝ) :
    minkowskiInner (N *ᵥ x) (N *ᵥ y) = minkowskiInner x y := by
  rw [minkowskiInner_polar, minkowskiInner_polar x y, ← Matrix.mulVec_add, ← Matrix.mulVec_sub,
    hN, hN]

/-- The Minkowski metric `diag(1,-1,-1,-1)`. -/
def eta : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, -1, -1, -1]

theorem lorentz_matrix (N : Matrix (Fin 4) (Fin 4) ℝ)
    (hN : ∀ x, minkowskiSq (N *ᵥ x) = minkowskiSq x) : Nᵀ * eta * N = eta := by
  ext i j
  have h := lorentz_inner N hN (Pi.single i 1) (Pi.single j 1)
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
  fin_cases i <;> fin_cases j <;>
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four, minkowskiInner] at h ⊢ <;>
    linarith

theorem eta_mul_eta : eta * eta = 1 := by
  rw [eta, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

theorem adjugate_lorentz (N : Matrix (Fin 4) (Fin 4) ℝ) (h : Nᵀ * eta * N = eta) :
    adjugate N = N.det • (eta * Nᵀ * eta) := by
  have hleft : (eta * Nᵀ * eta) * N = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Nᵀ, h, eta_mul_eta]
  have hright : N * (eta * Nᵀ * eta) = 1 := mul_eq_one_comm.mp hleft
  calc adjugate N = adjugate N * (N * (eta * Nᵀ * eta)) := by rw [hright, Matrix.mul_one]
    _ = (adjugate N * N) * (eta * Nᵀ * eta) := (Matrix.mul_assoc _ _ _).symm
    _ = N.det • (eta * Nᵀ * eta) := by rw [adjugate_mul, Matrix.smul_mul, Matrix.one_mul]

/-! ## The spinor `N = Σ L_{μν} σ_μ σ_ν` -/

/-- `N = Σ_{μ,ν} L_{μν} σ_μ σ_ν`, written out entrywise. -/
def Nmat (L : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨L 0 0 + L 1 1 + L 2 2 + L 3 3 + L 0 3 + L 3 0, L 1 2 - L 2 1⟩,
     ⟨L 0 1 + L 1 0 + L 3 1 - L 1 3, L 2 3 - L 3 2 - L 0 2 - L 2 0⟩;
     ⟨L 0 1 + L 1 0 - L 3 1 + L 1 3, L 2 3 - L 3 2 + L 0 2 + L 2 0⟩,
     ⟨L 0 0 + L 1 1 + L 2 2 + L 3 3 - L 0 3 - L 3 0, L 2 1 - L 1 2⟩]

set_option maxHeartbeats 4000000 in
theorem key (L : Matrix (Fin 4) (Fin 4) ℝ) (hG : Lᵀ * eta * L = eta) (hdet : L.det = 1)
    (x : Fin 4 → ℝ) :
    Nmat L * hermOfVec x * (Nmat L)ᴴ =
      ((4 * (L 0 0 + L 1 1 + L 2 2 + L 3 3) : ℝ) : ℂ) • hermOfVec (L *ᵥ x) := by
  have hleft : (eta * Lᵀ * eta) * L = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Lᵀ, hG, eta_mul_eta]
  have hright : L * (eta * Lᵀ * eta) = 1 := mul_eq_one_comm.mp hleft
  have hH : L * eta * Lᵀ = eta := by
    calc L * eta * Lᵀ = L * (eta * Lᵀ * eta) * eta := by
          simp only [Matrix.mul_assoc, eta_mul_eta, Matrix.mul_one]
      _ = eta := by rw [hright, Matrix.one_mul]
  have hadj : adjugate L = eta * Lᵀ * eta := by
    rw [adjugate_lorentz L hG, hdet, one_smul]
  have e00 : ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) = L 0 0 := by
    have h := congrFun (congrFun hadj 0) 0
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e01 : (-(L 0 1 * L 2 2 * L 3 3 - L 0 1 * L 2 3 * L 3 2 - L 0 2 * L 2 1 * L 3 3 + L 0 2 * L 2 3 * L 3 1 + L 0 3 * L 2 1 * L 3 2 - L 0 3 * L 2 2 * L 3 1)) = (-L 1 0) := by
    have h := congrFun (congrFun hadj 0) 1
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e02 : ((L 0 1 * L 1 2 * L 3 3 - L 0 1 * L 1 3 * L 3 2 - L 0 2 * L 1 1 * L 3 3 + L 0 2 * L 1 3 * L 3 1 + L 0 3 * L 1 1 * L 3 2 - L 0 3 * L 1 2 * L 3 1)) = (-L 2 0) := by
    have h := congrFun (congrFun hadj 0) 2
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e03 : (-(L 0 1 * L 1 2 * L 2 3 - L 0 1 * L 1 3 * L 2 2 - L 0 2 * L 1 1 * L 2 3 + L 0 2 * L 1 3 * L 2 1 + L 0 3 * L 1 1 * L 2 2 - L 0 3 * L 1 2 * L 2 1)) = (-L 3 0) := by
    have h := congrFun (congrFun hadj 0) 3
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e10 : (-(L 1 0 * L 2 2 * L 3 3 - L 1 0 * L 2 3 * L 3 2 - L 1 2 * L 2 0 * L 3 3 + L 1 2 * L 2 3 * L 3 0 + L 1 3 * L 2 0 * L 3 2 - L 1 3 * L 2 2 * L 3 0)) = (-L 0 1) := by
    have h := congrFun (congrFun hadj 1) 0
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e11 : ((L 0 0 * L 2 2 * L 3 3 - L 0 0 * L 2 3 * L 3 2 - L 0 2 * L 2 0 * L 3 3 + L 0 2 * L 2 3 * L 3 0 + L 0 3 * L 2 0 * L 3 2 - L 0 3 * L 2 2 * L 3 0)) = L 1 1 := by
    have h := congrFun (congrFun hadj 1) 1
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e12 : (-(L 0 0 * L 1 2 * L 3 3 - L 0 0 * L 1 3 * L 3 2 - L 0 2 * L 1 0 * L 3 3 + L 0 2 * L 1 3 * L 3 0 + L 0 3 * L 1 0 * L 3 2 - L 0 3 * L 1 2 * L 3 0)) = L 2 1 := by
    have h := congrFun (congrFun hadj 1) 2
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e13 : ((L 0 0 * L 1 2 * L 2 3 - L 0 0 * L 1 3 * L 2 2 - L 0 2 * L 1 0 * L 2 3 + L 0 2 * L 1 3 * L 2 0 + L 0 3 * L 1 0 * L 2 2 - L 0 3 * L 1 2 * L 2 0)) = L 3 1 := by
    have h := congrFun (congrFun hadj 1) 3
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e20 : ((L 1 0 * L 2 1 * L 3 3 - L 1 0 * L 2 3 * L 3 1 - L 1 1 * L 2 0 * L 3 3 + L 1 1 * L 2 3 * L 3 0 + L 1 3 * L 2 0 * L 3 1 - L 1 3 * L 2 1 * L 3 0)) = (-L 0 2) := by
    have h := congrFun (congrFun hadj 2) 0
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e21 : (-(L 0 0 * L 2 1 * L 3 3 - L 0 0 * L 2 3 * L 3 1 - L 0 1 * L 2 0 * L 3 3 + L 0 1 * L 2 3 * L 3 0 + L 0 3 * L 2 0 * L 3 1 - L 0 3 * L 2 1 * L 3 0)) = L 1 2 := by
    have h := congrFun (congrFun hadj 2) 1
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e22 : ((L 0 0 * L 1 1 * L 3 3 - L 0 0 * L 1 3 * L 3 1 - L 0 1 * L 1 0 * L 3 3 + L 0 1 * L 1 3 * L 3 0 + L 0 3 * L 1 0 * L 3 1 - L 0 3 * L 1 1 * L 3 0)) = L 2 2 := by
    have h := congrFun (congrFun hadj 2) 2
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e23 : (-(L 0 0 * L 1 1 * L 2 3 - L 0 0 * L 1 3 * L 2 1 - L 0 1 * L 1 0 * L 2 3 + L 0 1 * L 1 3 * L 2 0 + L 0 3 * L 1 0 * L 2 1 - L 0 3 * L 1 1 * L 2 0)) = L 3 2 := by
    have h := congrFun (congrFun hadj 2) 3
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e30 : (-(L 1 0 * L 2 1 * L 3 2 - L 1 0 * L 2 2 * L 3 1 - L 1 1 * L 2 0 * L 3 2 + L 1 1 * L 2 2 * L 3 0 + L 1 2 * L 2 0 * L 3 1 - L 1 2 * L 2 1 * L 3 0)) = (-L 0 3) := by
    have h := congrFun (congrFun hadj 3) 0
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e31 : ((L 0 0 * L 2 1 * L 3 2 - L 0 0 * L 2 2 * L 3 1 - L 0 1 * L 2 0 * L 3 2 + L 0 1 * L 2 2 * L 3 0 + L 0 2 * L 2 0 * L 3 1 - L 0 2 * L 2 1 * L 3 0)) = L 1 3 := by
    have h := congrFun (congrFun hadj 3) 1
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e32 : (-(L 0 0 * L 1 1 * L 3 2 - L 0 0 * L 1 2 * L 3 1 - L 0 1 * L 1 0 * L 3 2 + L 0 1 * L 1 2 * L 3 0 + L 0 2 * L 1 0 * L 3 1 - L 0 2 * L 1 1 * L 3 0)) = L 2 3 := by
    have h := congrFun (congrFun hadj 3) 2
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have e33 : ((L 0 0 * L 1 1 * L 2 2 - L 0 0 * L 1 2 * L 2 1 - L 0 1 * L 1 0 * L 2 2 + L 0 1 * L 1 2 * L 2 0 + L 0 2 * L 1 0 * L 2 1 - L 0 2 * L 1 1 * L 2 0)) = L 3 3 := by
    have h := congrFun (congrFun hadj 3) 3
    simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, Fin.succAbove, eta,
      Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    linear_combination h
  have g00 : (1) * L 0 0 * L 0 0 + (-1) * L 1 0 * L 1 0 + (-1) * L 2 0 * L 2 0 + (-1) * L 3 0 * L 3 0 = 1 := by
    have h := congrFun (congrFun hG 0) 0
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have g01 : (1) * L 0 0 * L 0 1 + (-1) * L 1 0 * L 1 1 + (-1) * L 2 0 * L 2 1 + (-1) * L 3 0 * L 3 1 = 0 := by
    have h := congrFun (congrFun hG 0) 1
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have g02 : (1) * L 0 0 * L 0 2 + (-1) * L 1 0 * L 1 2 + (-1) * L 2 0 * L 2 2 + (-1) * L 3 0 * L 3 2 = 0 := by
    have h := congrFun (congrFun hG 0) 2
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have g03 : (1) * L 0 0 * L 0 3 + (-1) * L 1 0 * L 1 3 + (-1) * L 2 0 * L 2 3 + (-1) * L 3 0 * L 3 3 = 0 := by
    have h := congrFun (congrFun hG 0) 3
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have g11 : (1) * L 0 1 * L 0 1 + (-1) * L 1 1 * L 1 1 + (-1) * L 2 1 * L 2 1 + (-1) * L 3 1 * L 3 1 = -1 := by
    have h := congrFun (congrFun hG 1) 1
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have g12 : (1) * L 0 1 * L 0 2 + (-1) * L 1 1 * L 1 2 + (-1) * L 2 1 * L 2 2 + (-1) * L 3 1 * L 3 2 = 0 := by
    have h := congrFun (congrFun hG 1) 2
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have g13 : (1) * L 0 1 * L 0 3 + (-1) * L 1 1 * L 1 3 + (-1) * L 2 1 * L 2 3 + (-1) * L 3 1 * L 3 3 = 0 := by
    have h := congrFun (congrFun hG 1) 3
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have g22 : (1) * L 0 2 * L 0 2 + (-1) * L 1 2 * L 1 2 + (-1) * L 2 2 * L 2 2 + (-1) * L 3 2 * L 3 2 = -1 := by
    have h := congrFun (congrFun hG 2) 2
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have g23 : (1) * L 0 2 * L 0 3 + (-1) * L 1 2 * L 1 3 + (-1) * L 2 2 * L 2 3 + (-1) * L 3 2 * L 3 3 = 0 := by
    have h := congrFun (congrFun hG 2) 3
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have g33 : (1) * L 0 3 * L 0 3 + (-1) * L 1 3 * L 1 3 + (-1) * L 2 3 * L 2 3 + (-1) * L 3 3 * L 3 3 = -1 := by
    have h := congrFun (congrFun hG 3) 3
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h00 : (1) * L 0 0 * L 0 0 + (-1) * L 0 1 * L 0 1 + (-1) * L 0 2 * L 0 2 + (-1) * L 0 3 * L 0 3 = 1 := by
    have h := congrFun (congrFun hH 0) 0
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h01 : (1) * L 0 0 * L 1 0 + (-1) * L 0 1 * L 1 1 + (-1) * L 0 2 * L 1 2 + (-1) * L 0 3 * L 1 3 = 0 := by
    have h := congrFun (congrFun hH 0) 1
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h02 : (1) * L 0 0 * L 2 0 + (-1) * L 0 1 * L 2 1 + (-1) * L 0 2 * L 2 2 + (-1) * L 0 3 * L 2 3 = 0 := by
    have h := congrFun (congrFun hH 0) 2
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h03 : (1) * L 0 0 * L 3 0 + (-1) * L 0 1 * L 3 1 + (-1) * L 0 2 * L 3 2 + (-1) * L 0 3 * L 3 3 = 0 := by
    have h := congrFun (congrFun hH 0) 3
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h11 : (1) * L 1 0 * L 1 0 + (-1) * L 1 1 * L 1 1 + (-1) * L 1 2 * L 1 2 + (-1) * L 1 3 * L 1 3 = -1 := by
    have h := congrFun (congrFun hH 1) 1
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h12 : (1) * L 1 0 * L 2 0 + (-1) * L 1 1 * L 2 1 + (-1) * L 1 2 * L 2 2 + (-1) * L 1 3 * L 2 3 = 0 := by
    have h := congrFun (congrFun hH 1) 2
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h13 : (1) * L 1 0 * L 3 0 + (-1) * L 1 1 * L 3 1 + (-1) * L 1 2 * L 3 2 + (-1) * L 1 3 * L 3 3 = 0 := by
    have h := congrFun (congrFun hH 1) 3
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h22 : (1) * L 2 0 * L 2 0 + (-1) * L 2 1 * L 2 1 + (-1) * L 2 2 * L 2 2 + (-1) * L 2 3 * L 2 3 = -1 := by
    have h := congrFun (congrFun hH 2) 2
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h23 : (1) * L 2 0 * L 3 0 + (-1) * L 2 1 * L 3 1 + (-1) * L 2 2 * L 3 2 + (-1) * L 2 3 * L 3 3 = 0 := by
    have h := congrFun (congrFun hH 2) 3
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have h33 : (1) * L 3 0 * L 3 0 + (-1) * L 3 1 * L 3 1 + (-1) * L 3 2 * L 3 2 + (-1) * L 3 3 * L 3 3 = -1 := by
    have h := congrFun (congrFun hH 3) 3
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have j01_01 : L 0 0 * L 1 1 - (-L 1 0) * (-L 0 1) = (1) * (L 2 2 * L 3 3 - L 2 3 * L 3 2) := by
    linear_combination (-L 1 1) * e00 - ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) * e11 + (-L 0 1) * e01 + (-(L 0 1 * L 2 2 * L 3 3 - L 0 1 * L 2 3 * L 3 2 - L 0 2 * L 2 1 * L 3 3 + L 0 2 * L 2 3 * L 3 1 + L 0 3 * L 2 1 * L 3 2 - L 0 3 * L 2 2 * L 3 1)) * e10 + (1) * (L 2 2 * L 3 3 - L 2 3 * L 3 2) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (1) * (L 2 2 * L 3 3 - L 2 3 * L 3 2) * h00
  have j01_02 : L 0 0 * L 2 1 - (-L 2 0) * (-L 0 1) = (-1) * (L 1 2 * L 3 3 - L 1 3 * L 3 2) := by
    linear_combination (-L 2 1) * e00 - ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) * e12 + (-L 0 1) * e02 + ((L 0 1 * L 1 2 * L 3 3 - L 0 1 * L 1 3 * L 3 2 - L 0 2 * L 1 1 * L 3 3 + L 0 2 * L 1 3 * L 3 1 + L 0 3 * L 1 1 * L 3 2 - L 0 3 * L 1 2 * L 3 1)) * e10 + (-1) * (L 1 2 * L 3 3 - L 1 3 * L 3 2) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (-1) * (L 1 2 * L 3 3 - L 1 3 * L 3 2) * h00
  have j01_03 : L 0 0 * L 3 1 - (-L 3 0) * (-L 0 1) = (1) * (L 1 2 * L 2 3 - L 1 3 * L 2 2) := by
    linear_combination (-L 3 1) * e00 - ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) * e13 + (-L 0 1) * e03 + (-(L 0 1 * L 1 2 * L 2 3 - L 0 1 * L 1 3 * L 2 2 - L 0 2 * L 1 1 * L 2 3 + L 0 2 * L 1 3 * L 2 1 + L 0 3 * L 1 1 * L 2 2 - L 0 3 * L 1 2 * L 2 1)) * e10 + (1) * (L 1 2 * L 2 3 - L 1 3 * L 2 2) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (1) * (L 1 2 * L 2 3 - L 1 3 * L 2 2) * h00
  have j01_12 : (-L 1 0) * L 2 1 - (-L 2 0) * L 1 1 = (1) * (L 0 2 * L 3 3 - L 0 3 * L 3 2) := by
    linear_combination (-L 2 1) * e01 - (-(L 0 1 * L 2 2 * L 3 3 - L 0 1 * L 2 3 * L 3 2 - L 0 2 * L 2 1 * L 3 3 + L 0 2 * L 2 3 * L 3 1 + L 0 3 * L 2 1 * L 3 2 - L 0 3 * L 2 2 * L 3 1)) * e12 + L 1 1 * e02 + ((L 0 1 * L 1 2 * L 3 3 - L 0 1 * L 1 3 * L 3 2 - L 0 2 * L 1 1 * L 3 3 + L 0 2 * L 1 3 * L 3 1 + L 0 3 * L 1 1 * L 3 2 - L 0 3 * L 1 2 * L 3 1)) * e11 + (1) * (L 0 2 * L 3 3 - L 0 3 * L 3 2) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (1) * (L 0 2 * L 3 3 - L 0 3 * L 3 2) * h00
  have j01_13 : (-L 1 0) * L 3 1 - (-L 3 0) * L 1 1 = (-1) * (L 0 2 * L 2 3 - L 0 3 * L 2 2) := by
    linear_combination (-L 3 1) * e01 - (-(L 0 1 * L 2 2 * L 3 3 - L 0 1 * L 2 3 * L 3 2 - L 0 2 * L 2 1 * L 3 3 + L 0 2 * L 2 3 * L 3 1 + L 0 3 * L 2 1 * L 3 2 - L 0 3 * L 2 2 * L 3 1)) * e13 + L 1 1 * e03 + (-(L 0 1 * L 1 2 * L 2 3 - L 0 1 * L 1 3 * L 2 2 - L 0 2 * L 1 1 * L 2 3 + L 0 2 * L 1 3 * L 2 1 + L 0 3 * L 1 1 * L 2 2 - L 0 3 * L 1 2 * L 2 1)) * e11 + (-1) * (L 0 2 * L 2 3 - L 0 3 * L 2 2) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (-1) * (L 0 2 * L 2 3 - L 0 3 * L 2 2) * h00
  have j02_01 : L 0 0 * L 1 2 - (-L 1 0) * (-L 0 2) = (-1) * (L 2 1 * L 3 3 - L 2 3 * L 3 1) := by
    linear_combination (-L 1 2) * e00 - ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) * e21 + (-L 0 2) * e01 + (-(L 0 1 * L 2 2 * L 3 3 - L 0 1 * L 2 3 * L 3 2 - L 0 2 * L 2 1 * L 3 3 + L 0 2 * L 2 3 * L 3 1 + L 0 3 * L 2 1 * L 3 2 - L 0 3 * L 2 2 * L 3 1)) * e20 + (-1) * (L 2 1 * L 3 3 - L 2 3 * L 3 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (-1) * (L 2 1 * L 3 3 - L 2 3 * L 3 1) * h00
  have j02_02 : L 0 0 * L 2 2 - (-L 2 0) * (-L 0 2) = (1) * (L 1 1 * L 3 3 - L 1 3 * L 3 1) := by
    linear_combination (-L 2 2) * e00 - ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) * e22 + (-L 0 2) * e02 + ((L 0 1 * L 1 2 * L 3 3 - L 0 1 * L 1 3 * L 3 2 - L 0 2 * L 1 1 * L 3 3 + L 0 2 * L 1 3 * L 3 1 + L 0 3 * L 1 1 * L 3 2 - L 0 3 * L 1 2 * L 3 1)) * e20 + (1) * (L 1 1 * L 3 3 - L 1 3 * L 3 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (1) * (L 1 1 * L 3 3 - L 1 3 * L 3 1) * h00
  have j02_03 : L 0 0 * L 3 2 - (-L 3 0) * (-L 0 2) = (-1) * (L 1 1 * L 2 3 - L 1 3 * L 2 1) := by
    linear_combination (-L 3 2) * e00 - ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) * e23 + (-L 0 2) * e03 + (-(L 0 1 * L 1 2 * L 2 3 - L 0 1 * L 1 3 * L 2 2 - L 0 2 * L 1 1 * L 2 3 + L 0 2 * L 1 3 * L 2 1 + L 0 3 * L 1 1 * L 2 2 - L 0 3 * L 1 2 * L 2 1)) * e20 + (-1) * (L 1 1 * L 2 3 - L 1 3 * L 2 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (-1) * (L 1 1 * L 2 3 - L 1 3 * L 2 1) * h00
  have j02_12 : (-L 1 0) * L 2 2 - (-L 2 0) * L 1 2 = (-1) * (L 0 1 * L 3 3 - L 0 3 * L 3 1) := by
    linear_combination (-L 2 2) * e01 - (-(L 0 1 * L 2 2 * L 3 3 - L 0 1 * L 2 3 * L 3 2 - L 0 2 * L 2 1 * L 3 3 + L 0 2 * L 2 3 * L 3 1 + L 0 3 * L 2 1 * L 3 2 - L 0 3 * L 2 2 * L 3 1)) * e22 + L 1 2 * e02 + ((L 0 1 * L 1 2 * L 3 3 - L 0 1 * L 1 3 * L 3 2 - L 0 2 * L 1 1 * L 3 3 + L 0 2 * L 1 3 * L 3 1 + L 0 3 * L 1 1 * L 3 2 - L 0 3 * L 1 2 * L 3 1)) * e21 + (-1) * (L 0 1 * L 3 3 - L 0 3 * L 3 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (-1) * (L 0 1 * L 3 3 - L 0 3 * L 3 1) * h00
  have j02_23 : (-L 2 0) * L 3 2 - (-L 3 0) * L 2 2 = (-1) * (L 0 1 * L 1 3 - L 0 3 * L 1 1) := by
    linear_combination (-L 3 2) * e02 - ((L 0 1 * L 1 2 * L 3 3 - L 0 1 * L 1 3 * L 3 2 - L 0 2 * L 1 1 * L 3 3 + L 0 2 * L 1 3 * L 3 1 + L 0 3 * L 1 1 * L 3 2 - L 0 3 * L 1 2 * L 3 1)) * e23 + L 2 2 * e03 + (-(L 0 1 * L 1 2 * L 2 3 - L 0 1 * L 1 3 * L 2 2 - L 0 2 * L 1 1 * L 2 3 + L 0 2 * L 1 3 * L 2 1 + L 0 3 * L 1 1 * L 2 2 - L 0 3 * L 1 2 * L 2 1)) * e22 + (-1) * (L 0 1 * L 1 3 - L 0 3 * L 1 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (-1) * (L 0 1 * L 1 3 - L 0 3 * L 1 1) * h00
  have j03_01 : L 0 0 * L 1 3 - (-L 1 0) * (-L 0 3) = (1) * (L 2 1 * L 3 2 - L 2 2 * L 3 1) := by
    linear_combination (-L 1 3) * e00 - ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) * e31 + (-L 0 3) * e01 + (-(L 0 1 * L 2 2 * L 3 3 - L 0 1 * L 2 3 * L 3 2 - L 0 2 * L 2 1 * L 3 3 + L 0 2 * L 2 3 * L 3 1 + L 0 3 * L 2 1 * L 3 2 - L 0 3 * L 2 2 * L 3 1)) * e30 + (1) * (L 2 1 * L 3 2 - L 2 2 * L 3 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (1) * (L 2 1 * L 3 2 - L 2 2 * L 3 1) * h00
  have j03_02 : L 0 0 * L 2 3 - (-L 2 0) * (-L 0 3) = (-1) * (L 1 1 * L 3 2 - L 1 2 * L 3 1) := by
    linear_combination (-L 2 3) * e00 - ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) * e32 + (-L 0 3) * e02 + ((L 0 1 * L 1 2 * L 3 3 - L 0 1 * L 1 3 * L 3 2 - L 0 2 * L 1 1 * L 3 3 + L 0 2 * L 1 3 * L 3 1 + L 0 3 * L 1 1 * L 3 2 - L 0 3 * L 1 2 * L 3 1)) * e30 + (-1) * (L 1 1 * L 3 2 - L 1 2 * L 3 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (-1) * (L 1 1 * L 3 2 - L 1 2 * L 3 1) * h00
  have j03_03 : L 0 0 * L 3 3 - (-L 3 0) * (-L 0 3) = (1) * (L 1 1 * L 2 2 - L 1 2 * L 2 1) := by
    linear_combination (-L 3 3) * e00 - ((L 1 1 * L 2 2 * L 3 3 - L 1 1 * L 2 3 * L 3 2 - L 1 2 * L 2 1 * L 3 3 + L 1 2 * L 2 3 * L 3 1 + L 1 3 * L 2 1 * L 3 2 - L 1 3 * L 2 2 * L 3 1)) * e33 + (-L 0 3) * e03 + (-(L 0 1 * L 1 2 * L 2 3 - L 0 1 * L 1 3 * L 2 2 - L 0 2 * L 1 1 * L 2 3 + L 0 2 * L 1 3 * L 2 1 + L 0 3 * L 1 1 * L 2 2 - L 0 3 * L 1 2 * L 2 1)) * e30 + (1) * (L 1 1 * L 2 2 - L 1 2 * L 2 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (1) * (L 1 1 * L 2 2 - L 1 2 * L 2 1) * h00
  have j03_13 : (-L 1 0) * L 3 3 - (-L 3 0) * L 1 3 = (-1) * (L 0 1 * L 2 2 - L 0 2 * L 2 1) := by
    linear_combination (-L 3 3) * e01 - (-(L 0 1 * L 2 2 * L 3 3 - L 0 1 * L 2 3 * L 3 2 - L 0 2 * L 2 1 * L 3 3 + L 0 2 * L 2 3 * L 3 1 + L 0 3 * L 2 1 * L 3 2 - L 0 3 * L 2 2 * L 3 1)) * e33 + L 1 3 * e03 + (-(L 0 1 * L 1 2 * L 2 3 - L 0 1 * L 1 3 * L 2 2 - L 0 2 * L 1 1 * L 2 3 + L 0 2 * L 1 3 * L 2 1 + L 0 3 * L 1 1 * L 2 2 - L 0 3 * L 1 2 * L 2 1)) * e31 + (-1) * (L 0 1 * L 2 2 - L 0 2 * L 2 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (-1) * (L 0 1 * L 2 2 - L 0 2 * L 2 1) * h00
  have j03_23 : (-L 2 0) * L 3 3 - (-L 3 0) * L 2 3 = (1) * (L 0 1 * L 1 2 - L 0 2 * L 1 1) := by
    linear_combination (-L 3 3) * e02 - ((L 0 1 * L 1 2 * L 3 3 - L 0 1 * L 1 3 * L 3 2 - L 0 2 * L 1 1 * L 3 3 + L 0 2 * L 1 3 * L 3 1 + L 0 3 * L 1 1 * L 3 2 - L 0 3 * L 1 2 * L 3 1)) * e33 + L 2 3 * e03 + (-(L 0 1 * L 1 2 * L 2 3 - L 0 1 * L 1 3 * L 2 2 - L 0 2 * L 1 1 * L 2 3 + L 0 2 * L 1 3 * L 2 1 + L 0 3 * L 1 1 * L 2 2 - L 0 3 * L 1 2 * L 2 1)) * e32 + (1) * (L 0 1 * L 1 2 - L 0 2 * L 1 1) * (L 0 0 * e00 + L 0 1 * e10 + L 0 2 * e20 + L 0 3 * e30) + (1) * (L 0 1 * L 1 2 - L 0 2 * L 1 1) * h00
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Nmat, hermOfVec, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.ext_iff, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Complex.star_def]
    refine ⟨?_, ?_⟩
    · linear_combination x 0 * ((-1) * g00 + (2) * g03 + (-1) * g11 + (-1) * g22 + (-1) * g33 + (-2) * h00 + (-2) * h03 + (-2) * j01_01 + (-2) * j01_13 + (-2) * j02_02 + (-2) * j02_23 + (-2) * j03_03) + x 1 * ((-2) * g01 + (2) * g13 + (2) * h01 + (2) * h13 + (-2) * j01_03 + (-2) * j02_12 + (-2) * j03_01 + (-2) * j03_13) + x 2 * ((-2) * g02 + (2) * g23 + (2) * h02 + (2) * h23 + (2) * j01_12 + (-2) * j02_03 + (-2) * j03_02 + (-2) * j03_23) + x 3 * ((-1) * g00 + (-2) * g03 + (1) * g11 + (1) * g22 + (3) * g33 + (2) * h00 + (2) * h03 + (-2) * h11 + (-2) * h22 + (2) * j01_01 + (2) * j01_13 + (2) * j02_02 + (2) * j02_23 + (-2) * j03_03)
    · linear_combination
  · simp [Nmat, hermOfVec, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.ext_iff, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Complex.star_def]
    refine ⟨?_, ?_⟩
    · linear_combination x 0 * ((2) * g01 + (-2) * h01 + (2) * j02_12 + (2) * j03_13) + x 1 * ((1) * g00 + (1) * g11 + (-1) * g22 + (-1) * g33 + (2) * h11 + (-2) * j01_01 + (2) * j02_02 + (2) * j03_03) + x 2 * ((2) * g12 + (2) * h12 + (-2) * j01_02 + (-2) * j02_01) + x 3 * ((2) * g13 + (2) * h13 + (-2) * j01_03 + (-2) * j03_01)
    · linear_combination x 0 * ((-2) * g02 + (2) * h02 + (2) * j01_12 + (-2) * j03_23) + x 1 * ((-2) * g12 + (-2) * h12 + (2) * j01_02 + (2) * j02_01) + x 2 * ((-1) * g00 + (1) * g11 + (-1) * g22 + (1) * g33 + (-2) * h22 + (-2) * j01_01 + (2) * j02_02 + (-2) * j03_03) + x 3 * ((-2) * g23 + (-2) * h23 + (2) * j02_03 + (2) * j03_02)
  · simp [Nmat, hermOfVec, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.ext_iff, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Complex.star_def]
    refine ⟨?_, ?_⟩
    · linear_combination x 0 * ((2) * g01 + (-2) * h01 + (2) * j02_12 + (2) * j03_13) + x 1 * ((1) * g00 + (1) * g11 + (-1) * g22 + (-1) * g33 + (2) * h11 + (-2) * j01_01 + (2) * j02_02 + (2) * j03_03) + x 2 * ((2) * g12 + (2) * h12 + (-2) * j01_02 + (-2) * j02_01) + x 3 * ((2) * g13 + (2) * h13 + (-2) * j01_03 + (-2) * j03_01)
    · linear_combination x 0 * ((2) * g02 + (-2) * h02 + (-2) * j01_12 + (2) * j03_23) + x 1 * ((2) * g12 + (2) * h12 + (-2) * j01_02 + (-2) * j02_01) + x 2 * ((1) * g00 + (-1) * g11 + (1) * g22 + (-1) * g33 + (2) * h22 + (2) * j01_01 + (-2) * j02_02 + (2) * j03_03) + x 3 * ((2) * g23 + (2) * h23 + (-2) * j02_03 + (-2) * j03_02)
  · simp [Nmat, hermOfVec, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.ext_iff, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Complex.star_def]
    refine ⟨?_, ?_⟩
    · linear_combination x 0 * ((-1) * g00 + (-2) * g03 + (-1) * g11 + (-1) * g22 + (-1) * g33 + (-2) * h00 + (2) * h03 + (-2) * j01_01 + (2) * j01_13 + (-2) * j02_02 + (2) * j02_23 + (-2) * j03_03) + x 1 * ((-2) * g01 + (-2) * g13 + (2) * h01 + (-2) * h13 + (2) * j01_03 + (-2) * j02_12 + (2) * j03_01 + (-2) * j03_13) + x 2 * ((-2) * g02 + (-2) * g23 + (2) * h02 + (-2) * h23 + (2) * j01_12 + (2) * j02_03 + (2) * j03_02 + (-2) * j03_23) + x 3 * ((1) * g00 + (-2) * g03 + (-1) * g11 + (-1) * g22 + (-3) * g33 + (-2) * h00 + (2) * h03 + (2) * h11 + (2) * h22 + (-2) * j01_01 + (2) * j01_13 + (-2) * j02_02 + (2) * j02_23 + (2) * j03_03)
    · linear_combination

/-! ## Surjectivity -/

theorem main_pos (L : Matrix (Fin 4) (Fin 4) ℝ) (hG : Lᵀ * eta * L = eta) (hdet : L.det = 1)
    (htr : 0 < L 0 0 + L 1 1 + L 2 2 + L 3 3) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ ∀ x, kappa A x = L *ᵥ x := by
  have hk := key L hG hdet
  set t := L 0 0 + L 1 1 + L 2 2 + L 3 3 with ht
  have g00 : L 0 0 * L 0 0 - L 1 0 * L 1 0 - L 2 0 * L 2 0 - L 3 0 * L 3 0 = 1 := by
    have h := congrFun (congrFun hG 0) 0
    simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_four] at h
    linear_combination h
  have hm : minkowskiSq (L *ᵥ ![1, 0, 0, 0]) = 1 := by
    simp [minkowskiSq, minkowskiInner, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    linear_combination g00
  have hdN : Complex.normSq (Nmat L).det = 16 * t ^ 2 := by
    have h := congrArg Matrix.det (hk ![1, 0, 0, 0])
    rw [hermOfVec_e0, Matrix.mul_one, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_smul,
      det_hermOfVec, hm, Complex.star_def, Complex.mul_conj] at h
    have h3 : Complex.normSq (Nmat L).det = (4 * t) ^ 2 := by
      simp only [Fintype.card_fin, Complex.ofReal_one, mul_one] at h
      exact_mod_cast h
    linear_combination h3
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self ((Nmat L).det / 4)
  have hN4 : (Nmat L).det = 4 * (s * s) := by rw [← hs]; ring
  have hns : Complex.normSq s = t := by
    rw [hN4, Complex.normSq_mul, Complex.normSq_mul] at hdN
    have h4 : Complex.normSq 4 = 16 := by norm_num [Complex.normSq_apply]
    rw [h4] at hdN
    have hnn := Complex.normSq_nonneg s
    have hprod : (Complex.normSq s - t) * (Complex.normSq s + t) = 0 := by
      linear_combination hdN / 16
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · linarith
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, Complex.normSq_zero] at hns
    linarith
  have ht0 : t ≠ 0 := ne_of_gt htr
  refine ⟨(2 * s)⁻¹ • Nmat L, ?_, ?_⟩
  · rw [Matrix.det_smul, Fintype.card_fin, hN4]
    field_simp
    ring
  · apply kappa_of_herm
    intro x
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hk x, smul_smul]
    have hc : (2 * s)⁻¹ * star ((2 * s)⁻¹) * ((4 * t : ℝ) : ℂ) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_inv, Complex.normSq_mul, hns]
      have h2 : Complex.normSq 2 = 4 := by norm_num [Complex.normSq_apply]
      rw [h2]
      push_cast
      field_simp
    rw [hc, one_smul]

theorem diag_lorentz (d : Fin 4 → ℝ) (hd : ∀ i, d i * d i = 1) :
    (Matrix.diagonal d)ᵀ * eta * Matrix.diagonal d = eta := by
  rw [Matrix.diagonal_transpose, eta, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  calc d i * ![(1 : ℝ), -1, -1, -1] i * d i = ![(1 : ℝ), -1, -1, -1] i * (d i * d i) := by ring
    _ = ![(1 : ℝ), -1, -1, -1] i := by rw [hd i, mul_one]

theorem diag_sq (d : Fin 4 → ℝ) (hd : ∀ i, d i * d i = 1) :
    Matrix.diagonal d * Matrix.diagonal d = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact hd i

theorem reduce (L D : Matrix (Fin 4) (Fin 4) ℝ) (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : P.det = 1)
    (hPD : ∀ x, P * hermOfVec x * Pᴴ = hermOfVec (D *ᵥ x)) (hDD : D * D = 1)
    (hG : Lᵀ * eta * L = eta) (hD : Dᵀ * eta * D = eta) (hdet : L.det = 1) (hDdet : D.det = 1)
    (htr : 0 < (L * D) 0 0 + (L * D) 1 1 + (L * D) 2 2 + (L * D) 3 3) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ ∀ x, kappa A x = L *ᵥ x := by
  have hG' : (L * D)ᵀ * eta * (L * D) = eta := by
    rw [Matrix.transpose_mul]
    calc Dᵀ * Lᵀ * eta * (L * D) = Dᵀ * (Lᵀ * eta * L) * D := by simp only [Matrix.mul_assoc]
      _ = eta := by rw [hG, hD]
  have hdet' : (L * D).det = 1 := by rw [Matrix.det_mul, hdet, hDdet, one_mul]
  obtain ⟨A', hA', hA'x⟩ := main_pos (L * D) hG' hdet' htr
  refine ⟨A' * P, by rw [Matrix.det_mul, hA', hP, one_mul], fun x => ?_⟩
  rw [← kappa_kappa, kappa_of_herm P D hPD, hA'x, Matrix.mulVec_mulVec, Matrix.mul_assoc, hDD,
    Matrix.mul_one]

theorem herm_P1 (x : Fin 4 → ℝ) :
    !![0, Complex.I; Complex.I, 0] * hermOfVec x * (!![0, Complex.I; Complex.I, 0])ᴴ =
      hermOfVec (Matrix.diagonal ![1, 1, -1, -1] *ᵥ x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermOfVec, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.ext_iff, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.diagonal,
      Complex.star_def] <;> (try refine ⟨?_, ?_⟩) <;> ring

theorem herm_P2 (x : Fin 4 → ℝ) :
    !![0, 1; -1, 0] * hermOfVec x * (!![(0 : ℂ), 1; -1, 0])ᴴ =
      hermOfVec (Matrix.diagonal ![1, -1, 1, -1] *ᵥ x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermOfVec, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.ext_iff, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.diagonal,
      Complex.star_def] <;> (try refine ⟨?_, ?_⟩) <;> ring

theorem herm_P3 (x : Fin 4 → ℝ) :
    !![Complex.I, 0; 0, -Complex.I] * hermOfVec x * (!![Complex.I, 0; 0, -Complex.I])ᴴ =
      hermOfVec (Matrix.diagonal ![1, -1, -1, 1] *ᵥ x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermOfVec, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.ext_iff, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.diagonal,
      Complex.star_def] <;> (try refine ⟨?_, ?_⟩) <;> ring

theorem surj (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsRestrictedLorentz L) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ ∀ x, kappa A x = L *ᵥ x := by
  obtain ⟨hlor, hdet, h00⟩ := hL
  have hG : Lᵀ * eta * L = eta := lorentz_matrix L (fun x => hlor x x)
  by_cases h0 : 0 < L 0 0 + L 1 1 + L 2 2 + L 3 3
  · exact main_pos L hG hdet h0
  by_cases h1 : 0 < L 0 0 + L 1 1 - L 2 2 - L 3 3
  · refine reduce L (Matrix.diagonal ![1, 1, -1, -1]) _ (by simp [Matrix.det_fin_two])
      herm_P1 (diag_sq _ (by intro i; fin_cases i <;> norm_num)) hG
      (diag_lorentz _ (by intro i; fin_cases i <;> norm_num)) hdet
      (by simp [Matrix.det_diagonal, Fin.prod_univ_four]) ?_
    simp [Matrix.mul_diagonal]
    linarith
  by_cases h2 : 0 < L 0 0 - L 1 1 + L 2 2 - L 3 3
  · refine reduce L (Matrix.diagonal ![1, -1, 1, -1]) _ (by simp [Matrix.det_fin_two])
      herm_P2 (diag_sq _ (by intro i; fin_cases i <;> norm_num)) hG
      (diag_lorentz _ (by intro i; fin_cases i <;> norm_num)) hdet
      (by simp [Matrix.det_diagonal, Fin.prod_univ_four]) ?_
    simp [Matrix.mul_diagonal]
    linarith
  by_cases h3 : 0 < L 0 0 - L 1 1 - L 2 2 + L 3 3
  · refine reduce L (Matrix.diagonal ![1, -1, -1, 1]) _ (by simp [Matrix.det_fin_two])
      herm_P3 (diag_sq _ (by intro i; fin_cases i <;> norm_num)) hG
      (diag_lorentz _ (by intro i; fin_cases i <;> norm_num)) hdet
      (by simp [Matrix.det_diagonal, Fin.prod_univ_four]) ?_
    simp [Matrix.mul_diagonal]
    linarith
  exfalso
  linarith

end ChatterjeeQFTKappa

namespace CelestialBridge

open Matrix ChatterjeeQFT CelestialHolography

def Dg : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, 1, -1, -1]

theorem Dg_mulVec (x : Fin 4 → ℝ) : Dg *ᵥ x = ![x 0, x 1, -x 2, -x 3] := by
  ext i
  fin_cases i <;> simp [Dg, Matrix.mulVec_diagonal]

theorem Dg_mul_Dg : Dg * Dg = 1 := by
  rw [Dg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> norm_num

theorem toHermitian_eq (x : Fin 4 → ℝ) : toHermitian x = hermOfVec (Dg *ᵥ x) := by
  rw [Dg_mulVec]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toHermitian, hermOfVec, Complex.ext_iff] <;> ring

theorem fromHermitian_hermOfVec (y : Fin 4 → ℝ) : fromHermitian (hermOfVec y) = Dg *ᵥ y := by
  rw [Dg_mulVec]
  ext i
  fin_cases i <;> simp [fromHermitian, hermOfVec] <;> ring

theorem lorentz_eq (M : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    fromHermitian (M * toHermitian x * Mᴴ) = Dg *ᵥ kappa M (Dg *ᵥ x) := by
  rw [toHermitian_eq, ← ChatterjeeQFTKappa.hermOfVec_kappa, fromHermitian_hermOfVec]

theorem minkowskiSq_eq (x : Fin 4 → ℝ) : minkowskiSq x = - minkowskiNormSq x := by
  simp only [minkowskiSq, minkowskiInner, minkowskiNormSq]
  ring

theorem normSq_Dg (x : Fin 4 → ℝ) : minkowskiNormSq (Dg *ᵥ x) = minkowskiNormSq x := by
  rw [Dg_mulVec]
  simp [minkowskiNormSq]

theorem main (L : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))
    (hL : ∀ x, minkowskiNormSq (L x) = minkowskiNormSq x)
    (hdet : LinearMap.det L = 1) (horth : 0 < L (Pi.single 0 1) 0) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ x, lorentzOfSL2C M x = L x := by
  set l := LinearMap.toMatrix' L with hl
  have hlx : ∀ x, l *ᵥ x = L x := fun x => by rw [hl, LinearMap.toMatrix'_mulVec]
  set L' := Dg * l * Dg with hL'
  have hL'x : ∀ x, L' *ᵥ x = Dg *ᵥ L (Dg *ᵥ x) := by
    intro x
    rw [hL', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hlx]
  have hsq : ∀ x, minkowskiSq (L' *ᵥ x) = minkowskiSq x := by
    intro x
    rw [hL'x, minkowskiSq_eq, minkowskiSq_eq, normSq_Dg, hL, normSq_Dg]
  have hR : IsRestrictedLorentz L' := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y
      rw [ChatterjeeQFTKappa.minkowskiInner_polar, ChatterjeeQFTKappa.minkowskiInner_polar x y,
        ← Matrix.mulVec_add, ← Matrix.mulVec_sub, hsq, hsq]
    · have hD : Dg.det * Dg.det = 1 := by
        rw [← Matrix.det_mul, Dg_mul_Dg, Matrix.det_one]
      rw [hL', Matrix.det_mul, Matrix.det_mul, hl, LinearMap.det_toMatrix', hdet]
      linear_combination hD
    · have h0 : L' 0 0 = (L' *ᵥ (Pi.single 0 1 : Fin 4 → ℝ)) 0 := by
        rw [Matrix.mulVec_single_one]
        rfl
      rw [h0, hL'x]
      have he : Dg *ᵥ (Pi.single 0 1 : Fin 4 → ℝ) = Pi.single 0 1 := by
        rw [Dg_mulVec]
        ext i
        fin_cases i <;> simp
      rw [he, Dg_mulVec]
      simpa using horth
  obtain ⟨A, hA, hAx⟩ := ChatterjeeQFTKappa.surj L' hR
  refine ⟨⟨A, hA⟩, fun x => ?_⟩
  show fromHermitian (A * toHermitian x * Aᴴ) = L x
  rw [lorentz_eq, hAx, hL'x, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Dg_mul_Dg,
    Matrix.one_mulVec, Matrix.one_mulVec]

end CelestialBridge

open CelestialHolography in
theorem solution (L : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))
    (hL : ∀ x, minkowskiNormSq (L x) = minkowskiNormSq x)
    (hdet : LinearMap.det L = 1) (horth : 0 < L (Pi.single 0 1) 0) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ x, lorentzOfSL2C M x = L x := by
  exact CelestialBridge.main L hL hdet horth
