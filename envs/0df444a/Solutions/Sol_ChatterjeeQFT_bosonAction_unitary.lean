-- Prove2me | solution 1 for ChatterjeeQFT.bosonAction_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T15:11:26.359986+00:00
-- url     : https://prove2.me/submissions/10f10bb2-b5a0-431a-bea9-d6c790f2fc9e

import Mathlib
import Definitions.Def_ChatterjeeQFT_MassShell

/-! 25ee4f69 ChatterjeeQFT.bosonAction_unitary (Chatterjee, Lectures on QFT, 11.3).
Route: the phase `exp(i(a,p))` has modulus one, so the integrand equals
`conj ψ(L⁻¹p) φ(L⁻¹p)`.  The measure `λ_m` is invariant under every restricted Lorentz `L`
(proof reused from our accepted 1c0484f7: change of variables on ℝ³ with Jacobian
`ω_{Φq}/ω_q`), hence under `L⁻¹` (as `det L = 1`), and the change of variables `p ↦ L⁻¹p`
(a measurable embedding) gives the claim.  No `Theorems.*` module is imported. -/

set_option autoImplicit false

open MeasureTheory Matrix
open scoped ENNReal

namespace ChatterjeeQFTUnitary

open ChatterjeeQFT

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

theorem abs_det_lorentz (N : Matrix (Fin 4) (Fin 4) ℝ) (h : Nᵀ * eta * N = eta) :
    |N.det| = 1 := by
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h2
  have he : (eta).det = -1 := by
    simp [eta, Matrix.det_diagonal, Fin.prod_univ_four]
  rw [he] at h2
  have hsq : |N.det| ^ 2 = 1 := by rw [sq_abs]; linarith
  nlinarith [abs_nonneg N.det]

/-- The Jacobian matrix of `q ↦ spatial part of N (ω_q, q)`, with `v = q / ω_q`. -/
def jac (N : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => N i.succ j.succ + N i.succ 0 * v j

theorem det_jac (N : Matrix (Fin 4) (Fin 4) ℝ) (h : Nᵀ * eta * N = eta) (v : Fin 3 → ℝ) :
    (jac N v).det = N.det * (N 0 0 + N 0 1 * v 0 + N 0 2 * v 1 + N 0 3 * v 2) := by
  have hadj := adjugate_lorentz N h
  have e0 := congrFun (congrFun hadj 0) 0
  have e1 := congrFun (congrFun hadj 1) 0
  have e2 := congrFun (congrFun hadj 2) 0
  have e3 := congrFun (congrFun hadj 3) 0
  simp [adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three, eta, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Fin.succAbove] at e0 e1 e2 e3
  rw [Matrix.det_fin_three]
  have s0 : (Fin.succ (0 : Fin 3) : Fin 4) = 1 := rfl
  have s1 : (Fin.succ (1 : Fin 3) : Fin 4) = 2 := rfl
  have s2 : (Fin.succ (2 : Fin 3) : Fin 4) = 3 := rfl
  simp only [jac, Matrix.of_apply, s0, s1, s2]
  linear_combination e0 - v 0 * e1 - v 1 * e2 - v 2 * e3

theorem omega_sq (m : ℝ) (q : Fin 3 → ℝ) :
    omega m q ^ 2 = m ^ 2 + (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2) :=
  Real.sq_sqrt (by positivity)

theorem omega_pos {m : ℝ} (hm : 0 < m) (q : Fin 3 → ℝ) : 0 < omega m q :=
  Real.sqrt_pos.mpr (by positivity)

theorem continuous_omega (m : ℝ) : Continuous (omega m) := by
  unfold omega; fun_prop

theorem continuous_massShellEmb (m : ℝ) : Continuous (massShellEmb m) := by
  unfold massShellEmb
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_omega m
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_apply 2

theorem massShellEmb_mem (m : ℝ) (q : Fin 3 → ℝ) : massShellEmb m q ∈ massShell m := by
  refine ⟨?_, ?_⟩
  · have h := omega_sq m q
    simp only [minkowskiSq, minkowskiInner, massShellEmb]
    simp
    nlinarith [h]
  · simp only [massShellEmb]
    simp [omega, Real.sqrt_nonneg]

/-- spatial part of a four-vector -/
def proj3 (p : Fin 4 → ℝ) : Fin 3 → ℝ := fun i => p i.succ

theorem proj3_massShellEmb (m : ℝ) (q : Fin 3 → ℝ) : proj3 (massShellEmb m q) = q := by
  ext i; fin_cases i <;> rfl

theorem massShellEmb_proj3 {m : ℝ} {p : Fin 4 → ℝ} (hp : p ∈ massShell m) :
    massShellEmb m (proj3 p) = p := by
  obtain ⟨h1, h2⟩ := hp
  simp only [minkowskiSq, minkowskiInner] at h1
  ext i; fin_cases i
  · show Real.sqrt (m ^ 2 + (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2)) = p 0
    rw [show m ^ 2 + (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) = p 0 ^ 2 by nlinarith]
    exact Real.sqrt_sq h2
  · rfl
  · rfl
  · rfl

/-- The induced map on three-momenta. -/
noncomputable def Phi (m : ℝ) (N : Matrix (Fin 4) (Fin 4) ℝ) (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  proj3 (N *ᵥ massShellEmb m q)

theorem hasFDerivAt_omega {m : ℝ} (hm : 0 < m) (q : Fin 3 → ℝ) :
    HasFDerivAt (omega m)
      (∑ j : Fin 3, (q j / omega m q) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j) q := by
  have hg := ((((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 0 q).pow 2).add
    ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 1 q).pow 2)).add
      ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 2 q).pow 2)).const_add (m ^ 2)
  have hne : m ^ 2 + (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2) ≠ 0 := by positivity
  have h := hg.sqrt hne
  refine h.congr_fderiv ?_
  have hω := omega_pos hm q
  ext h
  simp [Fin.sum_univ_three]
  unfold omega at hω ⊢
  field_simp

theorem hasFDerivAt_Phi {m : ℝ} (hm : 0 < m) (N : Matrix (Fin 4) (Fin 4) ℝ) (q : Fin 3 → ℝ) :
    HasFDerivAt (Phi m N)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (jac N fun j => q j / omega m q))) q := by
  rw [hasFDerivAt_pi']
  intro i
  have hform : (fun q => Phi m N q i) = fun q => N i.succ 0 * omega m q +
      N i.succ 1 * q 0 + N i.succ 2 * q 1 + N i.succ 3 * q 2 := by
    funext q
    simp [Phi, proj3, massShellEmb, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  rw [hform]
  have h := ((((hasFDerivAt_omega hm q).const_mul (N i.succ 0)).add
    ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 0 q).const_mul (N i.succ 1))).add
      ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 1 q).const_mul (N i.succ 2))).add
      ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) 2 q).const_mul (N i.succ 3))
  refine h.congr_fderiv ?_
  ext h
  simp [jac, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem Phi_emb {m : ℝ} {N : Matrix (Fin 4) (Fin 4) ℝ}
    (hshell : ∀ p ∈ massShell m, N *ᵥ p ∈ massShell m) (q : Fin 3 → ℝ) :
    massShellEmb m (Phi m N q) = N *ᵥ massShellEmb m q :=
  massShellEmb_proj3 (hshell _ (massShellEmb_mem m q))

theorem omega_Phi {m : ℝ} {N : Matrix (Fin 4) (Fin 4) ℝ}
    (hshell : ∀ p ∈ massShell m, N *ᵥ p ∈ massShell m) (q : Fin 3 → ℝ) :
    omega m (Phi m N q) = (N *ᵥ massShellEmb m q) 0 :=
  congrFun (Phi_emb hshell q) 0

theorem abs_det_jac {m : ℝ} (hm : 0 < m) {N : Matrix (Fin 4) (Fin 4) ℝ}
    (hSq : ∀ x, minkowskiSq (N *ᵥ x) = minkowskiSq x)
    (hshell : ∀ p ∈ massShell m, N *ᵥ p ∈ massShell m) (q : Fin 3 → ℝ) :
    |(jac N fun j => q j / omega m q).det| = omega m (Phi m N q) / omega m q := by
  have hL := lorentz_matrix N hSq
  have hω := omega_pos hm q
  rw [det_jac N hL, abs_mul, abs_det_lorentz N hL, one_mul, omega_Phi hshell]
  have key : N 0 0 + N 0 1 * (q 0 / omega m q) + N 0 2 * (q 1 / omega m q)
      + N 0 3 * (q 2 / omega m q) = (N *ᵥ massShellEmb m q) 0 / omega m q := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, massShellEmb]
    field_simp
  rw [key, abs_div, abs_of_pos hω, abs_of_nonneg (hshell _ (massShellEmb_mem m q)).2]

theorem mulVec_injective_of_lorentz {N : Matrix (Fin 4) (Fin 4) ℝ}
    (hSq : ∀ x, minkowskiSq (N *ᵥ x) = minkowskiSq x) : Function.Injective (N *ᵥ ·) := by
  have h := abs_det_lorentz N (lorentz_matrix N hSq)
  have h0 : N.det ≠ 0 := by intro h0; rw [h0, abs_zero] at h; exact zero_ne_one h
  exact Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det N).mpr (isUnit_iff_ne_zero.mpr h0))

theorem Phi_injective {m : ℝ} {N : Matrix (Fin 4) (Fin 4) ℝ}
    (hSq : ∀ x, minkowskiSq (N *ᵥ x) = minkowskiSq x)
    (hshell : ∀ p ∈ massShell m, N *ᵥ p ∈ massShell m) : Function.Injective (Phi m N) := by
  intro q1 q2 h
  have h1 := congrArg (massShellEmb m) h
  rw [Phi_emb hshell, Phi_emb hshell] at h1
  have h2 : massShellEmb m q1 = massShellEmb m q2 := mulVec_injective_of_lorentz hSq h1
  rw [← proj3_massShellEmb m q1, h2, proj3_massShellEmb]

theorem Phi_surjective {m : ℝ} {N : Matrix (Fin 4) (Fin 4) ℝ}
    (hsurj : ∀ p ∈ massShell m, ∃ p' ∈ massShell m, N *ᵥ p' = p) :
    Function.Surjective (Phi m N) := by
  intro q'
  obtain ⟨p', hp', hNp'⟩ := hsurj _ (massShellEmb_mem m q')
  refine ⟨proj3 p', ?_⟩
  simp only [Phi]
  rw [massShellEmb_proj3 hp', hNp', proj3_massShellEmb]

theorem map_Phi_withDensity {m : ℝ} (hm : 0 < m) {N : Matrix (Fin 4) (Fin 4) ℝ}
    (hSq : ∀ x, minkowskiSq (N *ᵥ x) = minkowskiSq x)
    (hshell : ∀ p ∈ massShell m, N *ᵥ p ∈ massShell m)
    (hsurj : ∀ p ∈ massShell m, ∃ p' ∈ massShell m, N *ᵥ p' = p) :
    Measure.map (Phi m N) ((volume : Measure (Fin 3 → ℝ)).withDensity fun q =>
      ENNReal.ofReal (1 / ((2 * Real.pi) ^ 3 * (2 * omega m q))))
      = (volume : Measure (Fin 3 → ℝ)).withDensity fun q =>
      ENNReal.ofReal (1 / ((2 * Real.pi) ^ 3 * (2 * omega m q))) := by
  have hdiff : Differentiable ℝ (Phi m N) := fun q => (hasFDerivAt_Phi hm N q).differentiableAt
  have hmeas : Measurable (Phi m N) := hdiff.continuous.measurable
  ext S hS
  rw [Measure.map_apply hmeas hS, withDensity_apply _ (hmeas hS), withDensity_apply _ hS]
  conv_rhs => rw [← Set.image_preimage_eq S (Phi_surjective hsurj)]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hmeas hS)
    (fun x _ => (hasFDerivAt_Phi hm N x).hasFDerivWithinAt) (Phi_injective hSq hshell).injOn]
  refine setLIntegral_congr_fun (hmeas hS) (fun x _ => ?_)
  have hdet : (LinearMap.toContinuousLinearMap
      (Matrix.toLin' (jac N fun j => x j / omega m x))).det
      = (jac N fun j => x j / omega m x).det := by
    rw [ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin']
  rw [hdet, abs_det_jac hm hSq hshell x]
  have hω := omega_pos hm x
  have hω' := omega_pos hm (Phi m N x)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

theorem massShellMeasure_map {m : ℝ} (hm : 0 < m) {N : Matrix (Fin 4) (Fin 4) ℝ}
    (hSq : ∀ x, minkowskiSq (N *ᵥ x) = minkowskiSq x)
    (hshell : ∀ p ∈ massShell m, N *ᵥ p ∈ massShell m)
    (hsurj : ∀ p ∈ massShell m, ∃ p' ∈ massShell m, N *ᵥ p' = p) :
    Measure.map (fun p => N *ᵥ p) (massShellMeasure m) = massShellMeasure m := by
  have hdiff : Differentiable ℝ (Phi m N) := fun q => (hasFDerivAt_Phi hm N q).differentiableAt
  have hPmeas : Measurable (Phi m N) := hdiff.continuous.measurable
  have hN : Measurable (fun p : Fin 4 → ℝ => N *ᵥ p) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hE : Measurable (massShellEmb m) := (continuous_massShellEmb m).measurable
  unfold massShellMeasure
  rw [Measure.map_map hN hE]
  have hcomp : (fun p => N *ᵥ p) ∘ massShellEmb m = massShellEmb m ∘ Phi m N :=
    funext fun q => (Phi_emb hshell q).symm
  rw [hcomp, ← Measure.map_map hE hPmeas, map_Phi_withDensity hm hSq hshell hsurj]


/-- Reverse Cauchy-Schwarz for future-pointing vectors. -/
theorem future_pair_nonneg (a0 a1 a2 a3 p0 p1 p2 p3 : ℝ) (ha0 : 0 < a0)
    (ha : a1 ^ 2 + a2 ^ 2 + a3 ^ 2 ≤ a0 ^ 2) (hp0 : 0 ≤ p0)
    (hp : p1 ^ 2 + p2 ^ 2 + p3 ^ 2 ≤ p0 ^ 2) :
    0 ≤ a0 * p0 + (a1 * p1 + a2 * p2 + a3 * p3) := by
  set s := a1 * p1 + a2 * p2 + a3 * p3 with hs
  have hlag : s ^ 2 + ((a1 * p2 - a2 * p1) ^ 2 + (a1 * p3 - a3 * p1) ^ 2 + (a2 * p3 - a3 * p2) ^ 2)
      = (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) * (p1 ^ 2 + p2 ^ 2 + p3 ^ 2) := by rw [hs]; ring
  have hA : 0 ≤ a1 ^ 2 + a2 ^ 2 + a3 ^ 2 := by positivity
  have hP : 0 ≤ p1 ^ 2 + p2 ^ 2 + p3 ^ 2 := by positivity
  have hprod : (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) * (p1 ^ 2 + p2 ^ 2 + p3 ^ 2) ≤ a0 ^ 2 * p0 ^ 2 :=
    mul_le_mul ha hp hP (sq_nonneg _)
  have hs2 : s ^ 2 ≤ (a0 * p0) ^ 2 := by
    nlinarith [sq_nonneg (a1 * p2 - a2 * p1), sq_nonneg (a1 * p3 - a3 * p1),
      sq_nonneg (a2 * p3 - a3 * p2)]
  have hap : 0 ≤ a0 * p0 := mul_nonneg ha0.le hp0
  have hb := abs_le_of_sq_le_sq' hs2 hap
  linarith [hb.1]

theorem sq_of_lorentz (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsLorentz L) :
    ∀ x, minkowskiSq (L *ᵥ x) = minkowskiSq x := fun x => hL x x

theorem right_inv_lorentz (L : Matrix (Fin 4) (Fin 4) ℝ) (h : Lᵀ * eta * L = eta) :
    L * (eta * Lᵀ * eta) = 1 := by
  have hleft : (eta * Lᵀ * eta) * L = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Lᵀ, h, eta_mul_eta]
  exact mul_eq_one_comm.mp hleft

theorem row0_lorentz (L : Matrix (Fin 4) (Fin 4) ℝ) (h : Lᵀ * eta * L = eta) :
    L 0 0 ^ 2 - (L 0 1 ^ 2 + L 0 2 ^ 2 + L 0 3 ^ 2) = 1 := by
  have e := congrFun (congrFun (right_inv_lorentz L h) 0) 0
  simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Fin.sum_univ_four] at e
  linear_combination e

theorem col0_lorentz (L : Matrix (Fin 4) (Fin 4) ℝ) (h : Lᵀ * eta * L = eta) :
    L 0 0 ^ 2 - (L 1 0 ^ 2 + L 2 0 ^ 2 + L 3 0 ^ 2) = 1 := by
  have e := congrFun (congrFun h 0) 0
  simp [eta, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Fin.sum_univ_four] at e
  linear_combination e

theorem shell_sq {m : ℝ} {p : Fin 4 → ℝ} (hp : p ∈ massShell m) :
    p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 ≤ p 0 ^ 2 := by
  obtain ⟨h1, _⟩ := hp
  simp only [minkowskiSq, minkowskiInner] at h1
  nlinarith [sq_nonneg m]

theorem restricted_shell {m : ℝ} {L : Matrix (Fin 4) (Fin 4) ℝ} (hL : IsRestrictedLorentz L) :
    ∀ p ∈ massShell m, L *ᵥ p ∈ massShell m := by
  intro p hp
  have hSq := sq_of_lorentz L hL.1
  have hη := lorentz_matrix L hSq
  have hrow := row0_lorentz L hη
  refine ⟨by rw [hSq]; exact hp.1, ?_⟩
  have key := future_pair_nonneg (L 0 0) (L 0 1) (L 0 2) (L 0 3) (p 0) (p 1) (p 2) (p 3)
    hL.2.2 (by linarith) hp.2 (shell_sq hp)
  have hform : (L *ᵥ p) 0 = L 0 0 * p 0 + (L 0 1 * p 1 + L 0 2 * p 2 + L 0 3 * p 3) := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]; ring
  rw [hform]; exact key

theorem restricted_surj {m : ℝ} {L : Matrix (Fin 4) (Fin 4) ℝ} (hL : IsRestrictedLorentz L) :
    ∀ p ∈ massShell m, ∃ p' ∈ massShell m, L *ᵥ p' = p := by
  intro p hp
  have hSq := sq_of_lorentz L hL.1
  have hη := lorentz_matrix L hSq
  have hcol := col0_lorentz L hη
  have hinv := right_inv_lorentz L hη
  have hLp : L *ᵥ ((eta * Lᵀ * eta) *ᵥ p) = p := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  refine ⟨(eta * Lᵀ * eta) *ᵥ p, ⟨?_, ?_⟩, hLp⟩
  · rw [← hSq, hLp]; exact hp.1
  · have key := future_pair_nonneg (L 0 0) (-L 1 0) (-L 2 0) (-L 3 0) (p 0) (p 1) (p 2) (p 3)
      hL.2.2 (by nlinarith) hp.2 (shell_sq hp)
    have hform : ((eta * Lᵀ * eta) *ᵥ p) 0
        = L 0 0 * p 0 + (-L 1 0 * p 1 + -L 2 0 * p 2 + -L 3 0 * p 3) := by
      simp [eta, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.mul_apply,
        Matrix.mul_diagonal, Matrix.diagonal_mul]
      ring
    rw [hform]; exact key

theorem lorentz_invariant {m : ℝ} (hm : 0 < m) {L : Matrix (Fin 4) (Fin 4) ℝ}
    (hL : IsRestrictedLorentz L) :
    Measure.map (fun p : Fin 4 → ℝ => L *ᵥ p) (massShellMeasure m) = massShellMeasure m :=
  massShellMeasure_map hm (sq_of_lorentz L hL.1) (restricted_shell hL) (restricted_surj hL)

theorem inv_invariant {m : ℝ} (hm : 0 < m) {L : Matrix (Fin 4) (Fin 4) ℝ}
    (hL : IsRestrictedLorentz L) :
    Measure.map (fun p : Fin 4 → ℝ => L⁻¹ *ᵥ p) (massShellMeasure m) = massShellMeasure m := by
  have hdet : IsUnit L.det := by rw [hL.2.1]; exact isUnit_one
  have hA : Measurable (fun p : Fin 4 → ℝ => L *ᵥ p) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hB : Measurable (fun p : Fin 4 → ℝ => L⁻¹ *ᵥ p) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  conv_lhs => rw [← lorentz_invariant hm hL]
  rw [Measure.map_map hB hA]
  have hid : (fun p : Fin 4 → ℝ => L⁻¹ *ᵥ p) ∘ (fun p : Fin 4 → ℝ => L *ᵥ p) = id := by
    funext p
    simp [Function.comp, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul L hdet]
  rw [hid, Measure.map_id]

/-- `p ↦ L⁻¹ p` as a homeomorphism. -/
noncomputable def invHomeo (L : Matrix (Fin 4) (Fin 4) ℝ) (hdet : IsUnit L.det) :
    (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) where
  toFun p := L⁻¹ *ᵥ p
  invFun p := L *ᵥ p
  left_inv p := by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv L hdet]
  right_inv p := by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul L hdet]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem phase_norm (x : ℝ) :
    (starRingEnd ℂ) (Complex.exp (Complex.I * (x : ℂ))) * Complex.exp (Complex.I * (x : ℂ)) = 1 := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_add]
  have : -Complex.I * (x : ℂ) + Complex.I * (x : ℂ) = 0 := by ring
  rw [this, Complex.exp_zero]

end ChatterjeeQFTUnitary

open MeasureTheory Matrix ChatterjeeQFT in
theorem solution (m : ℝ) (hm : 0 < m) (a : Fin 4 → ℝ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsRestrictedLorentz L)
    (ψ φ : (Fin 4 → ℝ) → ℂ) (hψ : MemLp ψ 2 (massShellMeasure m))
    (hφ : MemLp φ 2 (massShellMeasure m)) :
    ∫ p, (starRingEnd ℂ) (bosonAction a L ψ p) * bosonAction a L φ p ∂(massShellMeasure m)
      = ∫ p, (starRingEnd ℂ) (ψ p) * φ p ∂(massShellMeasure m) := by
  have hdet : IsUnit L.det := by rw [hL.2.1]; exact isUnit_one
  have hpt : ∀ p, (starRingEnd ℂ) (bosonAction a L ψ p) * bosonAction a L φ p
      = (fun q => (starRingEnd ℂ) (ψ q) * φ q) (L⁻¹ *ᵥ p) := by
    intro p
    simp only [bosonAction, map_mul]
    have h1 := ChatterjeeQFTUnitary.phase_norm (minkowskiInner a p)
    linear_combination ((starRingEnd ℂ) (ψ (L⁻¹ *ᵥ p)) * φ (L⁻¹ *ᵥ p)) * h1
  simp_rw [hpt]
  have hemb := (ChatterjeeQFTUnitary.invHomeo L hdet).toMeasurableEquiv.measurableEmbedding
  have key := hemb.integral_map (μ := massShellMeasure m)
    (fun q => (starRingEnd ℂ) (ψ q) * φ q)
  have hmap : Measure.map (ChatterjeeQFTUnitary.invHomeo L hdet).toMeasurableEquiv
      (massShellMeasure m) = massShellMeasure m :=
    ChatterjeeQFTUnitary.inv_invariant hm hL
  rw [hmap] at key
  exact key.symm
