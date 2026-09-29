-- Prove2me | solution 1 for ChatterjeeQFT.massShellMeasure_unique
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T16:15:05.768033+00:00
-- url     : https://prove2.me/submissions/165cae0d-4e3d-4ac2-b110-55d9a7464772

import Mathlib
import Definitions.Def_ChatterjeeQFT_MassShell

/-! 4ffc4493 ChatterjeeQFT.massShellMeasure_unique (Chatterjee, Lectures on QFT, 10.1).
Route: the solvable subgroup `AN` of `SO↑(1,3)` (null rotations `N_{a,b}` about the light-like
direction `e₀ + e₃`, composed with boosts `B_s` along the 3-axis) acts simply transitively on the
mass shell.  We realise `AN` as `ℝ × ℝ × ℝ` with `(a,b,s)(a',b',s') = (a + eˢa', b + eˢb', s + s')`,
an explicit restricted Lorentz matrix `Mg g`, and the orbit map `phi g = Mg g (m,0,0,0)` with the
explicit measurable inverse `psi` on the shell.  For any `μ` as in the statement, `psi_* μ` is a
left-invariant measure on `AN`, finite on compacts, hence a multiple of Haar measure
(`isMulLeftInvariant_eq_smul`), and `μ = phi_* psi_* μ`.  Applying this to `μ` and to `λ_m`
(invariant by our accepted 1c0484f7, whose lemmas are copied here) and using `λ_m ≠ 0` gives
`μ = c • λ_m`.  No `Theorems.*` module is imported. -/

set_option autoImplicit false

open MeasureTheory Matrix
open scoped ENNReal

namespace ChatterjeeQFTUnique

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

/-! ### The group `AN` -/

/-- The group `AN ≅ ℝ² ⋊ ℝ`, as `ℝ × ℝ × ℝ` with
`(a,b,s)(a',b',s') = (a + eˢa', b + eˢb', s + s')`. -/
def AN : Type := ℝ × ℝ × ℝ

namespace AN

instance : TopologicalSpace AN := inferInstanceAs (TopologicalSpace (ℝ × ℝ × ℝ))
instance : MeasurableSpace AN := inferInstanceAs (MeasurableSpace (ℝ × ℝ × ℝ))
instance : BorelSpace AN := inferInstanceAs (BorelSpace (ℝ × ℝ × ℝ))
instance : LocallyCompactSpace AN := inferInstanceAs (LocallyCompactSpace (ℝ × ℝ × ℝ))
instance : SecondCountableTopology AN := inferInstanceAs (SecondCountableTopology (ℝ × ℝ × ℝ))
instance : T2Space AN := inferInstanceAs (T2Space (ℝ × ℝ × ℝ))
instance : Nonempty AN := inferInstanceAs (Nonempty (ℝ × ℝ × ℝ))

def mk (x y z : ℝ) : AN := (x, y, z)
def a (g : AN) : ℝ := (show ℝ × ℝ × ℝ from g).1
def b (g : AN) : ℝ := (show ℝ × ℝ × ℝ from g).2.1
def s (g : AN) : ℝ := (show ℝ × ℝ × ℝ from g).2.2

@[simp] theorem a_mk (x y z : ℝ) : (mk x y z).a = x := rfl
@[simp] theorem b_mk (x y z : ℝ) : (mk x y z).b = y := rfl
@[simp] theorem s_mk (x y z : ℝ) : (mk x y z).s = z := rfl

theorem ext' {g h : AN} (h1 : g.a = h.a) (h2 : g.b = h.b) (h3 : g.s = h.s) : g = h :=
  Prod.ext h1 (Prod.ext h2 h3)

@[fun_prop] theorem continuous_a : Continuous a := continuous_fst
@[fun_prop] theorem continuous_b : Continuous b := continuous_fst.comp continuous_snd
@[fun_prop] theorem continuous_s : Continuous s := continuous_snd.comp continuous_snd

theorem continuous_mk' {X : Type*} [TopologicalSpace X] {f g h : X → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hh : Continuous h) : Continuous fun x => mk (f x) (g x) (h x) :=
  hf.prodMk (hg.prodMk hh)

theorem measurable_mk' {X : Type*} [MeasurableSpace X] {f g h : X → ℝ} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) : Measurable fun x => mk (f x) (g x) (h x) :=
  hf.prodMk (hg.prodMk hh)

noncomputable instance : Mul AN :=
  ⟨fun g h => mk (g.a + Real.exp g.s * h.a) (g.b + Real.exp g.s * h.b) (g.s + h.s)⟩
instance : One AN := ⟨mk 0 0 0⟩
noncomputable instance : Inv AN :=
  ⟨fun g => mk (-(Real.exp (-g.s) * g.a)) (-(Real.exp (-g.s) * g.b)) (-g.s)⟩

theorem mul_def (g h : AN) :
    g * h = mk (g.a + Real.exp g.s * h.a) (g.b + Real.exp g.s * h.b) (g.s + h.s) := rfl
theorem one_def : (1 : AN) = mk 0 0 0 := rfl
theorem inv_def (g : AN) :
    g⁻¹ = mk (-(Real.exp (-g.s) * g.a)) (-(Real.exp (-g.s) * g.b)) (-g.s) := rfl

theorem mul_assoc' (g h k : AN) : g * h * k = g * (h * k) := by
  simp only [mul_def]
  refine ext' ?_ ?_ ?_ <;> simp only [a_mk, b_mk, s_mk, Real.exp_add] <;> ring

theorem one_mul' (g : AN) : 1 * g = g := by
  simp only [mul_def, one_def]
  refine ext' ?_ ?_ ?_ <;> simp

theorem mul_one' (g : AN) : g * 1 = g := by
  simp only [mul_def, one_def]
  refine ext' ?_ ?_ ?_ <;> simp

theorem inv_mul_cancel' (g : AN) : g⁻¹ * g = 1 := by
  simp only [mul_def, inv_def, one_def]
  refine ext' ?_ ?_ ?_ <;> simp only [a_mk, b_mk, s_mk] <;> ring

noncomputable instance : Group AN where
  mul := (· * ·)
  one := 1
  inv := (·⁻¹)
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  inv_mul_cancel := inv_mul_cancel'

instance : IsTopologicalGroup AN where
  continuous_mul := by
    show Continuous fun p : AN × AN =>
      mk (p.1.a + Real.exp p.1.s * p.2.a) (p.1.b + Real.exp p.1.s * p.2.b) (p.1.s + p.2.s)
    exact continuous_mk' (by fun_prop) (by fun_prop) (by fun_prop)
  continuous_inv := by
    show Continuous fun g : AN =>
      mk (-(Real.exp (-g.s) * g.a)) (-(Real.exp (-g.s) * g.b)) (-g.s)
    exact continuous_mk' (by fun_prop) (by fun_prop) (by fun_prop)

end AN

open AN

/-! ### The Lorentz matrices of `AN` -/

/-- `N_{a,b} ∘ B_s` with `E = e^{-s}`, `F = eˢ`. -/
noncomputable def Mat (a b E F : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(E + F + (a ^ 2 + b ^ 2) * E) / 2, a, b, (E - F + (a ^ 2 + b ^ 2) * E) / 2;
     a * E, 1, 0, a * E;
     b * E, 0, 1, b * E;
     (E - F - (a ^ 2 + b ^ 2) * E) / 2, -a, -b, (E + F - (a ^ 2 + b ^ 2) * E) / 2]

theorem Mat_lorentz (a b E F : ℝ) (h : E * F = 1) : IsLorentz (Mat a b E F) := by
  intro x y
  simp [Mat, minkowskiInner, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  linear_combination (x 0 * y 0 - x 3 * y 3) * h

theorem Mat_det (a b E F : ℝ) (h : E * F = 1) : (Mat a b E F).det = 1 := by
  simp [Mat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  linear_combination h

theorem exp_neg_mul_exp (s : ℝ) : Real.exp (-s) * Real.exp s = 1 := by
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

noncomputable def Mg (g : AN) : Matrix (Fin 4) (Fin 4) ℝ :=
  Mat g.a g.b (Real.exp (-g.s)) (Real.exp g.s)

theorem Mg_restricted (g : AN) : IsRestrictedLorentz (Mg g) := by
  refine ⟨Mat_lorentz _ _ _ _ (exp_neg_mul_exp _), Mat_det _ _ _ _ (exp_neg_mul_exp _), ?_⟩
  simp only [Mg, Mat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  positivity

/-! ### The orbit map and its inverse -/

noncomputable def phi (m : ℝ) (g : AN) : Fin 4 → ℝ :=
  ![m * (Real.exp (-g.s) + Real.exp g.s + (g.a ^ 2 + g.b ^ 2) * Real.exp (-g.s)) / 2,
    m * g.a * Real.exp (-g.s), m * g.b * Real.exp (-g.s),
    m * (Real.exp (-g.s) - Real.exp g.s - (g.a ^ 2 + g.b ^ 2) * Real.exp (-g.s)) / 2]

noncomputable def psi (m : ℝ) (p : Fin 4 → ℝ) : AN :=
  mk (p 1 / (p 0 + p 3)) (p 2 / (p 0 + p 3)) (Real.log m - Real.log (p 0 + p 3))

theorem continuous_phi (m : ℝ) : Continuous (phi m) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [phi] <;> fun_prop

theorem measurable_psi (m : ℝ) : Measurable (psi m) := by
  unfold psi
  refine measurable_mk' ?_ ?_ ?_
  · exact (measurable_pi_apply 1).div ((measurable_pi_apply 0).add (measurable_pi_apply 3))
  · exact (measurable_pi_apply 2).div ((measurable_pi_apply 0).add (measurable_pi_apply 3))
  · exact measurable_const.sub
      (Real.measurable_log.comp ((measurable_pi_apply 0).add (measurable_pi_apply 3)))

theorem Mg_phi (m : ℝ) (g h : AN) : Mg g *ᵥ phi m h = phi m (g * h) := by
  funext i
  fin_cases i <;>
    simp [Mg, Mat, phi, mul_def, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Real.exp_add,
      Real.exp_neg] <;>
    field_simp <;> ring

theorem phi_u (m : ℝ) (g : AN) : phi m g 0 + phi m g 3 = m * Real.exp (-g.s) := by
  simp [phi]; ring

theorem psi_phi {m : ℝ} (hm : 0 < m) (g : AN) : psi m (phi m g) = g := by
  have hu := phi_u m g
  have hE : 0 < Real.exp (-g.s) := Real.exp_pos _
  have hm0 : m ≠ 0 := hm.ne'
  have hE0 : Real.exp (-g.s) ≠ 0 := hE.ne'
  unfold psi
  rw [hu]
  refine ext' ?_ ?_ ?_
  · simp only [a_mk]
    show m * g.a * Real.exp (-g.s) / (m * Real.exp (-g.s)) = g.a
    field_simp
  · simp only [b_mk]
    show m * g.b * Real.exp (-g.s) / (m * Real.exp (-g.s)) = g.b
    field_simp
  · simp only [s_mk]
    rw [Real.log_mul hm0 hE0, Real.log_exp]
    ring

theorem shell_u_pos {m : ℝ} (hm : 0 < m) {p : Fin 4 → ℝ} (hp : p ∈ massShell m) :
    0 < p 0 + p 3 := by
  obtain ⟨h1, h2⟩ := hp
  simp only [minkowskiSq, minkowskiInner] at h1
  have hlt : p 3 ^ 2 < p 0 ^ 2 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2)]
  have := abs_lt_of_sq_lt_sq' hlt h2
  linarith [this.1]

theorem phi_psi {m : ℝ} (hm : 0 < m) {p : Fin 4 → ℝ} (hp : p ∈ massShell m) :
    phi m (psi m p) = p := by
  have hu := shell_u_pos hm hp
  have hsh : p 0 ^ 2 - (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) = m ^ 2 := by
    have := hp.1
    simp only [minkowskiSq, minkowskiInner] at this
    linear_combination this
  have hm0 : m ≠ 0 := hm.ne'
  have hu0 : p 0 + p 3 ≠ 0 := hu.ne'
  have hE : Real.exp (-(psi m p).s) = (p 0 + p 3) / m := by
    show Real.exp (-(Real.log m - Real.log (p 0 + p 3))) = (p 0 + p 3) / m
    rw [neg_sub, Real.exp_sub, Real.exp_log hu, Real.exp_log hm]
  have hF : Real.exp (psi m p).s = m / (p 0 + p 3) := by
    show Real.exp (Real.log m - Real.log (p 0 + p 3)) = m / (p 0 + p 3)
    rw [Real.exp_sub, Real.exp_log hu, Real.exp_log hm]
  have ha : (psi m p).a = p 1 / (p 0 + p 3) := rfl
  have hb : (psi m p).b = p 2 / (p 0 + p 3) := rfl
  have hv : (m ^ 2 + p 1 ^ 2 + p 2 ^ 2) / (p 0 + p 3) = p 0 - p 3 := by
    rw [div_eq_iff hu0]; linear_combination -hsh
  funext i
  fin_cases i
  · show m * (Real.exp (-(psi m p).s) + Real.exp (psi m p).s
      + ((psi m p).a ^ 2 + (psi m p).b ^ 2) * Real.exp (-(psi m p).s)) / 2 = p 0
    rw [hE, hF, ha, hb]
    have e : m * ((p 0 + p 3) / m + m / (p 0 + p 3)
        + ((p 1 / (p 0 + p 3)) ^ 2 + (p 2 / (p 0 + p 3)) ^ 2) * ((p 0 + p 3) / m)) / 2
        = ((p 0 + p 3) + (m ^ 2 + p 1 ^ 2 + p 2 ^ 2) / (p 0 + p 3)) / 2 := by
      field_simp; ring
    rw [e, hv]; ring
  · show m * (psi m p).a * Real.exp (-(psi m p).s) = p 1
    rw [hE, ha]; field_simp
  · show m * (psi m p).b * Real.exp (-(psi m p).s) = p 2
    rw [hE, hb]; field_simp
  · show m * (Real.exp (-(psi m p).s) - Real.exp (psi m p).s
      - ((psi m p).a ^ 2 + (psi m p).b ^ 2) * Real.exp (-(psi m p).s)) / 2 = p 3
    rw [hE, hF, ha, hb]
    have e : m * ((p 0 + p 3) / m - m / (p 0 + p 3)
        - ((p 1 / (p 0 + p 3)) ^ 2 + (p 2 / (p 0 + p 3)) ^ 2) * ((p 0 + p 3) / m)) / 2
        = ((p 0 + p 3) - (m ^ 2 + p 1 ^ 2 + p 2 ^ 2) / (p 0 + p 3)) / 2 := by
      field_simp; ring
    rw [e, hv]; ring

/-! ### Invariant measures on the shell are multiples of `phi_* haar` -/

theorem key {m : ℝ} (hm : 0 < m) (μ : Measure (Fin 4 → ℝ)) [IsFiniteMeasureOnCompacts μ]
    (hμ : μ (massShell m)ᶜ = 0)
    (hinv : ∀ g : AN, Measure.map (fun p : Fin 4 → ℝ => Mg g *ᵥ p) μ = μ) :
    ∃ c : NNReal, μ = c • Measure.map (phi m) (Measure.haar : Measure AN) := by
  have hae : ∀ᵐ p ∂μ, p ∈ massShell m := mem_ae_iff.2 hμ
  have hpsi := measurable_psi m
  have hphi := (continuous_phi m).measurable
  have hμν : μ = Measure.map (phi m) (Measure.map (psi m) μ) := by
    rw [Measure.map_map hphi hpsi]
    conv_lhs => rw [← Measure.map_id (μ := μ)]
    exact Measure.map_congr (hae.mono fun p hp => (phi_psi hm hp).symm)
  have hfin : IsFiniteMeasureOnCompacts (Measure.map (psi m) μ) := ⟨fun K hK => by
    rw [Measure.map_apply hpsi hK.isClosed.measurableSet]
    calc μ (psi m ⁻¹' K) ≤ μ (phi m '' K ∪ (massShell m)ᶜ) := measure_mono (fun p hp => by
            by_cases h : p ∈ massShell m
            · exact Or.inl ⟨psi m p, hp, phi_psi hm h⟩
            · exact Or.inr h)
      _ ≤ μ (phi m '' K) + μ (massShell m)ᶜ := measure_union_le _ _
      _ < ⊤ := by rw [hμ, add_zero]; exact (hK.image (continuous_phi m)).measure_lt_top⟩
  have hleft : Measure.IsMulLeftInvariant (Measure.map (psi m) μ) := ⟨fun g => by
    have hmul : Measurable (fun h : AN => g * h) := (continuous_const_mul g).measurable
    have hM : Measurable (fun p : Fin 4 → ℝ => Mg g *ᵥ p) :=
      (Continuous.matrix_mulVec continuous_const continuous_id).measurable
    rw [Measure.map_map hmul hpsi]
    conv_rhs => rw [← hinv g]
    rw [Measure.map_map hpsi hM]
    refine Measure.map_congr (hae.mono fun p hp => ?_)
    show g * psi m p = psi m (Mg g *ᵥ p)
    calc g * psi m p = psi m (phi m (g * psi m p)) := (psi_phi hm _).symm
      _ = psi m (Mg g *ᵥ phi m (psi m p)) := by rw [Mg_phi]
      _ = psi m (Mg g *ᵥ p) := by rw [phi_psi hm hp]⟩
  have hν := Measure.isMulLeftInvariant_eq_smul (Measure.map (psi m) μ) (Measure.haar : Measure AN)
  refine ⟨Measure.haarScalarFactor (Measure.map (psi m) μ) (Measure.haar : Measure AN), ?_⟩
  calc μ = Measure.map (phi m) (Measure.map (psi m) μ) := hμν
    _ = Measure.map (phi m) (Measure.haarScalarFactor (Measure.map (psi m) μ) (Measure.haar : Measure AN)
          • (Measure.haar : Measure AN)) := congrArg _ hν
    _ = _ := Measure.map_smul _ _ _

/-! ### Facts about `λ_m` -/

theorem isClosed_massShell (m : ℝ) : IsClosed (massShell m) := by
  have h1 : Continuous minkowskiSq := by unfold minkowskiSq minkowskiInner; fun_prop
  exact (isClosed_eq h1 continuous_const).inter (isClosed_le continuous_const (continuous_apply 0))

theorem massShellMeasure_compl {m : ℝ} : massShellMeasure m (massShell m)ᶜ = 0 := by
  unfold massShellMeasure
  rw [Measure.map_apply (continuous_massShellEmb m).measurable
    (isClosed_massShell m).measurableSet.compl]
  have : massShellEmb m ⁻¹' (massShell m)ᶜ = ∅ := by
    ext q; simp [massShellEmb_mem]
  rw [this, measure_empty]

theorem density_measurable (m : ℝ) : Measurable fun q : Fin 3 → ℝ =>
    ENNReal.ofReal (1 / ((2 * Real.pi) ^ 3 * (2 * omega m q))) :=
  (measurable_const.div (measurable_const.mul
    (measurable_const.mul (continuous_omega m).measurable))).ennreal_ofReal

theorem massShellMeasure_ne_zero {m : ℝ} (hm : 0 < m) : massShellMeasure m ≠ 0 := by
  intro h
  unfold massShellMeasure at h
  rw [Measure.map_eq_zero_iff (continuous_massShellEmb m).measurable.aemeasurable,
    withDensity_eq_zero_iff (density_measurable m).aemeasurable] at h
  obtain ⟨q, hq⟩ := h.exists
  have hω := omega_pos hm q
  have hpos : 0 < 1 / ((2 * Real.pi) ^ 3 * (2 * omega m q)) := by positivity
  have : ENNReal.ofReal (1 / ((2 * Real.pi) ^ 3 * (2 * omega m q))) = 0 := hq
  rw [ENNReal.ofReal_eq_zero] at this
  linarith

theorem massShellMeasure_finite {m : ℝ} (hm : 0 < m) :
    IsFiniteMeasureOnCompacts (massShellMeasure m) := by
  have hf : Continuous fun q : Fin 3 → ℝ => 1 / ((2 * Real.pi) ^ 3 * (2 * omega m q)) := by
    refine continuous_const.div (continuous_const.mul (continuous_const.mul (continuous_omega m)))
      ?_
    intro q
    have := omega_pos hm q
    positivity
  haveI := IsLocallyFiniteMeasure.withDensity_ofReal (μ := (volume : Measure (Fin 3 → ℝ))) hf
  have hproj : Continuous proj3 := continuous_pi fun i => continuous_apply _
  refine ⟨fun K hK => ?_⟩
  unfold massShellMeasure
  rw [Measure.map_apply (continuous_massShellEmb m).measurable hK.isClosed.measurableSet]
  have hsub : massShellEmb m ⁻¹' K ⊆ proj3 '' K := fun q hq =>
    ⟨massShellEmb m q, hq, proj3_massShellEmb m q⟩
  exact (measure_mono hsub).trans_lt (hK.image hproj).measure_lt_top

theorem main (m : ℝ) (hm : 0 < m) (μ : Measure (Fin 4 → ℝ))
    [IsFiniteMeasureOnCompacts μ] (hμ : μ (massShell m)ᶜ = 0)
    (hinv : ∀ L : Matrix (Fin 4) (Fin 4) ℝ, IsRestrictedLorentz L →
      Measure.map (fun p : Fin 4 → ℝ => L *ᵥ p) μ = μ) :
    ∃ c : ℝ≥0∞, μ = c • massShellMeasure m := by
  have := massShellMeasure_finite hm
  obtain ⟨c1, h1⟩ := key hm μ hμ
    (fun g => hinv _ (Mg_restricted g))
  obtain ⟨c2, h2⟩ := key hm (massShellMeasure m)
    massShellMeasure_compl
    (fun g => lorentz_invariant hm (Mg_restricted g))
  have hc2 : c2 ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h2
    exact massShellMeasure_ne_zero hm h2
  refine ⟨((c1 / c2 : NNReal) : ℝ≥0∞), ?_⟩
  rw [← ENNReal.smul_def, h2, smul_smul, div_mul_cancel₀ c1 hc2]
  exact h1


end ChatterjeeQFTUnique

open MeasureTheory Matrix ChatterjeeQFT ENNReal in
theorem solution (m : ℝ) (hm : 0 < m) (μ : Measure (Fin 4 → ℝ))
    [IsFiniteMeasureOnCompacts μ] (hμ : μ (massShell m)ᶜ = 0)
    (hinv : ∀ L : Matrix (Fin 4) (Fin 4) ℝ, IsRestrictedLorentz L →
      Measure.map (fun p : Fin 4 → ℝ => L *ᵥ p) μ = μ) :
    ∃ c : ℝ≥0∞, μ = c • massShellMeasure m := by
  exact ChatterjeeQFTUnique.main m hm μ hμ hinv
