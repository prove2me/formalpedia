-- Prove2me | solution 1 for ChatterjeeQFT.single_particle_spaces_poincare_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T16:14:21.069982+00:00
-- url     : https://prove2.me/submissions/27d4a475-9a01-4dfe-8706-3371eca4ac92

import Mathlib
import Definitions.Def_ChatterjeeQFT_ElectronSpace

/-! bd7ca1ae ChatterjeeQFT.single_particle_spaces_poincare_invariant
(Chatterjee, Lectures on QFT, 11.3 and 25.3).
Route.  Algebra: `det M(x) = x²`, `M(κ(B)x) = B M(x) Bᴴ` (so `κ(B)` preserves `x²` when
`det B = 1`, and `κ(B)κ(B⁻¹) = id`), Cayley-Hamilton `M(x)² = 2x⁰M(x) - x²·1`, hence
`V_p² = M(p)/m` on the shell (Lemma 25.1: `V_p⁻² = m·M(p)⁻¹`, so `Aᴴ V_p⁻² A = V_q⁻²` with
`q = κ(A⁻¹)p`); `κ(B)` keeps `p⁰ ≥ 0` because `B M(p) Bᴴ = m (BV_p)(BV_p)ᴴ`.
Measure: for any matrix `N` preserving `x²` and mapping the shell onto itself, the induced map
`Φ(q) = spatial part of N(ω_q, q)` on ℝ³ has Jacobian `det(N_s + N_{s0} (q/ω)ᵀ)`; the cofactor
identities `adj N = det N · η Nᵀ η` give `det = det N · (N(ω,q))⁰/ω`, `|det N| = 1`, so
`|det DΦ| = ω_{Φq}/ω_q` and the change of variables formula
(`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) shows `Φ` preserves `d³q/(2ω_q)`; hence
`N` preserves `massShellMeasure`.  Applied to `N = L⁻¹ = κ(A⁻¹)`.
No `Theorems.*` module is imported. -/

set_option autoImplicit false

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

namespace ChatterjeeQFTBuild

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

theorem minkowskiSq_kappa (B : Matrix (Fin 2) (Fin 2) ℂ) (hB : B.det = 1) (x : Fin 4 → ℝ) :
    minkowskiSq (kappa B x) = minkowskiSq x := by
  have h := congrArg Matrix.det (hermOfVec_kappa B x)
  rw [det_hermOfVec, Matrix.det_mul, Matrix.det_mul, det_hermOfVec, Matrix.det_conjTranspose,
    hB] at h
  simpa using h


theorem kappa_kappa (B C : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    kappa B (kappa C x) = kappa (B * C) x := by
  rw [kappa, hermOfVec_kappa, kappa, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem kappa_one (x : Fin 4 → ℝ) : kappa 1 x = x := by
  simp [kappa, vecOfHerm_hermOfVec]

theorem det_inv_eq_one (B : Matrix (Fin 2) (Fin 2) ℂ) (hB : B.det = 1) : (B⁻¹).det = 1 := by
  rw [Matrix.det_nonsing_inv, hB, Ring.inverse_one]

theorem kappa_kappa_inv (B : Matrix (Fin 2) (Fin 2) ℂ) (hB : B.det = 1) (x : Fin 4 → ℝ) :
    kappa B (kappa B⁻¹ x) = x := by
  have hu : IsUnit B.det := by rw [hB]; exact isUnit_one
  rw [kappa_kappa, Matrix.mul_nonsing_inv _ hu, kappa_one]

/-- Cayley-Hamilton for `M(x)`. -/
theorem hermOfVec_mul_self (x : Fin 4 → ℝ) :
    hermOfVec x * hermOfVec x = (2 * (x 0 : ℂ)) • hermOfVec x - ((minkowskiSq x : ℝ) : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermOfVec, Matrix.mul_apply, Fin.sum_univ_two, minkowskiSq, minkowskiInner,
      Complex.ext_iff] <;> constructor <;> ring

theorem hermOfVec_smul (c : ℝ) (x : Fin 4 → ℝ) :
    hermOfVec (c • x) = (c : ℂ) • hermOfVec x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOfVec] <;> ring

theorem mem_massShell_pos {m : ℝ} (hm : 0 < m) {p : Fin 4 → ℝ} (hp : p ∈ massShell m) :
    0 < p 0 := by
  obtain ⟨h1, h2⟩ := hp
  simp only [minkowskiSq, minkowskiInner] at h1
  rcases h2.lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h] at h1
    nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]

theorem pureBoost_mul_self {m : ℝ} (hm : 0 < m) {p : Fin 4 → ℝ} (hp : p ∈ massShell m) :
    pureBoost m p * pureBoost m p = (m : ℂ)⁻¹ • hermOfVec p := by
  have hp0 := mem_massShell_pos hm hp
  set u : Fin 4 → ℝ := m⁻¹ • p with hu
  have hMu : (m : ℂ)⁻¹ • hermOfVec p = hermOfVec u := by
    rw [hu, hermOfVec_smul]; push_cast; rfl
  have hSq : minkowskiSq u = 1 := by
    have h1 := hp.1
    simp only [minkowskiSq, minkowskiInner, hu, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    field_simp
    linarith
  have hu0 : u 0 = p 0 / m := by
    simp [hu, div_eq_inv_mul]
  set s : ℝ := Real.sqrt (2 + 2 * p 0 / m) with hs
  have hs2 : s ^ 2 = 2 + 2 * p 0 / m := Real.sq_sqrt (by positivity)
  have hs0 : s ≠ 0 := by
    intro h0; rw [h0] at hs2; have : 0 < 2 * p 0 / m := by positivity
    norm_num at hs2; linarith
  have hX : (hermOfVec u + 1) * (hermOfVec u + 1) = ((s ^ 2 : ℝ) : ℂ) • hermOfVec u := by
    have hCH := hermOfVec_mul_self u
    rw [hSq] at hCH
    have hs2' : s ^ 2 = 2 + 2 * u 0 := by rw [hs2, hu0]; ring
    rw [hs2']
    have e : (hermOfVec u + 1) * (hermOfVec u + 1)
        = hermOfVec u * hermOfVec u + (2 : ℂ) • hermOfVec u + 1 := by
      rw [two_smul]; noncomm_ring
    rw [e, hCH]
    push_cast
    module
  unfold pureBoost
  rw [hMu, ← hs, smul_mul_smul_comm, hX, smul_smul]
  have : ((s : ℂ))⁻¹ * (s : ℂ)⁻¹ * ((s ^ 2 : ℝ) : ℂ) = 1 := by
    have : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
    push_cast; field_simp
  rw [this, one_smul]

theorem pureBoost_conjTranspose (m : ℝ) (p : Fin 4 → ℝ) : (pureBoost m p)ᴴ = pureBoost m p := by
  unfold pureBoost
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, hermOfVec_conjTranspose]
  simp

theorem re_diag_mul_conjTranspose_nonneg (D : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    0 ≤ ((D * Dᴴ) i i).re := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  apply Finset.sum_nonneg
  intro k _
  rw [RCLike.star_def, Complex.mul_conj]
  simp [Complex.normSq_nonneg]

theorem kappa_mem_massShell {m : ℝ} (hm : 0 < m) (B : Matrix (Fin 2) (Fin 2) ℂ) (hB : B.det = 1)
    {p : Fin 4 → ℝ} (hp : p ∈ massShell m) : kappa B p ∈ massShell m := by
  refine ⟨by rw [minkowskiSq_kappa B hB]; exact hp.1, ?_⟩
  set V := pureBoost m p
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hM : hermOfVec p = (m : ℂ) • (V * Vᴴ) := by
    rw [pureBoost_conjTranspose, pureBoost_mul_self hm hp, smul_smul, mul_inv_cancel₀ hm',
      one_smul]
  have hH : B * hermOfVec p * Bᴴ = (m : ℂ) • ((B * V) * (B * V)ᴴ) := by
    rw [hM, Matrix.conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
  have key : ∀ i, 0 ≤ ((B * hermOfVec p * Bᴴ) i i).re := by
    intro i
    rw [hH, Matrix.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
    exact mul_nonneg hm.le (re_diag_mul_conjTranspose_nonneg _ i)
  have h0 := key 0
  have h1 := key 1
  show 0 ≤ vecOfHerm (B * hermOfVec p * Bᴴ) 0
  simp only [vecOfHerm, Matrix.cons_val_zero, Complex.div_ofNat_re, Complex.add_re]
  linarith

theorem electronWeight_eq {m : ℝ} (hm : 0 < m) {p : Fin 4 → ℝ} (hp : p ∈ massShell m) :
    electronWeight m p = (m : ℂ) • (hermOfVec p)⁻¹ := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdet : IsUnit (hermOfVec p).det := by
    rw [det_hermOfVec, hp.1]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast (pow_pos hm 2).ne')
  unfold electronWeight
  rw [pureBoost_mul_self hm hp]
  apply Matrix.inv_eq_right_inv
  rw [smul_mul_smul_comm, Matrix.mul_nonsing_inv _ hdet, inv_mul_cancel₀ hm', one_smul]

theorem conj_electronWeight {m : ℝ} (hm : 0 < m) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1)
    {p : Fin 4 → ℝ} (hp : p ∈ massShell m) :
    Aᴴ * electronWeight m p * A = electronWeight m (kappa A⁻¹ p) := by
  have hu : IsUnit A.det := by rw [hA]; exact isUnit_one
  have hq := kappa_mem_massShell hm A⁻¹ (det_inv_eq_one A hA) hp
  rw [electronWeight_eq hm hq, electronWeight_eq hm hp, hermOfVec_kappa, Matrix.mul_inv_rev,
    Matrix.mul_inv_rev, ← Matrix.conjTranspose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hu,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem electronPairing_eq (m : ℝ) (ψ φ : (Fin 4 → ℝ) → (Fin 2 → ℂ)) (p : Fin 4 → ℝ) :
    electronPairing m ψ φ p = star (ψ p) ⬝ᵥ (electronWeight m p *ᵥ φ p) := by
  simp [electronPairing, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  ring

theorem conj_exp_mul_exp (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (Complex.I * θ)) * Complex.exp (Complex.I * θ) = 1 := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

theorem electronPairing_action {m : ℝ} (hm : 0 < m) (a : Fin 4 → ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) (ψ φ : (Fin 4 → ℝ) → (Fin 2 → ℂ))
    {p : Fin 4 → ℝ} (hp : p ∈ massShell m) :
    electronPairing m (electronAction a A ψ) (electronAction a A φ) p
      = electronPairing m ψ φ (kappa A⁻¹ p) := by
  rw [electronPairing_eq, electronPairing_eq, ← conj_electronWeight hm A hA hp]
  simp only [electronAction]
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, smul_smul,
    Matrix.mul_assoc]
  rw [RCLike.star_def, mul_comm, conj_exp_mul_exp, one_smul]

theorem bosonAction_pairing (a : Fin 4 → ℝ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (ψ φ : (Fin 4 → ℝ) → ℂ) (p : Fin 4 → ℝ) :
    (starRingEnd ℂ) (bosonAction a L ψ p) * bosonAction a L φ p
      = (starRingEnd ℂ) (ψ (L⁻¹ *ᵥ p)) * φ (L⁻¹ *ᵥ p) := by
  simp only [bosonAction, map_mul]
  rw [show ∀ x y z w : ℂ, x * y * (z * w) = (x * z) * (y * w) by intros; ring,
    conj_exp_mul_exp, one_mul]


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


theorem measurableSet_massShell (m : ℝ) : MeasurableSet (massShell m) := by
  have h1 : Measurable (fun p : Fin 4 → ℝ => minkowskiSq p) := by
    have : Continuous (fun p : Fin 4 → ℝ => minkowskiSq p) := by
      unfold minkowskiSq minkowskiInner; fun_prop
    exact this.measurable
  exact (measurableSet_eq_fun h1 measurable_const).inter
    (measurableSet_le measurable_const (measurable_pi_apply 0))

theorem ae_massShell (m : ℝ) : ∀ᵐ p ∂(massShellMeasure m), p ∈ massShell m := by
  unfold massShellMeasure
  exact (ae_map_iff (continuous_massShellEmb m).measurable.aemeasurable
    (measurableSet_massShell m)).mpr (Filter.Eventually.of_forall (massShellEmb_mem m))

/-- `p ↦ N p` as a homeomorphism, for invertible `N`. -/
noncomputable def mulVecHomeomorph (N : Matrix (Fin 4) (Fin 4) ℝ) (hN : IsUnit N.det) :
    (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) where
  toFun p := N *ᵥ p
  invFun p := N⁻¹ *ᵥ p
  left_inv p := by
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hN, Matrix.one_mulVec]
  right_inv p := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hN, Matrix.one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem integral_mulVec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℝ} (hm : 0 < m) {N : Matrix (Fin 4) (Fin 4) ℝ} (hN : IsUnit N.det)
    (hSq : ∀ x, minkowskiSq (N *ᵥ x) = minkowskiSq x)
    (hshell : ∀ p ∈ massShell m, N *ᵥ p ∈ massShell m)
    (hsurj : ∀ p ∈ massShell m, ∃ p' ∈ massShell m, N *ᵥ p' = p) (g : (Fin 4 → ℝ) → E) :
    ∫ p, g (N *ᵥ p) ∂(massShellMeasure m) = ∫ p, g p ∂(massShellMeasure m) := by
  have hmp : MeasurePreserving (fun p => N *ᵥ p) (massShellMeasure m) (massShellMeasure m) :=
    ⟨(Continuous.matrix_mulVec continuous_const continuous_id).measurable,
      massShellMeasure_map hm hSq hshell hsurj⟩
  exact hmp.integral_comp (mulVecHomeomorph N hN).measurableEmbedding g

theorem main (m : ℝ) (hm : 0 < m) (a : Fin 4 → ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : ∀ x : Fin 4 → ℝ, kappa A x = L *ᵥ x) :
    (∀ ψ φ : (Fin 4 → ℝ) → ℂ, MemLp ψ 2 (massShellMeasure m) → MemLp φ 2 (massShellMeasure m) →
        ∫ p, (starRingEnd ℂ) (bosonAction a L ψ p) * bosonAction a L φ p ∂(massShellMeasure m)
          = ∫ p, (starRingEnd ℂ) (ψ p) * φ p ∂(massShellMeasure m)) ∧
      (∀ ψ φ : (Fin 4 → ℝ) → (Fin 2 → ℂ), ψ ∈ ElectronL2 m → φ ∈ ElectronL2 m →
        electronInner m (electronAction a A ψ) (electronAction a A φ) = electronInner m ψ φ) := by
  have hAi : A⁻¹.det = 1 := det_inv_eq_one A hA
  have hLsurj : Function.Surjective L.mulVec := fun y =>
    ⟨kappa A⁻¹ y, by rw [← hL, kappa_kappa_inv A hA]⟩
  have hLdet : IsUnit L.det :=
    (Matrix.isUnit_iff_isUnit_det L).mp (Matrix.mulVec_surjective_iff_isUnit.mp hLsurj)
  have hLinv : ∀ x, L⁻¹ *ᵥ x = kappa A⁻¹ x := by
    intro x
    conv_lhs => rw [← kappa_kappa_inv A hA x, hL]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hLdet, Matrix.one_mulVec]
  have hSq : ∀ x, minkowskiSq (L⁻¹ *ᵥ x) = minkowskiSq x := fun x => by
    rw [hLinv, minkowskiSq_kappa _ hAi]
  have hshell : ∀ p ∈ massShell m, L⁻¹ *ᵥ p ∈ massShell m := fun p hp => by
    rw [hLinv]; exact kappa_mem_massShell hm _ hAi hp
  have hsurj : ∀ p ∈ massShell m, ∃ p' ∈ massShell m, L⁻¹ *ᵥ p' = p := fun p hp =>
    ⟨L *ᵥ p, by rw [← hL]; exact kappa_mem_massShell hm A hA hp,
      by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hLdet, Matrix.one_mulVec]⟩
  have hLi : IsUnit (L⁻¹).det := Matrix.isUnit_nonsing_inv_det L hLdet
  refine ⟨fun ψ φ _ _ => ?_, fun ψ φ _ _ => ?_⟩
  · simp_rw [bosonAction_pairing]
    exact integral_mulVec hm hLi hSq hshell hsurj (fun y => (starRingEnd ℂ) (ψ y) * φ y)
  · unfold electronInner
    have hae : (fun p => electronPairing m (electronAction a A ψ) (electronAction a A φ) p)
        =ᵐ[massShellMeasure m] fun p => electronPairing m ψ φ (L⁻¹ *ᵥ p) :=
      (ae_massShell m).mono fun p hp => by
        dsimp only
        rw [electronPairing_action hm a A hA ψ φ hp, hLinv]
    rw [integral_congr_ae hae]
    exact integral_mulVec hm hLi hSq hshell hsurj (electronPairing m ψ φ)

end ChatterjeeQFTBuild

set_option maxHeartbeats 4000000 in
open MeasureTheory Matrix ChatterjeeQFT in
theorem solution (m : ℝ) (hm : 0 < m) (a : Fin 4 → ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : ∀ x : Fin 4 → ℝ, kappa A x = L *ᵥ x) :
    (∀ ψ φ : (Fin 4 → ℝ) → ℂ, MemLp ψ 2 (massShellMeasure m) → MemLp φ 2 (massShellMeasure m) →
        ∫ p, (starRingEnd ℂ) (bosonAction a L ψ p) * bosonAction a L φ p ∂(massShellMeasure m)
          = ∫ p, (starRingEnd ℂ) (ψ p) * φ p ∂(massShellMeasure m)) ∧
      (∀ ψ φ : (Fin 4 → ℝ) → (Fin 2 → ℂ), ψ ∈ ElectronL2 m → φ ∈ ElectronL2 m →
        electronInner m (electronAction a A ψ) (electronAction a A φ) = electronInner m ψ φ) := by
  exact ChatterjeeQFTBuild.main m hm a A hA L hL
