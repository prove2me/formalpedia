-- Prove2me | solution 1 for ChandrasekaranNullCone.boost_distance_D23
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-26T14:54:20.50873+00:00
-- url     : https://prove2.me/submissions/9dab394b-791f-4917-beb8-c2ce714eacde

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Proof of (D.23), Chandrasekaran arXiv:2611.34924, finite-dimensional matrix model

Strategy.
1. `Ψ` is the vectorization of the matrix `X = r⁻¹ • (C * P)`, `r = √Z`, and
   `(1 ⊗ₖ M) *ᵥ vec X = vec (X * Mᵀ)`; with `ŝ* = ŝᵀ` (Hermiticity) the boost on the
   conjugate copy is `Uᵀ = V := exp(iα(ŝ - s₀))`, so the boosted difference is
   `Y = r⁻¹ • (C * P * (V - 1))`.
2. `‖Y‖²_F = Tr(Yᴴ Y) = Z⁻¹ Tr(Q (V-1)(V-1)ᴴ)` with `Q = (CP)ᴴ(CP) = P Cᴴ C P` and
   `Z = Tr(P Cᴴ C) = Tr Q ≥ 0` (orthonormality gives `P² = P`).
3. Spectral theorem `ŝ = W diag(λ) Wᴴ`: `(V-1)(V-1)ᴴ = W diag |e^{iα(λ-s₀)} - 1|² Wᴴ` and
   `(ŝ - s₀)² = W diag (λ - s₀)² Wᴴ`; conclude from `|e^{ix} - 1| ≤ |x|` and the
   nonnegativity of the diagonal of `Wᴴ Q W`.
-/

open Matrix Kronecker Finset

namespace ChandrasekaranNullCone.D23

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `W diag(a) Wᴴ`. -/
noncomputable def udu (W : Matrix n n ℂ) (a : n → ℂ) : Matrix n n ℂ :=
  W * diagonal a * Wᴴ

lemma udu_mul {W : Matrix n n ℂ} (hW : Wᴴ * W = 1) (a b : n → ℂ) :
    udu W a * udu W b = udu W (a * b) := by
  simp only [udu]
  calc W * diagonal a * Wᴴ * (W * diagonal b * Wᴴ)
      = W * diagonal a * (Wᴴ * W) * diagonal b * Wᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hW, Matrix.mul_one, Matrix.mul_assoc W, diagonal_mul_diagonal]; rfl

lemma udu_conjTranspose (W : Matrix n n ℂ) (a : n → ℂ) :
    (udu W a)ᴴ = udu W (star a) := by
  simp only [udu, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
    Matrix.mul_assoc]

lemma udu_const {W : Matrix n n ℂ} (hW : W * Wᴴ = 1) (z : ℂ) :
    udu W (fun _ => z) = z • (1 : Matrix n n ℂ) := by
  have : diagonal (fun _ : n => z) = z • (1 : Matrix n n ℂ) := by
    ext i j; simp [diagonal_apply, one_apply]
  rw [udu, this, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hW]

lemma udu_sub (W : Matrix n n ℂ) (a b : n → ℂ) : udu W a - udu W b = udu W (a - b) := by
  have : diagonal (a - b) = diagonal a - diagonal b := by
    ext i j; by_cases hij : i = j <;> simp [diagonal_apply, hij]
  rw [udu, udu, udu, this, Matrix.mul_sub, Matrix.sub_mul]

lemma udu_smul (W : Matrix n n ℂ) (c : ℂ) (a : n → ℂ) : c • udu W a = udu W (c • a) := by
  have : diagonal (c • a) = c • diagonal a := by
    ext i j; by_cases hij : i = j <;> simp [diagonal_apply, hij]
  rw [udu, udu, this, Matrix.mul_smul, Matrix.smul_mul]

lemma exp_udu {W : Matrix n n ℂ} (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) (a : n → ℂ) :
    NormedSpace.exp (udu W a) = udu W (fun k => Complex.exp (a k)) := by
  let u : (Matrix n n ℂ)ˣ := ⟨W, Wᴴ, hW2, hW1⟩
  have h := Matrix.exp_units_conj u (diagonal a)
  simp only [u, Units.inv_mk, Units.val_mk] at h
  have hexp : NormedSpace.exp a = fun k => Complex.exp (a k) := by
    funext k; rw [Complex.exp_eq_exp_ℂ]; exact Pi.coe_exp a k
  rw [udu, h, Matrix.exp_diagonal, udu, hexp]

omit [DecidableEq n] in
/-- Diagonal entries of a Gram matrix. -/
lemma gram_diag (B : Matrix n n ℂ) (k : n) :
    (Bᴴ * B) k k = ((∑ a, ‖B a k‖ ^ 2 : ℝ) : ℂ) := by
  simp only [mul_apply, conjTranspose_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine sum_congr rfl fun a _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

lemma trace_mul_udu (Q W : Matrix n n ℂ) (d : n → ℂ) :
    (Q * udu W d).trace = ∑ k, (Wᴴ * Q * W) k k * d k := by
  rw [udu, show Q * (W * diagonal d * Wᴴ) = (Q * W * diagonal d) * Wᴴ by
      simp only [Matrix.mul_assoc], trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  simp only [trace, diag_apply, mul_diagonal]

/-- Monotonicity of `d ↦ re Tr(Bᴴ B · W diag(d) Wᴴ)` for real diagonals. -/
lemma re_trace_gram_udu_le (B W : Matrix n n ℂ) {g h : n → ℝ} {κ : ℝ}
    (hgh : ∀ k, g k ≤ κ * h k) :
    (Bᴴ * B * udu W (fun k => (g k : ℂ))).trace.re
      ≤ κ * (Bᴴ * B * udu W (fun k => (h k : ℂ))).trace.re := by
  have hq : ∀ k, (Wᴴ * (Bᴴ * B) * W) k k = ((∑ a, ‖(B * W) a k‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [← gram_diag, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  simp only [trace_mul_udu, hq, ← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re,
    mul_sum]
  refine sum_le_sum fun k _ => ?_
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hgh k) (sum_nonneg fun a _ => by positivity)

/-- `(1 ⊗ₖ M) *ᵥ Ψ` acts on the second (conjugate-copy) index. -/
lemma one_kronecker_mulVec (M : Matrix n n ℂ) (Ψ : n × n → ℂ) (a b : n) :
    (((1 : Matrix n n ℂ) ⊗ₖ M) *ᵥ Ψ) (a, b) = ∑ c, M b c * Ψ (a, c) := by
  simp only [mulVec, dotProduct, kronecker_apply, Fintype.sum_prod_type, one_apply, ite_mul,
    one_mul, zero_mul, mul_assoc]
  rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp

lemma one_mulVec_apply (Ψ : n × n → ℂ) (ab : n × n) : ((1 : Matrix (n × n) (n × n) ℂ) *ᵥ Ψ) ab = Ψ ab := by
  rw [Matrix.one_mulVec]

end ChandrasekaranNullCone.D23

open ChandrasekaranNullCone.D23 in
theorem solution {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
    (C s : Matrix n n ℂ) (hs : s.IsHermitian)
    (v : ι → n → ℂ) (hv : ∀ i j, star (v i) ⬝ᵥ v j = if i = j then 1 else 0)
    (s₀ η : ℝ) :
    let P : Matrix n n ℂ := ∑ i, vecMulVec (v i) (star (v i))
    let Z : ℂ := (P * Cᴴ * C).trace
    let ρ : Matrix n n ℂ := Z⁻¹ • (P * Cᴴ * C * P)
    let Ψ : n × n → ℂ := fun ab =>
      (∑ i, (C *ᵥ v i) ab.1 * star (v i ab.2)) / ((Real.sqrt Z.re : ℝ) : ℂ)
    let sStar : Matrix n n ℂ := s.map star
    let U : Matrix n n ℂ :=
      NormedSpace.exp ((Complex.I * ((η / (2 * Real.pi) : ℝ) : ℂ)) • (sStar - (s₀ : ℂ) • 1))
    ∑ ab, ‖(((1 : Matrix n n ℂ) ⊗ₖ U - 1) *ᵥ Ψ) ab‖ ^ 2
      ≤ η ^ 2 / (4 * Real.pi ^ 2) * (ρ * (s - (s₀ : ℂ) • 1) ^ 2).trace.re := by
  intro P Z ρ Ψ sStar U
  set α : ℝ := η / (2 * Real.pi) with hα
  set c : ℂ := Complex.I * (α : ℂ) with hc
  -- the projection
  let Vm : Matrix n ι ℂ := Matrix.of fun a i => v i a
  have hP : P = Vm * Vmᴴ := by
    ext a b
    show (∑ i, vecMulVec (v i) (star (v i))) a b = _
    rw [Matrix.sum_apply]
    simp [Vm, mul_apply, vecMulVec_apply, conjTranspose_apply, Complex.star_def]
  have hVV : Vmᴴ * Vm = 1 := by
    ext i j
    rw [one_apply, ← hv i j]
    simp [Vm, mul_apply, dotProduct, conjTranspose_apply]
  have hPh : Pᴴ = P := by rw [hP, conjTranspose_mul, conjTranspose_conjTranspose]
  have hPP : P * P = P := by
    rw [hP, show Vm * Vmᴴ * (Vm * Vmᴴ) = Vm * (Vmᴴ * Vm) * Vmᴴ by simp only [Matrix.mul_assoc],
      hVV, Matrix.mul_one]
  -- Gram data
  set B : Matrix n n ℂ := C * P with hB
  have hQ : Bᴴ * B = P * Cᴴ * C * P := by
    rw [hB, conjTranspose_mul, hPh]; simp only [Matrix.mul_assoc]
  set zr : ℝ := ∑ k, ∑ a, ‖B a k‖ ^ 2 with hzr
  have hzr0 : 0 ≤ zr := sum_nonneg fun k _ => sum_nonneg fun a _ => by positivity
  have hZ : Z = (zr : ℂ) := by
    have : Z = (Bᴴ * B).trace := by
      rw [hQ]
      change (P * Cᴴ * C).trace = _
      rw [trace_mul_comm (P * Cᴴ * C) P]
      simp only [← Matrix.mul_assoc, hPP]
    rw [this, trace]
    simp only [diag_apply, gram_diag, hzr, Complex.ofReal_sum]
  -- spectral data
  set W : Matrix n n ℂ := (hs.eigenvectorUnitary : Matrix n n ℂ) with hWdef
  have hW1 : Wᴴ * W = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem hs.eigenvectorUnitary.2
  have hW2 : W * Wᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hs.eigenvectorUnitary.2
  set lam : n → ℝ := hs.eigenvalues with hlam
  have hspec : s = udu W (fun k => (lam k : ℂ)) := by
    conv_lhs => rw [hs.spectral_theorem]
    simp [udu, W, lam, Matrix.star_eq_conjTranspose, Function.comp_def]
  have hss : s - (s₀ : ℂ) • 1 = udu W (fun k => ((lam k - s₀ : ℝ) : ℂ)) := by
    rw [hspec, ← udu_const hW2, udu_sub]; congr 1; funext k; simp
  -- the boost
  set V : Matrix n n ℂ := NormedSpace.exp (c • (s - (s₀ : ℂ) • 1)) with hV
  have hsStar : sStar = sᵀ := by
    ext a b
    have := congrFun (congrFun hs b) a
    simp only [conjTranspose_apply] at this
    simp [sStar, transpose_apply, ← this]
  have hU : U = Vᵀ := by
    change NormedSpace.exp (c • (sStar - (s₀ : ℂ) • 1)) = _
    rw [hV, ← Matrix.exp_transpose, hsStar, transpose_smul, transpose_sub, transpose_smul,
      transpose_one]
  set e : n → ℂ := fun k => Complex.exp (c * ((lam k - s₀ : ℝ) : ℂ)) with he
  have hVe : V = udu W e := by
    rw [hV, hss, udu_smul, exp_udu hW1 hW2]; rfl
  -- the boosted difference as a matrix
  set r : ℂ := ((Real.sqrt Z.re : ℝ) : ℂ) with hr
  set Y : Matrix n n ℂ := r⁻¹ • (B * (V - 1)) with hY
  have hΨ : ∀ a c', Ψ (a, c') = (r⁻¹ • B) a c' := by
    intro a c'
    simp only [Ψ, hB, hP, Matrix.smul_apply, smul_eq_mul, mul_apply, Vm, conjTranspose_apply, of_apply,
      mulVec, dotProduct, sum_mul, mul_sum, div_eq_inv_mul]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun a' _ => ?_
    ring
  have hw : ∀ a b, (((1 : Matrix n n ℂ) ⊗ₖ U - 1) *ᵥ Ψ) (a, b) = Y a b := by
    intro a b
    rw [sub_mulVec, Pi.sub_apply, one_kronecker_mulVec, one_mulVec_apply, hU]
    simp only [hY, Matrix.smul_apply, smul_eq_mul, mul_apply, Matrix.sub_apply, transpose_apply, hΨ,
      mul_sub, sum_sub_distrib, one_apply, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ,
      if_true, mul_sum]
    congr 1
    · refine sum_congr rfl fun c' _ => ?_; ring
  -- LHS = Re Tr(Yᴴ Y)
  have hLHS : ∑ ab, ‖(((1 : Matrix n n ℂ) ⊗ₖ U - 1) *ᵥ Ψ) ab‖ ^ 2 = (Yᴴ * Y).trace.re := by
    rw [Fintype.sum_prod_type, trace]
    simp only [hw, diag_apply, gram_diag, ← Complex.ofReal_sum, Complex.ofReal_re]
    exact sum_comm
  have hrr : star r⁻¹ * r⁻¹ = ((zr⁻¹ : ℝ) : ℂ) := by
    rw [hr, hZ, Complex.ofReal_re, star_inv₀, Complex.star_def, Complex.conj_ofReal,
      ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hzr0]
    push_cast; rfl
  have hYY : (Yᴴ * Y).trace
      = ((zr⁻¹ : ℝ) : ℂ) * (Bᴴ * B * ((V - 1) * (V - 1)ᴴ)).trace := by
    rw [hY, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, trace_smul, hrr,
      smul_eq_mul, conjTranspose_mul,
      show (V - 1)ᴴ * Bᴴ * (B * (V - 1)) = (V - 1)ᴴ * (Bᴴ * B * (V - 1)) by
        simp only [Matrix.mul_assoc],
      trace_mul_comm, Matrix.mul_assoc (Bᴴ * B)]
  -- spectral forms
  set g : n → ℝ := fun k => ‖e k - 1‖ ^ 2 with hg
  set h : n → ℝ := fun k => (lam k - s₀) ^ 2 with hh
  have hG : (V - 1) * (V - 1)ᴴ = udu W (fun k => (g k : ℂ)) := by
    rw [hVe, show (1 : Matrix n n ℂ) = udu W (fun _ => 1) by rw [udu_const hW2, one_smul],
      udu_sub, udu_conjTranspose, udu_mul hW1]
    congr 1; funext k
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.star_apply, hg, Complex.star_def]
    rw [Complex.mul_conj']; push_cast; rfl
  have hH : (s - (s₀ : ℂ) • 1) ^ 2 = udu W (fun k => (h k : ℂ)) := by
    rw [sq, hss, udu_mul hW1]; congr 1; funext k; simp [hh]; ring
  have hgh : ∀ k, g k ≤ (η ^ 2 / (4 * Real.pi ^ 2)) * h k := by
    intro k
    have hx : c * ((lam k - s₀ : ℝ) : ℂ) = Complex.I * ((α * (lam k - s₀) : ℝ) : ℂ) := by
      rw [hc]; push_cast; ring
    have h1 : ‖e k - 1‖ ≤ |α * (lam k - s₀)| := by
      simp only [he, hx]
      exact Real.norm_exp_I_mul_ofReal_sub_one_le
    have h2 : g k ≤ (α * (lam k - s₀)) ^ 2 := by
      simp only [hg]
      rw [← sq_abs (α * _)]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc g k ≤ (α * (lam k - s₀)) ^ 2 := h2
      _ = _ := by rw [hα, hh]; field_simp; ring
  -- RHS
  have hRHS : (ρ * (s - (s₀ : ℂ) • 1) ^ 2).trace.re
      = zr⁻¹ * (Bᴴ * B * udu W (fun k => (h k : ℂ))).trace.re := by
    change ((Z⁻¹ • (P * Cᴴ * C * P)) * _).trace.re = _
    rw [Matrix.smul_mul, trace_smul, hZ, hH, ← hQ, smul_eq_mul, ← Complex.ofReal_inv,
      Complex.re_ofReal_mul]
  rw [hLHS, hYY, hG, Complex.re_ofReal_mul, hRHS, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (re_trace_gram_udu_le B W hgh) (inv_nonneg.2 hzr0)
