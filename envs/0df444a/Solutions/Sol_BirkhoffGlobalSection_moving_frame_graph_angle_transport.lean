-- Prove2me | solution 1 for BirkhoffGlobalSection.moving_frame_graph_angle_transport
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T17:03:44.307997+00:00
-- url     : https://prove2.me/submissions/44fd494a-c77e-46f7-8b7a-93056b2f5597

import Definitions.Def_BirkhoffGlobalSection_MovingFrameAlgebra
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

-- Generic algebra adapted from Mazecto, accepted submission
-- 893234ef-5ec2-4f4b-b415-f79ec1030002, with attribution.
open HryniewiczCriterion Matrix Complex
namespace HryniewiczCriterion
noncomputable section
lemma transpose_omega_mul_apply (F : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    (F.transpose * omegaMat * F) i j = omega0 (fun k => F k i) (fun k => F k j) := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, omegaMat, omega0]; ring


lemma cA_mul (g h : Matrix (Fin 4) (Fin 4) ℝ) : cA (g * h) = cA g * cA h + cC g * cCb h := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [cA, cC, cCb, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, Complex.ext_iff] <;>
    constructor <;> ring


lemma cA_one : cA 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cA, Complex.ext_iff, Matrix.one_apply]


lemma cC_one : cC 1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cC, Complex.ext_iff, Matrix.one_apply]


lemma cdet_one : cdet 1 = 1 := by simp [cdet, cA_one]


lemma graphBasis4_eq (g : Matrix (Fin 4) (Fin 4) ℝ) : graphBasis4 g =
    !![1, -I, 0, 0; 0, 0, 1, -I;
      (g 0 0 : ℂ) + I * g 1 0, (g 0 1 : ℂ) + I * g 1 1, (g 0 2 : ℂ) + I * g 1 2, (g 0 3 : ℂ) + I * g 1 3;
      (g 2 0 : ℂ) + I * g 3 0, (g 2 1 : ℂ) + I * g 3 1, (g 2 2 : ℂ) + I * g 3 2, (g 2 3 : ℂ) + I * g 3 3] := by
  ext r k; fin_cases r <;> fin_cases k <;> simp [graphBasis4, Matrix.one_apply]


lemma det_graphBasis4 (g : Matrix (Fin 4) (Fin 4) ℝ) : (graphBasis4 g).det = 4 * cdet g := by
  rw [graphBasis4_eq, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three]
  simp [Matrix.submatrix_apply, Fin.succAbove, Fin.lt_def, cdet, cA, Matrix.det_fin_two]
  apply Complex.ext <;> simp <;> ring

end

end HryniewiczCriterion

/-!
# Leaf D, algebra II: `det graphUnitary4 = d / d̄` and the slit-plane factorization

For `g₁ Ω g₁ᵀ = Ω` and `g₂ᵀ Ω g₂ = Ω`, `d(g₁ g₂) / (d(g₁) d(g₂)) = det (1 + X Y)` with
`X = A₁⁻¹ C₁` a weak and `Y = C̄₂ A₂⁻¹` a strict contraction, so it lies in the slit plane.
-/

namespace HryniewiczCriterion

open Matrix Complex

noncomputable section


lemma det_lagUnitary {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.det ≠ 0) :
    (lagUnitary A).det = A.det / star A.det := by
  have hs : star A.det ≠ 0 := star_ne_zero.mpr hA
  unfold lagUnitary
  rw [det_mul, det_mul, det_nonsing_inv, det_mul, det_conjTranspose, det_transpose,
    Ring.inverse_eq_inv']
  field_simp


lemma det_graphUnitary4 {g : Matrix (Fin 4) (Fin 4) ℝ} (h : cdet g ≠ 0) :
    (graphUnitary4 g).det = cdet g / star (cdet g) := by
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  have hg : (graphBasis4 g).det ≠ 0 := by rw [det_graphBasis4]; exact mul_ne_zero h4 h
  have h1 : (graphBasis4 1).det ≠ 0 := by rw [det_graphBasis4, cdet_one]; norm_num
  have hs : star (cdet g) ≠ 0 := star_ne_zero.mpr h
  unfold graphUnitary4
  rw [det_mul, det_nonsing_inv, det_lagUnitary hg, det_lagUnitary h1, det_graphBasis4,
    det_graphBasis4, cdet_one, Ring.inverse_eq_inv']
  simp only [star_mul', mul_one]
  have : star (4 : ℂ) = 4 := by simp
  rw [this]
  field_simp

/-! ### Symplectic matrices -/


lemma omegaMat_mul_self : omegaMat * omegaMat = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [omegaMat, Matrix.mul_apply, Fin.sum_univ_four]


lemma sp_mul_transpose {g : Matrix (Fin 4) (Fin 4) ℝ} (h : g.transpose * omegaMat * g = omegaMat) :
    g * omegaMat * g.transpose = omegaMat := by
  have h1 : (-(omegaMat * g.transpose * omegaMat)) * g = 1 := by
    have : (-(omegaMat * g.transpose * omegaMat)) * g =
        -(omegaMat * (g.transpose * omegaMat * g)) := by
      simp only [Matrix.neg_mul, Matrix.mul_assoc]
    rw [this, h, omegaMat_mul_self, neg_neg]
  have h2 := mul_eq_one_comm.1 h1
  have : (g * (-(omegaMat * g.transpose * omegaMat))) * omegaMat = g * omegaMat * g.transpose := by
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, omegaMat_mul_self, Matrix.mul_one,
      neg_neg]
  rw [← this, h2, Matrix.one_mul]


lemma sp_transpose_of {g : Matrix (Fin 4) (Fin 4) ℝ} (h : g * omegaMat * g.transpose = omegaMat) :
    g.transpose * omegaMat * g = omegaMat := by
  have := sp_mul_transpose (g := g.transpose) (by rwa [Matrix.transpose_transpose])
  rwa [Matrix.transpose_transpose] at this


lemma sp_mul {g h : Matrix (Fin 4) (Fin 4) ℝ} (hg : g.transpose * omegaMat * g = omegaMat)
    (hh : h.transpose * omegaMat * h = omegaMat) :
    (g * h).transpose * omegaMat * (g * h) = omegaMat := by
  rw [Matrix.transpose_mul]
  calc h.transpose * g.transpose * omegaMat * (g * h)
      = h.transpose * (g.transpose * omegaMat * g) * h := by simp only [Matrix.mul_assoc]
    _ = omegaMat := by rw [hg, hh]


lemma sp_id1 {g : Matrix (Fin 4) (Fin 4) ℝ} (h : g.transpose * omegaMat * g = omegaMat) :
    (cA g)ᴴ * cA g = 1 + (cCb g)ᴴ * cCb g := by
  have e : ∀ a b, omega0 (fun k => g k a) (fun k => g k b) = omegaMat a b := fun a b => by
    rw [← transpose_omega_mul_apply, h]
  have h01 := e 0 1; have h02 := e 0 2; have h03 := e 0 3
  have h12 := e 1 2; have h13 := e 1 3; have h23 := e 2 3
  simp only [omega0] at h01 h02 h03 h12 h13 h23
  simp [omegaMat] at h01 h02 h03 h12 h13 h23
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [cA, cCb, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff, Matrix.one_apply] <;>
    (try constructor) <;>
    first
      | ring1
      | linear_combination h01 | linear_combination -h01
      | linear_combination h23 | linear_combination -h23
      | linear_combination (1/2) * h03 - (1/2) * h12 | linear_combination -(1/2) * h03 + (1/2) * h12
      | linear_combination (1/2) * h02 + (1/2) * h13 | linear_combination -(1/2) * h02 - (1/2) * h13


lemma sp_id2 {g : Matrix (Fin 4) (Fin 4) ℝ} (h : g * omegaMat * g.transpose = omegaMat) :
    cA g * (cA g)ᴴ = 1 + cC g * (cC g)ᴴ := by
  have e : ∀ a b, omega0 (fun k => g a k) (fun k => g b k) = omegaMat a b := fun a b => by
    have := transpose_omega_mul_apply g.transpose a b
    rw [Matrix.transpose_transpose, h] at this
    rw [this]; rfl
  have h01 := e 0 1; have h02 := e 0 2; have h03 := e 0 3
  have h12 := e 1 2; have h13 := e 1 3; have h23 := e 2 3
  simp only [omega0] at h01 h02 h03 h12 h13 h23
  simp [omegaMat] at h01 h02 h03 h12 h13 h23
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [cA, cC, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Complex.ext_iff, Matrix.one_apply] <;>
    (try constructor) <;>
    first
      | ring1
      | linear_combination h01 | linear_combination -h01
      | linear_combination h23 | linear_combination -h23
      | linear_combination (1/2) * h03 - (1/2) * h12 | linear_combination -(1/2) * h03 + (1/2) * h12
      | linear_combination (1/2) * h02 + (1/2) * h13 | linear_combination -(1/2) * h02 - (1/2) * h13

/-! ### Contractions on `ℂ²` -/

/-- The squared Hermitian norm on `ℂ²`. -/

lemma nsq_nonneg (v : Fin 2 → ℂ) : 0 ≤ nsq v := add_nonneg (normSq_nonneg _) (normSq_nonneg _)


lemma nsq_pos {v : Fin 2 → ℂ} (hv : v ≠ 0) : 0 < nsq v := by
  rcases (nsq_nonneg v).lt_or_eq with h | h
  · exact h
  · exfalso; apply hv
    have h0 : normSq (v 0) = 0 := by
      have := normSq_nonneg (v 0); have := normSq_nonneg (v 1); unfold nsq at h; linarith
    have h1 : normSq (v 1) = 0 := by
      have := normSq_nonneg (v 0); have := normSq_nonneg (v 1); unfold nsq at h; linarith
    ext i; fin_cases i
    · simpa using h0
    · simpa using h1


lemma star_dotProduct_self (v : Fin 2 → ℂ) : star v ⬝ᵥ v = (nsq v : ℂ) := by
  simp [dotProduct, Fin.sum_univ_two, nsq, normSq_eq_conj_mul_self]


lemma star_mulVec_dotProduct (M N : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    star (M *ᵥ v) ⬝ᵥ (N *ᵥ v) = star v ⬝ᵥ ((Mᴴ * N) *ᵥ v) := by
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec]


lemma nsq_mulVec_of {M N : Matrix (Fin 2) (Fin 2) ℂ} (h : Mᴴ * M = 1 + Nᴴ * N) (v : Fin 2 → ℂ) :
    nsq (M *ᵥ v) = nsq v + nsq (N *ᵥ v) := by
  have e := star_mulVec_dotProduct M M v
  rw [h, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, ← star_mulVec_dotProduct N N v,
    star_dotProduct_self, star_dotProduct_self, star_dotProduct_self] at e
  exact_mod_cast e


lemma det_ne_zero_of_id {M N : Matrix (Fin 2) (Fin 2) ℂ} (h : Mᴴ * M = 1 + Nᴴ * N) : M.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have e := nsq_mulVec_of h v
  rw [hMv] at e
  have h0 : nsq (0 : Fin 2 → ℂ) = 0 := by simp [nsq]
  have := nsq_pos hv; have := nsq_nonneg (N *ᵥ v); linarith


lemma nsq_bound_eq {M N : Matrix (Fin 2) (Fin 2) ℂ} (h : Mᴴ * M = 1 + Nᴴ * N) (v : Fin 2 → ℂ) :
    nsq ((N * M⁻¹) *ᵥ v) + nsq (M⁻¹ *ᵥ v) = nsq v := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.2 (det_ne_zero_of_id h)
  have hz : M *ᵥ (M⁻¹ *ᵥ v) = v := by rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have e := nsq_mulVec_of h (M⁻¹ *ᵥ v)
  rw [hz] at e
  rw [← mulVec_mulVec]
  linarith


lemma normSq_dotProduct_le (a b : Fin 2 → ℂ) : normSq (star a ⬝ᵥ b) ≤ nsq a * nsq b := by
  have key : nsq a * nsq b - normSq (star a ⬝ᵥ b) = normSq (a 0 * b 1 - a 1 * b 0) := by
    simp [nsq, dotProduct, Fin.sum_univ_two, normSq_apply]; ring
  have := normSq_nonneg (a 0 * b 1 - a 1 * b 0); linarith

/-- `X = A⁻¹ C` is a weak contraction when `A Aᴴ = 1 + C Cᴴ`. -/

lemma weak_contraction {A C : Matrix (Fin 2) (Fin 2) ℂ} (h : A * Aᴴ = 1 + C * Cᴴ)
    (v : Fin 2 → ℂ) : nsq ((A⁻¹ * C) *ᵥ v) ≤ nsq v := by
  have h' : (Aᴴ)ᴴ * Aᴴ = 1 + (Cᴴ)ᴴ * Cᴴ := by simpa using h
  set X := A⁻¹ * C
  have hXH : Xᴴ = Cᴴ * (Aᴴ)⁻¹ := by
    simp only [X, conjTranspose_mul, conjTranspose_nonsing_inv]
  have hstar : ∀ u, nsq (Xᴴ *ᵥ u) ≤ nsq u := fun u => by
    have := nsq_bound_eq h' u; rw [hXH]; have := nsq_nonneg ((Aᴴ)⁻¹ *ᵥ u); linarith
  clear_value X
  have e := star_mulVec_dotProduct X X v
  rw [star_dotProduct_self, ← mulVec_mulVec] at e
  have hcs := normSq_dotProduct_le v (Xᴴ *ᵥ (X *ᵥ v))
  rw [← e, normSq_ofReal] at hcs
  have h2 := hstar (X *ᵥ v)
  have hp := nsq_nonneg (X *ᵥ v)
  have hv := nsq_nonneg v
  by_contra hlt
  push_neg at hlt
  nlinarith [mul_le_mul_of_nonneg_left h2 hv]

/-- `Y = C̄ A⁻¹` is a strict contraction when `Aᴴ A = 1 + C̄ᴴ C̄`. -/

lemma strict_contraction {A Cb : Matrix (Fin 2) (Fin 2) ℂ} (h : Aᴴ * A = 1 + Cbᴴ * Cb)
    {v : Fin 2 → ℂ} (hv : v ≠ 0) : nsq ((Cb * A⁻¹) *ᵥ v) < nsq v := by
  have e := nsq_bound_eq h v
  have hz : A⁻¹ *ᵥ v ≠ 0 := by
    intro h0
    have hu : IsUnit A.det := isUnit_iff_ne_zero.2 (det_ne_zero_of_id h)
    apply hv
    rw [← one_mulVec v, ← mul_nonsing_inv _ hu, ← mulVec_mulVec, h0, mulVec_zero]
  have := nsq_pos hz
  linarith


lemma mul_mem_slitPlane_of_re_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    a * b ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases him : (a * b).im = 0
  · left
    simp only [mul_im] at him
    simp only [mul_re]
    have h1 : a.re * (a.re * b.re - a.im * b.im) = (a.re ^ 2 + a.im ^ 2) * b.re := by
      linear_combination (-a.im) * him
    have h2 : 0 < (a.re ^ 2 + a.im ^ 2) * b.re := by positivity
    by_contra hle; push_neg at hle
    nlinarith
  · exact Or.inr him

/-- If `X` is a weak and `Y` a strict contraction of `ℂ²`, `det (1 + X Y)` avoids `(-∞, 0]`. -/

lemma det_one_add_mul_mem_slitPlane {X Y : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : ∀ v, nsq (X *ᵥ v) ≤ nsq v) (hY : ∀ v, v ≠ 0 → nsq (Y *ᵥ v) < nsq v) :
    (1 + X * Y).det ∈ slitPlane := by
  set Z := X * Y
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (Z.trace ^ 2 - 4 * Z.det)
  have hev : ∀ μ : ℂ, μ ^ 2 - Z.trace * μ + Z.det = 0 → 0 < (1 + μ).re := by
    intro μ hμ
    have hd : (Z - μ • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 := by
      rw [det_fin_two]; rw [trace_fin_two, det_fin_two] at hμ
      simp [Matrix.one_apply]; linear_combination hμ
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    have hZv : Z *ᵥ v = μ • v := by
      rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hv; exact hv
    have h1 : nsq (Z *ᵥ v) = normSq μ * nsq v := by
      rw [hZv]; simp [nsq, normSq_mul]; ring
    have h2 : nsq (Z *ᵥ v) < nsq v := by
      simp only [Z]; rw [← mulVec_mulVec]; exact (hX _).trans_lt (hY v hv0)
    have hpos := nsq_pos hv0
    have hμ1 : normSq μ < 1 := by
      by_contra hc; push_neg at hc; nlinarith
    have : μ.re ^ 2 ≤ normSq μ := by rw [normSq_apply]; nlinarith [sq_nonneg μ.im]
    simp only [add_re, one_re]
    nlinarith
  set μ₁ := (Z.trace + s) / 2
  set μ₂ := (Z.trace - s) / 2
  have e1 : μ₁ ^ 2 - Z.trace * μ₁ + Z.det = 0 := by simp only [μ₁]; linear_combination (-1/4) * hs
  have e2 : μ₂ ^ 2 - Z.trace * μ₂ + Z.det = 0 := by simp only [μ₂]; linear_combination (-1/4) * hs
  have hdet : (1 + Z).det = (1 + μ₁) * (1 + μ₂) := by
    have : (1 + Z).det = 1 + Z.trace + Z.det := by
      rw [det_fin_two, det_fin_two, trace_fin_two]; simp [Matrix.one_apply]; ring
    rw [this]; simp only [μ₁, μ₂]; linear_combination (-1/4) * hs
  rw [hdet]
  exact mul_mem_slitPlane_of_re_pos (hev _ e1) (hev _ e2)


lemma cdet_ne_zero {g : Matrix (Fin 4) (Fin 4) ℝ} (h : g.transpose * omegaMat * g = omegaMat) :
    cdet g ≠ 0 := det_ne_zero_of_id (sp_id1 h)

/-- The slit-plane factorization: for `g₁ Ω g₁ᵀ = Ω` and `g₂ᵀ Ω g₂ = Ω`,
`d(g₁ g₂) / (d(g₁) d(g₂)) = det (1 + X Y)` lies in the slit plane. -/

lemma cdet_mul_ratio_mem_slitPlane {g₁ g₂ : Matrix (Fin 4) (Fin 4) ℝ}
    (h₁ : g₁ * omegaMat * g₁.transpose = omegaMat) (h₂ : g₂.transpose * omegaMat * g₂ = omegaMat) :
    cdet (g₁ * g₂) / (cdet g₁ * cdet g₂) ∈ slitPlane := by
  have i1 := sp_id2 h₁
  have i2 := sp_id1 h₂
  have hA1 : (cA g₁).det ≠ 0 := by
    have : ((cA g₁)ᴴ)ᴴ * (cA g₁)ᴴ = 1 + ((cC g₁)ᴴ)ᴴ * (cC g₁)ᴴ := by simpa using i1
    have := det_ne_zero_of_id this
    rwa [det_conjTranspose, star_ne_zero] at this
  have hA2 : (cA g₂).det ≠ 0 := det_ne_zero_of_id i2
  have u1 : IsUnit (cA g₁).det := isUnit_iff_ne_zero.2 hA1
  have u2 : IsUnit (cA g₂).det := isUnit_iff_ne_zero.2 hA2
  set X := (cA g₁)⁻¹ * cC g₁
  set Y := cCb g₂ * (cA g₂)⁻¹
  have hfac : cA (g₁ * g₂) = cA g₁ * (1 + X * Y) * cA g₂ := by
    rw [cA_mul]
    simp only [X, Y, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [nonsing_inv_mul _ u2, Matrix.mul_one, ← Matrix.mul_assoc (cA g₁), mul_nonsing_inv _ u1,
      Matrix.one_mul]
  have hr : cdet (g₁ * g₂) / (cdet g₁ * cdet g₂) = (1 + X * Y).det := by
    unfold cdet; rw [hfac, det_mul, det_mul]; field_simp
  rw [hr]
  exact det_one_add_mul_mem_slitPlane (weak_contraction i1) (fun v hv => strict_contraction i2 hv)

end

end HryniewiczCriterion

/-!
# Leaf D, pointwise facts: frame determinant, `blockOne`, polar decomposition

* `i · d(F(y))` has positive real part for the frame `F(y) = homogFrame H y` whenever
  `dH(y) y > 0`: `Re (i d(F)) = |y|⁻¹ (2|y|² + 2⟨y, w⟩ + |D|²) / 4` with `w = ∇H / dH(y)y`.
* `F(y)` is symplectic.
* `d(blockOne m) = c(m) = ((m₀₀ + m₁₁) + i (m₁₀ - m₀₁)) / 2`, and `m = R(α) P` with `P ≻ 0` when
  `c(m) = r e^{iα}`, `r > 0`, `det m = 1`.
-/

namespace HryniewiczCriterion

open Matrix Complex

noncomputable section

variable {H : R4 → ℝ}

/-- The frame with columns `y`, `J w`, `m (Q₂y - ⟨w, Q₂y⟩ y)`, `m (Q₁y - ⟨w, Q₁y⟩ y)`. -/

lemma cdet_blockOne (m : Matrix (Fin 2) (Fin 2) ℝ) : cdet (blockOne m) = polarC m := by
  simp [cdet, cA, blockOne, det_fin_two, polarC, Complex.ext_iff]


lemma blockOne_one : blockOne 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [blockOne, Matrix.one_apply]


lemma blockOne_sp {m : Matrix (Fin 2) (Fin 2) ℝ} (h : m.det = 1) :
    (blockOne m).transpose * omegaMat * blockOne m = omegaMat := by
  rw [det_fin_two] at h
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [blockOne, omegaMat, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first
      | ring1 | linear_combination h | linear_combination -h | linear_combination 2 * h
      | linear_combination -2 * h


lemma one_le_normSq_polarC {m : Matrix (Fin 2) (Fin 2) ℝ} (h : m.det = 1) :
    1 ≤ normSq (polarC m) := by
  rw [det_fin_two] at h
  simp only [polarC, normSq_mk]
  nlinarith [sq_nonneg (m 0 0 - m 1 1), sq_nonneg (m 0 1 + m 1 0)]


lemma polarC_ne_zero {m : Matrix (Fin 2) (Fin 2) ℝ} (h : m.det = 1) : polarC m ≠ 0 := by
  intro h0; have := one_le_normSq_polarC h; rw [h0, map_zero] at this; norm_num at this


lemma rotationMatrix_mul_neg (a : ℝ) : rotationMatrix a * rotationMatrix (-a) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg] <;>
    nlinarith [Real.sin_sq_add_cos_sq a]

/-- Polar decomposition from the angle of `c(m)`. -/

lemma polar_of_polarC {m : Matrix (Fin 2) (Fin 2) ℝ} (hdet : m.det = 1) {α r : ℝ} (hr : 0 < r)
    (hc : polarC m = r * exp (α * I)) :
    ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.PosDef ∧ m = rotationMatrix α * P := by
  refine ⟨rotationMatrix (-α) * m, ?_, ?_⟩
  · have hre : (m 0 0 + m 1 1) / 2 = r * Real.cos α := by
      have := congrArg Complex.re hc
      simpa [polarC, exp_mul_I, ← ofReal_cos, ← ofReal_sin, mul_re] using this
    have him : (m 1 0 - m 0 1) / 2 = r * Real.sin α := by
      have := congrArg Complex.im hc
      simpa [polarC, exp_mul_I, ← ofReal_cos, ← ofReal_sin, mul_im] using this
    rw [det_fin_two] at hdet
    set c := Real.cos α
    set s := Real.sin α
    have hcs : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    set P := rotationMatrix (-α) * m with hP
    have e00 : P 0 0 = c * m 0 0 + s * m 1 0 := by
      simp [hP, rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg, c, s,
        Matrix.vecMul, dotProduct]
    have e01 : P 0 1 = c * m 0 1 + s * m 1 1 := by
      simp [hP, rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg, c, s,
        Matrix.vecMul, dotProduct]
    have e10 : P 1 0 = -s * m 0 0 + c * m 1 0 := by
      simp [hP, rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg, c, s,
        Matrix.vecMul, dotProduct]
    have e11 : P 1 1 = -s * m 0 1 + c * m 1 1 := by
      simp [hP, rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg, c, s,
        Matrix.vecMul, dotProduct]
    have hsym : P 1 0 = P 0 1 := by
      rw [e10, e01]; linear_combination (2 * c) * him - (2 * s) * hre
    have htr : P 0 0 + P 1 1 = 2 * r := by
      rw [e00, e11]; linear_combination (2 * c) * hre + (2 * s) * him + 2 * r * hcs
    have hdP : P 0 0 * P 1 1 - P 0 1 * P 1 0 = 1 := by
      rw [e00, e01, e10, e11]; linear_combination hdet + (m 0 0 * m 1 1 - m 0 1 * m 1 0 - 1) * 0 +
        (m 0 0 * m 1 1 - m 0 1 * m 1 0) * hcs
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [hsym]
    · have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
        by_contra hc; push_neg at hc; apply hv; ext i; fin_cases i <;> simp [hc.1, hc.2]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, star_trivial]
      rw [hsym]
      rw [hsym] at hdP
      have ha : 0 < P 0 0 := by
        by_contra hc; push_neg at hc
        nlinarith [sq_nonneg (P 0 1), mul_nonneg (neg_nonneg.2 hc) (sq_nonneg (P 0 1))]
      have hq : P 0 0 * (v 0 * (P 0 0 * v 0 + P 0 1 * v 1) + v 1 * (P 0 1 * v 0 + P 1 1 * v 1)) =
          (P 0 0 * v 0 + P 0 1 * v 1) ^ 2 + (P 0 0 * P 1 1 - P 0 1 * P 0 1) * v 1 ^ 2 := by ring
      have hpos : 0 < (P 0 0 * v 0 + P 0 1 * v 1) ^ 2 + (P 0 0 * P 1 1 - P 0 1 * P 0 1) * v 1 ^ 2 := by
        rcases hv' with h0 | h1
        · by_cases h1 : v 1 = 0
          · rw [h1]
            have hne : P 0 0 * v 0 ≠ 0 := mul_ne_zero ha.ne' h0
            have := pow_pos (abs_pos.2 hne) 2; rw [sq_abs] at this; nlinarith
          · have := pow_pos (abs_pos.2 h1) 2; rw [sq_abs] at this
            nlinarith [sq_nonneg (P 0 0 * v 0 + P 0 1 * v 1)]
        · have := pow_pos (abs_pos.2 h1) 2; rw [sq_abs] at this
          nlinarith [sq_nonneg (P 0 0 * v 0 + P 0 1 * v 1)]
      have := hq ▸ hpos
      exact pos_of_mul_pos_right this ha.le
  · rw [← Matrix.mul_assoc, rotationMatrix_mul_neg, Matrix.one_mul]

end

end HryniewiczCriterion

/-!
# Leaf D, analytic helpers

* `z / z̄ = e^{2 i arg z}`;
* continuity of `cdet` and of `arg` on the slit plane;
* a continuous polar angle of a path in `SL(2, ℝ)` (path lifting through `exp : ℂ → ℂ \ {0}`);
* the frame-flow factorization `Y(t) F(x₀) = F(x(t)) blockOne(φ(t / T))` for every `t`.
-/

namespace HryniewiczCriterion

open Matrix Complex
open scoped ContDiff

noncomputable section

/-! ### `z / z̄` -/


lemma ofReal_mul_exp_div_star (r : ℝ) (hr : r ≠ 0) (a : ℝ) :
    (r * exp (a * I)) / star (r * exp (a * I)) = exp ((2 * a : ℝ) * I) := by
  have hs : star (r * exp (a * I)) = r * exp (-(a * I)) := by
    rw [star_mul', Complex.star_def, conj_ofReal, ← exp_conj, map_mul,
      conj_ofReal, conj_I, mul_neg]
  rw [hs, mul_div_mul_left _ _ (ofReal_ne_zero.2 hr), ← exp_sub]
  congr 1; push_cast; ring


lemma div_star_eq_exp_arg {z : ℂ} (hz : z ≠ 0) :
    z / star z = exp ((2 * arg z : ℝ) * I) := by
  have h := norm_mul_exp_arg_mul_I z
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  conv_lhs => rw [← h]
  exact ofReal_mul_exp_div_star _ hn _


lemma div_star_mul (a b : ℂ) : (a * b) / star (a * b) = (a / star a) * (b / star b) := by
  rw [star_mul', mul_div_mul_comm]


lemma div_star_div (a b : ℂ) : (a / b) / star (a / b) = (a / star a) / (b / star b) := by
  rw [star_div₀, div_div_div_comm]

/-! ### Continuity -/


lemma continuousOn_complex_mk {s : Set ℝ} {a b : ℝ → ℝ} (ha : ContinuousOn a s)
    (hb : ContinuousOn b s) : ContinuousOn (fun t => (⟨a t, b t⟩ : ℂ)) s := by
  have e : (fun t => (⟨a t, b t⟩ : ℂ)) = fun t => (a t : ℂ) + (b t : ℂ) * I :=
    funext fun t => by apply Complex.ext <;> simp
  rw [e]
  exact (continuous_ofReal.comp_continuousOn ha).add
    ((continuous_ofReal.comp_continuousOn hb).mul continuousOn_const)


lemma continuousOn_cdet {s : Set ℝ} {g : ℝ → Matrix (Fin 4) (Fin 4) ℝ}
    (hg : ∀ i j, ContinuousOn (fun t => g t i j) s) : ContinuousOn (fun t => cdet (g t)) s := by
  have hA : ∀ k l, ContinuousOn (fun t => cA (g t) k l) s := by
    intro k l
    fin_cases k <;> fin_cases l <;> simp only [cA] <;> simp <;>
      exact continuousOn_complex_mk
        ((((hg _ _).add (hg _ _)).div_const 2)) (((hg _ _).sub (hg _ _)).div_const 2)
  simp only [cdet, det_fin_two]
  exact ((hA 0 0).mul (hA 1 1)).sub ((hA 0 1).mul (hA 1 0))


lemma continuousOn_mul_entries {s : Set ℝ} {g h : ℝ → Matrix (Fin 4) (Fin 4) ℝ}
    (hg : ∀ i j, ContinuousOn (fun t => g t i j) s) (hh : ∀ i j, ContinuousOn (fun t => h t i j) s)
    (i j : Fin 4) : ContinuousOn (fun t => (g t * h t) i j) s := by
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  exact ((((hg i 0).mul (hh 0 j)).add ((hg i 1).mul (hh 1 j))).add ((hg i 2).mul (hh 2 j))).add
    ((hg i 3).mul (hh 3 j))


lemma continuousOn_arg_comp {s : Set ℝ} {f : ℝ → ℂ} (hf : ContinuousOn f s)
    (hs : ∀ t ∈ s, f t ∈ slitPlane) : ContinuousOn (fun t => arg (f t)) s :=
  fun t ht => (continuousAt_arg (hs t ht)).comp_continuousWithinAt (hf t ht)

/-! ### The polar angle of a path in `SL(2, ℝ)` -/

/-- A continuous angle `α` with `c(φ(τ)) = r e^{iα(τ)}`, `r > 0`, `α(0) = 0`, for a continuous
path `φ` in `SL(2, ℝ)` on `[0, 1]` starting at `1`. -/

lemma exists_polarC_lift {φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hc : ∀ i j, ContinuousOn (fun τ => φ τ i j) (Set.Icc 0 1))
    (hdet : ∀ τ ∈ Set.Icc (0 : ℝ) 1, (φ τ).det = 1) (h0 : φ 0 = 1) :
    ∃ α : ℝ → ℝ, Continuous α ∧ α 0 = 0 ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧ polarC (φ τ) = r * exp (α τ * I) := by
  have hpc : ContinuousOn (fun τ => polarC (φ τ)) (Set.Icc 0 1) :=
    continuousOn_complex_mk (((hc 0 0).add (hc 1 1)).div_const 2)
      (((hc 1 0).sub (hc 0 1)).div_const 2)
  let γ : C(unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun τ => ⟨polarC (φ τ), polarC_ne_zero (hdet τ τ.2)⟩,
      (hpc.restrict).subtype_mk _⟩
  have γ0 : γ 0 = (fun z : ℂ => (⟨exp z, exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) 0 := by
    apply Subtype.ext
    show polarC (φ 0) = exp 0
    rw [h0, exp_zero]
    simp [polarC, Complex.ext_iff]
  obtain ⟨Γ, hΓ, hΓ0⟩ := isCoveringMap_exp.exists_path_lifts γ 0 γ0
  refine ⟨fun τ => (Γ (Set.projIcc 0 1 zero_le_one τ)).im,
    (continuous_im.comp Γ.continuous).comp continuous_projIcc, ?_, ?_⟩
  · simp only
    rw [Set.projIcc_left]
    have : (⟨0, Set.left_mem_Icc.2 zero_le_one⟩ : Set.Icc (0 : ℝ) 1) = (0 : unitInterval) := rfl
    rw [this, hΓ0, zero_im]
  · intro τ hτ
    have hp := congrFun hΓ ⟨τ, hτ⟩
    have he : exp (Γ ⟨τ, hτ⟩) = polarC (φ τ) := congrArg Subtype.val hp
    refine ⟨Real.exp (Γ ⟨τ, hτ⟩).re, Real.exp_pos _, ?_⟩
    simp only
    rw [Set.projIcc_of_mem _ hτ, ← he]
    conv_lhs => rw [← re_add_im (Γ ⟨τ, hτ⟩)]
    rw [exp_add, ofReal_exp]

/-! ### The frame-flow factorization at every time -/


end
end HryniewiczCriterion

namespace HryniewiczCriterion

open Matrix Complex
open scoped ContDiff

noncomputable section


lemma sp_inv_mul_self {g : Matrix (Fin 4) (Fin 4) ℝ} (h : g.transpose * omegaMat * g = omegaMat) :
    g⁻¹ * g = 1 := by
  have h1 : (-(omegaMat * g.transpose * omegaMat)) * g = 1 := by
    have : (-(omegaMat * g.transpose * omegaMat)) * g =
        -(omegaMat * (g.transpose * omegaMat * g)) := by
      simp only [Matrix.neg_mul, Matrix.mul_assoc]
    rw [this, h, omegaMat_mul_self, neg_neg]
  rw [Matrix.inv_eq_left_inv h1, h1]


lemma sp_inv {g : Matrix (Fin 4) (Fin 4) ℝ} (h : g.transpose * omegaMat * g = omegaMat) :
    g⁻¹ * omegaMat * g⁻¹.transpose = omegaMat := by
  have hgi := sp_inv_mul_self h
  calc g⁻¹ * omegaMat * g⁻¹.transpose
      = g⁻¹ * (g * omegaMat * g.transpose) * g⁻¹.transpose := by rw [sp_mul_transpose h]
    _ = (g⁻¹ * g) * omegaMat * (g⁻¹ * g).transpose := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = omegaMat := by rw [hgi]; simp


end

end HryniewiczCriterion

theorem solution
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (T : ℝ) (hTpos : 0 < T)
    (hFsp : ∀ t, (F t).transpose * omegaMat * F t = omegaMat)
    (hFpos : ∀ t, 0 < (Complex.I * cdet (F t)).re)
    (hFc : ∀ i j, Continuous fun t => F t i j) (hFT : F T = F 0)
    (hφc : ∀ i j, ContinuousOn (fun t => φ t i j) (Set.Icc 0 1))
    (hφdet : ∀ t ∈ Set.Icc (0 : ℝ) 1, (φ t).det = 1) (hφ0 : φ 0 = 1) :
    ∃ θ α : ℝ → ℝ,
      IsDetAngleLift (fun t => graphUnitary4
        ((F 0)⁻¹ * F t * blockOne (φ (t / T)))) T θ ∧
      IsPolarAngleLift φ α ∧ θ T = 2 * α 1 := by
  set G := (F 0)⁻¹ with hGdef
  set B : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun t => blockOne (φ (t / T)) with hBdef
  -- symplectic facts
  have hGF0 : G * F 0 = 1 := sp_inv_mul_self (hFsp 0)
  have hG1 : G * omegaMat * G.transpose = omegaMat := sp_inv (hFsp 0)
  have hG2 : G.transpose * omegaMat * G = omegaMat := sp_transpose_of hG1
  have hGFsp : ∀ t, (G * F t).transpose * omegaMat * (G * F t) = omegaMat := fun t =>
    sp_mul hG2 (hFsp t)
  have hmem : ∀ t ∈ Set.Icc 0 T, t / T ∈ Set.Icc (0 : ℝ) 1 := fun t ht =>
    ⟨div_nonneg ht.1 hTpos.le, (div_le_one hTpos).2 ht.2⟩
  have hBsp : ∀ t ∈ Set.Icc 0 T, (B t).transpose * omegaMat * B t = omegaMat := fun t ht =>
    blockOne_sp (hφdet _ (hmem t ht))
  -- nonvanishing
  have hdG : cdet G ≠ 0 := cdet_ne_zero hG2
  have hdF : ∀ t, cdet (F t) ≠ 0 := fun t => cdet_ne_zero (hFsp t)
  have hdGF : ∀ t, cdet (G * F t) ≠ 0 := fun t => cdet_ne_zero (hGFsp t)
  have hdB : ∀ t ∈ Set.Icc 0 T, cdet (B t) ≠ 0 := fun t ht => by
    simp only [hBdef]; rw [cdet_blockOne]; exact polarC_ne_zero (hφdet _ (hmem t ht))
  have hdY : ∀ t ∈ Set.Icc 0 T, cdet (G * F t * B t) ≠ 0 := fun t ht =>
    cdet_ne_zero (sp_mul (hGFsp t) (hBsp t ht))
  -- the three factors
  set ν : ℝ → ℂ := fun t => I * cdet (F t) with hν
  set w1 : ℝ → ℂ := fun t => cdet (G * F t) / (cdet G * cdet (F t)) with hw1
  set w2 : ℝ → ℂ := fun t => cdet (G * F t * B t) / (cdet (G * F t) * cdet (B t)) with hw2
  have hνs : ∀ t, ν t ∈ slitPlane := fun t =>
    mem_slitPlane_iff.2 (Or.inl (hFpos t))
  have hw1s : ∀ t, w1 t ∈ slitPlane := fun t => cdet_mul_ratio_mem_slitPlane hG1 (hFsp t)
  have hw2s : ∀ t ∈ Set.Icc 0 T, w2 t ∈ slitPlane := fun t ht =>
    cdet_mul_ratio_mem_slitPlane (sp_mul_transpose (hGFsp t)) (hBsp t ht)
  have hne : ∀ z : ℂ, z ∈ slitPlane → z ≠ 0 := fun z hz => slitPlane_ne_zero hz
  -- continuity
  have hFcO : ∀ i j, ContinuousOn (fun t => F t i j) (Set.Icc 0 T) := fun i j =>
    (hFc i j).continuousOn
  have hGcO : ∀ i j, ContinuousOn (fun _ : ℝ => G i j) (Set.Icc 0 T) := fun _ _ =>
    continuousOn_const
  have hdiv : ContinuousOn (fun t : ℝ => t / T) (Set.Icc 0 T) :=
    continuousOn_id.div_const T
  have hBcO : ∀ i j, ContinuousOn (fun t => B t i j) (Set.Icc 0 T) := by
    intro i j
    have hφT : ∀ k l, ContinuousOn (fun t => φ (t / T) k l) (Set.Icc 0 T) := fun k l =>
      (hφc k l).comp hdiv (fun t ht => hmem t ht)
    fin_cases i <;> fin_cases j <;> simp only [hBdef, blockOne] <;> simp <;>
      first | exact continuousOn_const | exact hφT _ _
  have hGFcO := continuousOn_mul_entries hGcO hFcO
  have hYcO := continuousOn_mul_entries hGFcO hBcO
  have hνc : ContinuousOn ν (Set.Icc 0 T) :=
    continuousOn_const.mul (continuousOn_cdet hFcO)
  have hw1c : ContinuousOn w1 (Set.Icc 0 T) :=
    (continuousOn_cdet hGFcO).div (continuousOn_const.mul (continuousOn_cdet hFcO))
      fun t _ => mul_ne_zero hdG (hdF t)
  have hw2c : ContinuousOn w2 (Set.Icc 0 T) :=
    (continuousOn_cdet hYcO).div ((continuousOn_cdet hGFcO).mul (continuousOn_cdet hBcO))
      fun t ht => mul_ne_zero (hdGF t) (hdB t ht)
  -- the polar angle
  obtain ⟨α, hαc, hα0, hαr⟩ := exists_polarC_lift hφc hφdet hφ0
  -- endpoint values
  have hB0 : B 0 = 1 := by simp only [hBdef, zero_div]; rw [hφ0, blockOne_one]
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hTpos.le⟩
  have hTmem : T ∈ Set.Icc 0 T := ⟨hTpos.le, le_rfl⟩
  have hw2_0 : w2 0 = 1 := by
    simp only [hw2]; rw [hGF0, hB0, Matrix.mul_one, cdet_one]; simp
  have hw2_T : w2 T = 1 := by
    simp only [hw2]; rw [hFT, hGF0, Matrix.one_mul, cdet_one, one_mul]
    exact div_self (hdB T hTmem)
  refine ⟨fun t => 2 * (arg (w2 t) + arg (w1 t) + arg (ν t) + α (t / T) - arg (w1 0) -
    arg (ν 0)), α, ⟨?_, ?_, ?_⟩, ⟨hαc.continuousOn, hα0, ?_⟩, ?_⟩
  · -- continuity
    refine ContinuousOn.mul continuousOn_const ?_
    exact ((((continuousOn_arg_comp hw2c hw2s).add
      (continuousOn_arg_comp hw1c fun t _ => hw1s t)).add
      (continuousOn_arg_comp hνc fun t _ => hνs t)).add (hαc.comp_continuousOn hdiv)).sub
      continuousOn_const |>.sub continuousOn_const
  · simp only [zero_div, hα0, hw2_0, arg_one]; ring
  · intro t ht
    simp only
    change (graphUnitary4 (G * F t * B t)).det = _
    rw [det_graphUnitary4 (hdY t ht)]
    obtain ⟨r, hr, hcr⟩ := hαr (t / T) (hmem t ht)
    have hcB : cdet (B t) = polarC (φ (t / T)) := cdet_blockOne _
    -- the key identity
    have key : cdet (G * F t * B t) =
        w2 t * w1 t * ν t * (r * exp (α (t / T) * I)) / (w1 0 * ν 0) := by
      rw [← hcr, ← hcB]
      simp only [hw1, hw2, hν]
      rw [hGF0, cdet_one]
      have := hdB t ht; have := hdF t; have := hdF 0; have := hdGF t
      field_simp
    have s1 := hne _ (hw2s t ht); have s2 := hne _ (hw1s t); have s3 := hne _ (hνs t)
    have s4 := hne _ (hw1s 0); have s5 := hne _ (hνs 0)
    rw [key]
    generalize w2 t = a at s1 ⊢
    generalize w1 t = b at s2 ⊢
    generalize ν t = c at s3 ⊢
    generalize w1 0 = d at s4 ⊢
    generalize ν 0 = e at s5 ⊢
    rw [div_star_div, div_star_mul (a * b * c), div_star_mul (a * b), div_star_mul a,
      div_star_mul d,
      div_star_eq_exp_arg s1, div_star_eq_exp_arg s2,
      div_star_eq_exp_arg s3, ofReal_mul_exp_div_star r hr.ne',
      div_star_eq_exp_arg s4, div_star_eq_exp_arg s5]
    simp only [← Complex.exp_add, ← Complex.exp_sub]
    congr 1; push_cast; ring
  · intro τ hτ
    obtain ⟨r, hr, hcr⟩ := hαr τ hτ
    exact polar_of_polarC (hφdet τ hτ) hr hcr
  · simp only [div_self hTpos.ne', hw2_T, arg_one]
    have e1 : w1 T = w1 0 := by simp only [hw1]; rw [hFT]
    have e2 : ν T = ν 0 := by simp only [hν]; rw [hFT]
    rw [e1, e2]; ring


