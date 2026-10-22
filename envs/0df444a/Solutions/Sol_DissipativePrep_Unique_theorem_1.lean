-- Prove2me | solution 1 for DissipativePrep.Unique.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T22:46:50.552763+00:00
-- url     : https://prove2.me/submissions/91f4e2ce-5c77-4ed5-bde4-19073f5c6f12

import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16 DissipativePrep.Unique

namespace DPt1Aux

lemma gform {d : ℕ} (D : LindbladData d) (φ : Fin d → ℂ) :
    gkslGenerator D (Matrix.vecMulVec φ (star φ)) =
      ∑ k, Matrix.vecMulVec (D.jump k *ᵥ φ) (star (D.jump k *ᵥ φ)) -
        Matrix.vecMulVec (driftK D *ᵥ φ) (star φ) -
        Matrix.vecMulVec φ (star (driftK D *ᵥ φ)) := by
  simp only [gkslGenerator, cpGenerator, sandwich, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  simp only [Matrix.vecMulVec_mul, Matrix.mul_vecMulVec, Matrix.star_mulVec]

lemma hconj {d : ℕ} (a b : Fin d → ℂ) : star a ⬝ᵥ b = star (star b ⬝ᵥ a) := by
  simp [dotProduct, star_sum, mul_comm]

lemma vmv_smul {d : ℕ} (a : ℂ) (w : Fin d → ℂ) :
    Matrix.vecMulVec (a • w) (star (a • w)) = (a * star a) • Matrix.vecMulVec w (star w) := by
  rw [star_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul]

lemma QK {d m : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (c : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → ℝ) (hg : ∀ l, 0 < g l) :
    (Qop H c g)ᴴ = driftK (krausData H hH c g) := by
  have h1 : (Qop H c g)ᴴ = Complex.I • H + ∑ l, ((g l : ℝ) : ℂ) • ((c l)ᴴ * c l) := by
    simp only [Qop, Pop, Matrix.conjTranspose_sub, Matrix.conjTranspose_sum,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hH.eq, Complex.star_def, Complex.conj_ofReal, Complex.conj_I, neg_smul, sub_neg_eq_add]
    abel
  rw [h1]
  show _ = Complex.I • H + (1 / 2 : ℂ) • ∑ l : Fin m,
    ((((Real.sqrt (2 * g l) : ℝ) : ℂ) • c l)ᴴ * (((Real.sqrt (2 * g l) : ℝ) : ℂ) • c l))
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
  congr 1
  have hs : ((Real.sqrt (2 * g l) : ℝ) : ℂ) * ((Real.sqrt (2 * g l) : ℝ) : ℂ) =
      ((2 * g l : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith [hg l])]
  rw [Complex.star_def, Complex.conj_ofReal, mul_assoc, mul_comm _ ((Real.sqrt _ : ℝ) : ℂ), hs]
  push_cast; ring

lemma mulconj (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

end DPt1Aux

open DPt1Aux

theorem solution {d m : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (c : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → ℝ) (hg : ∀ l, 0 < g l)
    (Φ : EuclideanSpace ℂ (Fin d)) (hΦ : ‖Φ‖ = 1) :
    gkslGenerator (krausData H hH c g) (pureDensity Φ) = 0 ↔
      ∃ lam : ℂ, act (Qop H c g)ᴴ Φ = lam • Φ ∧
        ∃ lamL : Fin m → ℂ, (∀ l, act (c l) Φ = lamL l • Φ) ∧
          ∑ l, g l * ‖lamL l‖ ^ 2 = lam.re := by
  set φ : Fin d → ℂ := WithLp.ofLp Φ with hφdef
  have hpd : pureDensity Φ = Matrix.vecMulVec φ (star φ) := by
    ext i j; rfl
  have hact : ∀ (A : Matrix (Fin d) (Fin d) ℂ) (z : ℂ), act A Φ = z • Φ ↔ A *ᵥ φ = z • φ := by
    intro A z
    constructor
    · intro h; exact congrArg WithLp.ofLp h
    · intro h; exact congrArg (WithLp.toLp 2) h
  have hφ : star φ ⬝ᵥ φ = 1 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) Φ
    rw [hΦ, EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [dotProduct_comm, h]; simp
  set w : Fin m → Fin d → ℂ := fun l => c l *ᵥ φ with hwdef
  set u : Fin d → ℂ := driftK (krausData H hH c g) *ᵥ φ with hudef
  have hG : gkslGenerator (krausData H hH c g) (pureDensity Φ) =
      ∑ l, ((2 * g l : ℝ) : ℂ) • Matrix.vecMulVec (w l) (star (w l)) -
        Matrix.vecMulVec u (star φ) - Matrix.vecMulVec φ (star u) := by
    rw [hpd, gform]
    congr 2
    refine Finset.sum_congr rfl fun l _ => ?_
    show Matrix.vecMulVec ((((Real.sqrt (2 * g l) : ℝ) : ℂ) • c l) *ᵥ φ)
      (star ((((Real.sqrt (2 * g l) : ℝ) : ℂ) • c l) *ᵥ φ)) = _
    rw [Matrix.smul_mulVec, vmv_smul, mulconj]
    congr 2
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact Real.sq_sqrt (by linarith [hg l])
  have hQ : ∀ lam : ℂ, act (Qop H c g)ᴴ Φ = lam • Φ ↔ u = lam • φ := by
    intro lam; rw [hact, QK H hH c g hg]
  have hMv : ∀ x : Fin d → ℂ, (∑ l, ((2 * g l : ℝ) : ℂ) • Matrix.vecMulVec (w l) (star (w l)) -
        Matrix.vecMulVec u (star φ) - Matrix.vecMulVec φ (star u)) *ᵥ x =
      ∑ l, (((2 * g l : ℝ) : ℂ) * (star (w l) ⬝ᵥ x)) • w l - (star φ ⬝ᵥ x) • u -
        (star u ⬝ᵥ x) • φ := by
    intro x
    simp only [Matrix.sub_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
      op_smul_eq_smul, smul_smul]
  rw [hG]
  constructor
  · intro hz
    -- step 1: each w l is a multiple of φ
    have hw : ∀ k, w k = (star φ ⬝ᵥ w k) • φ := by
      intro k
      set r := w k - (star φ ⬝ᵥ w k) • φ with hr
      have hφr : star φ ⬝ᵥ r = 0 := by
        rw [hr, dotProduct_sub, dotProduct_smul, hφ, smul_eq_mul, mul_one, sub_self]
      have h0 := congrArg (fun M => star r ⬝ᵥ (M *ᵥ r)) hz
      simp only [hMv, Matrix.zero_mulVec, dotProduct_zero, dotProduct_sub, dotProduct_sum,
        dotProduct_smul, smul_eq_mul, hφr, zero_mul, sub_zero] at h0
      have hrφ : star r ⬝ᵥ φ = 0 := by rw [hconj, hφr, star_zero]
      rw [hrφ, mul_zero, sub_zero] at h0
      have hterm : ∀ l, ((2 * g l : ℝ) : ℂ) * (star (w l) ⬝ᵥ r) * (star r ⬝ᵥ w l) =
          ((2 * g l : ℝ) : ℂ) * ((star (w l) ⬝ᵥ r) * star (star (w l) ⬝ᵥ r)) := by
        intro l; rw [hconj r (w l)]; ring
      simp only [hterm] at h0
      have hnn : ∀ l ∈ Finset.univ, 0 ≤ ((2 * g l : ℝ) : ℂ) *
          ((star (w l) ⬝ᵥ r) * star (star (w l) ⬝ᵥ r)) := by
        intro l _
        refine mul_nonneg ?_ (mul_star_self_nonneg _)
        exact_mod_cast (by linarith [hg l] : (0:ℝ) ≤ 2 * g l)
      have hk := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 k (Finset.mem_univ k)
      have hgk : ((2 * g k : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (by linarith [hg k] : (2 * g k : ℝ) ≠ 0)
      have hwr : star (w k) ⬝ᵥ r = 0 := by
        rcases mul_eq_zero.1 hk with h | h
        · exact absurd h hgk
        · rcases mul_eq_zero.1 h with h | h
          · exact h
          · exact star_eq_zero.1 h
      have hrr : star r ⬝ᵥ r = 0 := by
        have : star r ⬝ᵥ r = star (w k) ⬝ᵥ r - star (star φ ⬝ᵥ w k) * (star φ ⬝ᵥ r) := by
          rw [hr, star_sub, star_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul, ← hr]
        rw [this, hwr, hφr, mul_zero, sub_zero]
      have := dotProduct_star_self_eq_zero.1 hrr
      rw [hr, sub_eq_zero] at this
      exact this
    set lamL : Fin m → ℂ := fun l => star φ ⬝ᵥ w l with hlam
    set S : ℂ := ∑ l, ((2 * g l : ℝ) : ℂ) * (lamL l * star (lamL l)) with hS
    have h1 := congrArg (fun M => M *ᵥ φ) hz
    simp only [hMv, Matrix.zero_mulVec, hφ, one_smul] at h1
    have hsum : ∑ l, (((2 * g l : ℝ) : ℂ) * (star (w l) ⬝ᵥ φ)) • w l = S • φ := by
      rw [hS, Finset.sum_smul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hw l, star_smul, smul_dotProduct, hφ, smul_smul]
      simp only [smul_eq_mul, mul_one]
      congr 1; ring
    rw [hsum, sub_sub, sub_eq_zero] at h1
    set μ : ℂ := S - star u ⬝ᵥ φ with hμ
    have hu : u = μ • φ := by
      rw [hμ, sub_smul, h1]; abel
    have hμc : star u ⬝ᵥ φ = star μ := by
      rw [hconj, hu, dotProduct_smul, hφ, smul_eq_mul, mul_one]
    have hSre : S = ((∑ l, 2 * g l * ‖lamL l‖ ^ 2 : ℝ) : ℂ) := by
      rw [hS]; push_cast
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mulconj]; push_cast; ring
    refine ⟨μ, (hQ μ).2 hu, lamL, fun l => (hact _ _).2 (hw l), ?_⟩
    have key : μ = S - star μ := by rw [← hμc]
    clear_value μ S
    have hre := congrArg Complex.re key
    rw [Complex.sub_re, hSre, Complex.ofReal_re, Complex.star_def, Complex.conj_re] at hre
    have : ∑ l, 2 * g l * ‖lamL l‖ ^ 2 = 2 * ∑ l, g l * ‖lamL l‖ ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => by ring
    rw [this] at hre
    linarith
  · rintro ⟨lam, hl, lamL, hL, hs⟩
    have hu := (hQ lam).1 hl
    have hw : ∀ l, w l = lamL l • φ := fun l => (hact _ _).1 (hL l)
    simp only [hw, hu, vmv_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, star_smul,
      smul_smul, ← Finset.sum_smul, ← sub_smul, mulconj]
    convert zero_smul ℂ (Matrix.vecMulVec φ (star φ)) using 2
    have e : ∀ i, ((2 * g i : ℝ) : ℂ) * (star (lamL i) * lamL i) =
        ((2 * (g i * ‖lamL i‖ ^ 2) : ℝ) : ℂ) := by
      intro i; rw [mul_comm (star _), mulconj]; push_cast; ring
    simp_rw [e]
    rw [← Complex.ofReal_sum, ← Finset.mul_sum, hs]
    apply Complex.ext <;> simp; ring
