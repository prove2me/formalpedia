-- Prove2me | solution 1 for BosonicLearn.gaussian_sample_concentration
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T18:03:27.160584+00:00
-- url     : https://prove2.me/submissions/d1f078f6-8c20-4c51-9e8e-53452cdb54a5

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_extreme_singular_values_deviation
import Theorems.Thm_GaussianMatrix_gaussian_concentration
import Theorems.Thm_GaussianMatrix_frobenius_second_moment

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder

open GaussianMatrix

noncomputable section

/-! ### Column mean and centered covariance of a data matrix -/

/-- Column means of an `N × m` data matrix. -/
private def cmean {N m : ℕ} (G : Fin N → Fin m → ℝ) : Fin m → ℝ :=
  fun k => (1 / (N : ℝ)) * ∑ j, G j k

/-- Centered empirical covariance of the rows. -/
private def ccov {N m : ℕ} (G : Fin N → Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun a b => (1 / (N : ℝ)) * ∑ j, (G j a - cmean G a) * (G j b - cmean G b)

private lemma quad_identity {N m : ℕ} (c : ℝ) (u : Fin N → Fin m → ℝ) (x : Fin m → ℝ) :
    ∑ a, x a * ∑ b, (c * ∑ j, u j a * u j b) * x b = c * ∑ j, (∑ a, u j a * x a) ^ 2 := by
  have h : ∀ j, (∑ a, u j a * x a) ^ 2 = ∑ a, ∑ b, x a * (u j a * u j b) * x b := by
    intro j
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  calc ∑ a, x a * ∑ b, (c * ∑ j, u j a * u j b) * x b
      = ∑ a, ∑ b, ∑ j, c * (x a * (u j a * u j b) * x b) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ a, ∑ j, ∑ b, c * (x a * (u j a * u j b) * x b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ b, c * (x a * (u j a * u j b) * x b) := Finset.sum_comm
    _ = c * ∑ j, (∑ a, u j a * x a) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [h j, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]

private lemma ccov_form_eq {N m : ℕ} (G : Fin N → Fin m → ℝ) (x : Fin m → ℝ) :
    x ⬝ᵥ (ccov G *ᵥ x) =
      (1 / (N : ℝ)) * ∑ j, ((Matrix.of G *ᵥ x) j - cmean G ⬝ᵥ x) ^ 2 := by
  have h := quad_identity (1 / (N : ℝ)) (fun j a => G j a - cmean G a) x
  have hu : ∀ j, ∑ a, (G j a - cmean G a) * x a = (Matrix.of G *ᵥ x) j - cmean G ⬝ᵥ x := by
    intro j
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib]
  simp only [hu] at h
  rw [← h]
  simp only [dotProduct, Matrix.mulVec, ccov, Matrix.of_apply]

private lemma ccov_form_nonneg {N m : ℕ} (G : Fin N → Fin m → ℝ) (x : Fin m → ℝ) :
    0 ≤ x ⬝ᵥ (ccov G *ᵥ x) := by
  rw [ccov_form_eq]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => sq_nonneg _)

private lemma ccov_form {N m : ℕ} (hN : 1 ≤ N) (G : Fin N → Fin m → ℝ) (x : Fin m → ℝ) :
    x ⬝ᵥ (ccov G *ᵥ x) =
      (1 / (N : ℝ)) * ((Matrix.of G *ᵥ x) ⬝ᵥ (Matrix.of G *ᵥ x)) - (cmean G ⬝ᵥ x) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [ccov_form_eq]
  set a : Fin N → ℝ := Matrix.of G *ᵥ x with ha
  set c : ℝ := cmean G ⬝ᵥ x with hc
  have hsum : ∑ j, a j = N * c := by
    rw [hc, ha]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, cmean]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul]
    field_simp
  have hexp : ∑ j, (a j - c) ^ 2 = a ⬝ᵥ a - N * c ^ 2 := by
    have h1 : ∀ j, (a j - c) ^ 2 = a j * a j - 2 * c * a j + c ^ 2 := fun j => by ring
    simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, dotProduct]
    ring
  rw [hexp]
  field_simp

private lemma mulVec_sq_le {N m : ℕ} (A : Matrix (Fin N) (Fin m) ℝ) (x : Fin m → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ x) ≤ specNorm A ^ 2 * (x ⬝ᵥ x) := by
  have hn : ∀ (ι : Type) [Fintype ι] (v : ι → ℝ),
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ ^ 2 = v ⬝ᵥ v := by
    intro ι _ v
    rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, sq]
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have e1 : ‖(EuclideanSpace.equiv (Fin N) ℝ).symm
      (A *ᵥ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m)).ofLp)‖ ^ 2 = (A *ᵥ x) ⬝ᵥ (A *ᵥ x) := hn _ _
  have e2 : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ ^ 2 = x ⬝ᵥ x := hn _ _
  rw [mul_pow, e1, e2] at h2
  exact h2

private lemma sMin_sq_le {N m : ℕ} (A : Matrix (Fin N) (Fin m) ℝ) (x : Fin m → ℝ) :
    sMin A ^ 2 * (x ⬝ᵥ x) ≤ (A *ᵥ x) ⬝ᵥ (A *ᵥ x) := by
  have hq : ∀ v : Fin N → ℝ, 0 ≤ v ⬝ᵥ v := fun v => Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hs0 : 0 ≤ sMin A := Real.iInf_nonneg fun _ => Real.sqrt_nonneg _
  have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rcases hxx.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact hq _
  · set s : ℝ := Real.sqrt (x ⬝ᵥ x) with hs
    have hspos : 0 < s := Real.sqrt_pos.mpr hpos
    have hs2 : s ^ 2 = x ⬝ᵥ x := Real.sq_sqrt hpos.le
    have hu : (s⁻¹ • x) ⬝ᵥ (s⁻¹ • x) = 1 := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hs2]
      field_simp
    have hle : sMin A ≤ Real.sqrt ((A *ᵥ (s⁻¹ • x)) ⬝ᵥ (A *ᵥ (s⁻¹ • x))) :=
      ciInf_le (f := fun y : {y : Fin m → ℝ // y ⬝ᵥ y = 1} =>
        Real.sqrt ((A *ᵥ y.1) ⬝ᵥ (A *ᵥ y.1)))
        ⟨0, by rintro _ ⟨y, rfl⟩; exact Real.sqrt_nonneg _⟩ ⟨s⁻¹ • x, hu⟩
    have hAu : (A *ᵥ (s⁻¹ • x)) ⬝ᵥ (A *ᵥ (s⁻¹ • x)) = s⁻¹ ^ 2 * ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) := by
      rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      ring
    have h2 := pow_le_pow_left₀ hs0 hle 2
    rw [Real.sq_sqrt (hq _), hAu] at h2
    have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg s)
    rw [← hs2]
    calc sMin A ^ 2 * s ^ 2 ≤ s⁻¹ ^ 2 * ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) * s ^ 2 := h3
      _ = (A *ᵥ x) ⬝ᵥ (A *ᵥ x) := by field_simp

/-- Loewner bounds on the centered covariance from bounds on the mean and the extreme singular values. -/
private lemma cov_bounds {N m : ℕ} (hN : 1 ≤ N) (G : Fin N → Fin m → ℝ) (χ : ℝ) (hχ : 0 ≤ χ)
    (hmean : cmean G ⬝ᵥ cmean G ≤ χ ^ 2 / N)
    (hmin : Real.sqrt N - χ ≤ sMin (Matrix.of G))
    (hmax : specNorm (Matrix.of G) ≤ Real.sqrt N + χ) :
    (ccov G - (1 - (2 * χ / Real.sqrt N + 2 * χ ^ 2 / N)) •
      (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef ∧
    ((1 + (2 * χ / Real.sqrt N + 2 * χ ^ 2 / N)) • (1 : Matrix (Fin m) (Fin m) ℝ) -
      ccov G).PosSemidef := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set r : ℝ := Real.sqrt N with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr hNpos
  have hr2 : r ^ 2 = N := Real.sq_sqrt hNpos.le
  have hζN : (2 * χ / r + 2 * χ ^ 2 / N) * N = 2 * χ * r + 2 * χ ^ 2 := by
    rw [← hr2]
    field_simp
  have hsymm : (ccov G).IsHermitian := by
    ext a b
    simp only [Matrix.conjTranspose_apply, ccov, Matrix.of_apply, star_trivial]
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have h1herm : ∀ c : ℝ, (c • (1 : Matrix (Fin m) (Fin m) ℝ)).IsHermitian := by
    intro c
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  -- the scalar facts for a vector `x`
  have key : ∀ x : Fin m → ℝ,
      (N - 2 * χ * r - 2 * χ ^ 2) * (x ⬝ᵥ x) ≤ N * (x ⬝ᵥ (ccov G *ᵥ x)) ∧
      N * (x ⬝ᵥ (ccov G *ᵥ x)) ≤ (N + 2 * χ * r + 2 * χ ^ 2) * (x ⬝ᵥ x) := by
    intro x
    have hp : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hform := ccov_form hN G x
    have hnn := ccov_form_nonneg G x
    set q : ℝ := (Matrix.of G *ᵥ x) ⬝ᵥ (Matrix.of G *ᵥ x) with hq
    set p : ℝ := x ⬝ᵥ x with hpdef
    set c : ℝ := cmean G ⬝ᵥ x with hc
    have hNform : N * (x ⬝ᵥ (ccov G *ᵥ x)) = q - N * c ^ 2 := by
      rw [hform]
      field_simp
    have hcs : c ^ 2 ≤ (cmean G ⬝ᵥ cmean G) * p := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (cmean G) x
      simpa [dotProduct, sq, hc, hpdef] using h
    have hNc : N * c ^ 2 ≤ χ ^ 2 * p := by
      have h1 : c ^ 2 ≤ χ ^ 2 / N * p := hcs.trans (mul_le_mul_of_nonneg_right hmean hp)
      have h2 := mul_le_mul_of_nonneg_left h1 hNpos.le
      calc N * c ^ 2 ≤ N * (χ ^ 2 / N * p) := h2
        _ = χ ^ 2 * p := by field_simp
    have hupper : q ≤ (r + χ) ^ 2 * p := by
      have h1 := mulVec_sq_le (Matrix.of G) x
      have h2 : specNorm (Matrix.of G) ^ 2 ≤ (r + χ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hmax 2
      exact h1.trans (mul_le_mul_of_nonneg_right h2 hp)
    constructor
    · rw [hNform]
      by_cases hcase : χ ≤ r
      · have h1 := sMin_sq_le (Matrix.of G) x
        have h2 : (r - χ) ^ 2 ≤ sMin (Matrix.of G) ^ 2 :=
          pow_le_pow_left₀ (by linarith) hmin 2
        have h3 : (r - χ) ^ 2 * p ≤ q := (mul_le_mul_of_nonneg_right h2 hp).trans h1
        nlinarith [mul_nonneg (sq_nonneg χ) hp]
      · rw [not_le] at hcase
        have h1 : 0 ≤ q - N * c ^ 2 := by
          rw [← hNform]
          exact mul_nonneg hNpos.le hnn
        have h2 : (N : ℝ) - 2 * χ * r - 2 * χ ^ 2 ≤ 0 := by nlinarith
        nlinarith [mul_nonneg hp (neg_nonneg.mpr h2)]
    · rw [hNform]
      have h1 : 0 ≤ N * c ^ 2 := by positivity
      nlinarith [mul_nonneg (sq_nonneg χ) hp]
  constructor
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hsymm.sub (h1herm _)) fun x => ?_
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul]
    have h := (key x).1
    have h2 : (1 - (2 * χ / r + 2 * χ ^ 2 / N)) * (x ⬝ᵥ x) * N =
        (N - 2 * χ * r - 2 * χ ^ 2) * (x ⬝ᵥ x) := by
      have : (1 - (2 * χ / r + 2 * χ ^ 2 / N)) * N = N - 2 * χ * r - 2 * χ ^ 2 := by
        rw [sub_mul, one_mul, hζN]
        ring
      rw [mul_right_comm, this]
    have h3 : (1 - (2 * χ / r + 2 * χ ^ 2 / N)) * (x ⬝ᵥ x) * N ≤ (x ⬝ᵥ (ccov G *ᵥ x)) * N := by
      rw [h2, mul_comm (x ⬝ᵥ (ccov G *ᵥ x))]
      exact h
    have h4 := le_of_mul_le_mul_right h3 hNpos
    linarith
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ((h1herm _).sub hsymm) fun x => ?_
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul]
    have h := (key x).2
    have h2 : (1 + (2 * χ / r + 2 * χ ^ 2 / N)) * (x ⬝ᵥ x) * N =
        (N + 2 * χ * r + 2 * χ ^ 2) * (x ⬝ᵥ x) := by
      have : (1 + (2 * χ / r + 2 * χ ^ 2 / N)) * N = N + 2 * χ * r + 2 * χ ^ 2 := by
        rw [add_mul, one_mul, hζN]
        ring
      rw [mul_right_comm, this]
    have h3 : (x ⬝ᵥ (ccov G *ᵥ x)) * N ≤ (1 + (2 * χ / r + 2 * χ ^ 2 / N)) * (x ⬝ᵥ x) * N := by
      rw [h2, mul_comm (x ⬝ᵥ (ccov G *ᵥ x))]
      exact h
    have h4 := le_of_mul_le_mul_right h3 hNpos
    linarith

/-! ### The scaled column sum and its concentration -/

private def rowS (N : ℕ) : Matrix (Fin 1) (Fin N) ℝ := fun _ _ => (Real.sqrt N)⁻¹

/-- `h(G) = ‖(1/√N) ∑ⱼ Gⱼ‖₂ = √N ‖ḡ‖₂`. -/
private def hfun {N m : ℕ} (G : Fin N → Fin m → ℝ) : ℝ :=
  Real.sqrt (frobSq (rowS N * Matrix.of G * (1 : Matrix (Fin m) (Fin m) ℝ)))

private lemma frobSq_nonneg' {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) : 0 ≤ frobSq A :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

private lemma frobSq_row {N m : ℕ} (G : Fin N → Fin m → ℝ) :
    frobSq (rowS N * Matrix.of G * (1 : Matrix (Fin m) (Fin m) ℝ)) =
      ∑ k, ((Real.sqrt N)⁻¹ * ∑ j, G j k) ^ 2 := by
  rw [Matrix.mul_one]
  simp only [frobSq, Fin.sum_univ_one, Matrix.mul_apply, rowS, Matrix.of_apply, Finset.mul_sum]

private lemma hfun_sq {N m : ℕ} (G : Fin N → Fin m → ℝ) :
    hfun G ^ 2 = ∑ k, ((Real.sqrt N)⁻¹ * ∑ j, G j k) ^ 2 := by
  unfold hfun
  rw [Real.sq_sqrt (frobSq_nonneg' _), frobSq_row]

private lemma cmean_sq_eq {N m : ℕ} (hN : 1 ≤ N) (G : Fin N → Fin m → ℝ) :
    cmean G ⬝ᵥ cmean G = hfun G ^ 2 / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hr2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNpos.le
  have hrpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  rw [hfun_sq, Finset.sum_div]
  simp only [dotProduct, cmean]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_pow, inv_pow, hr2]
  field_simp

/-- `h` is the Euclidean norm of a linear image of the matrix. -/
private lemma hfun_eq_norm {N m : ℕ} (G : Fin N → Fin m → ℝ) :
    hfun G = ‖(WithLp.toLp 2 (fun k => (Real.sqrt N)⁻¹ * ∑ j, G j k) : EuclideanSpace ℝ (Fin m))‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold hfun
  rw [frobSq_row]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

private lemma hfun_lip {N m : ℕ} (hN : 1 ≤ N) (X Y : Fin N → Fin m → ℝ) :
    |hfun X - hfun Y| ≤ 1 * frobNorm (Matrix.of X - Matrix.of Y) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hr2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNpos.le
  rw [hfun_eq_norm, hfun_eq_norm, one_mul]
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [← WithLp.toLp_sub, EuclideanSpace.norm_eq]
  unfold frobNorm
  refine Real.sqrt_le_sqrt ?_
  unfold frobSq
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Real.norm_eq_abs, sq_abs]
  show ((Real.sqrt N)⁻¹ * ∑ j, X j k - (Real.sqrt N)⁻¹ * ∑ j, Y j k) ^ 2 ≤
    ∑ j, (X j k - Y j k) ^ 2
  have h1 : (Real.sqrt N)⁻¹ * ∑ j, X j k - (Real.sqrt N)⁻¹ * ∑ j, Y j k =
      (Real.sqrt N)⁻¹ * ∑ j, (X j k - Y j k) := by
    rw [Finset.sum_sub_distrib, mul_sub]
  rw [h1, mul_pow, inv_pow, hr2]
  have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => X j k - Y j k)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  rw [inv_mul_le_iff₀ hNpos]
  exact h2

private lemma hfun_mean_le {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m) :
    ∫ G, hfun G ∂(gaussianMatrix N m) ≤ Real.sqrt m := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hr2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNpos.le
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hint := (gaussian_concentration (p := N) (m := m) hfun 1 one_pos (hfun_lip hN) 0 le_rfl).1
  have h2 := frobenius_second_moment (rowS N) (1 : Matrix (Fin m) (Fin m) ℝ)
  have hS : frobSq (rowS N) = 1 := by
    have h : frobSq (rowS N) = (N : ℝ) * ((Real.sqrt N)⁻¹) ^ 2 := by
      simp [frobSq, rowS]
    rw [h, inv_pow, hr2]
    field_simp
  have hT : frobSq (1 : Matrix (Fin m) (Fin m) ℝ) = m := by
    simp [frobSq, Matrix.one_apply]
  rw [hS, hT, one_mul] at h2
  have hsq : ∀ G : Fin N → Fin m → ℝ, hfun G ^ 2 =
      frobSq (rowS N * Matrix.of G * (1 : Matrix (Fin m) (Fin m) ℝ)) := fun G => by
    unfold hfun
    rw [Real.sq_sqrt (frobSq_nonneg' _)]
  have h2' : ∫ G, hfun G ^ 2 ∂(gaussianMatrix N m) = m := by
    simp only [hsq]
    exact h2
  have hint2 : Integrable (fun G => hfun G ^ 2) (gaussianMatrix N m) := by
    by_contra hni
    rw [integral_undef hni] at h2'
    linarith
  set c : ℝ := ∫ G, hfun G ∂(gaussianMatrix N m) with hc
  have hvar : 0 ≤ ∫ G, (hfun G - c) ^ 2 ∂(gaussianMatrix N m) :=
    integral_nonneg fun G => sq_nonneg _
  have hexp : ∫ G, (hfun G - c) ^ 2 ∂(gaussianMatrix N m) = m - c ^ 2 := by
    have h1 : ∀ G : Fin N → Fin m → ℝ, (hfun G - c) ^ 2 = hfun G ^ 2 - 2 * c * hfun G + c ^ 2 :=
      fun G => by ring
    simp only [h1]
    have e1 : ∫ G, (hfun G ^ 2 - 2 * c * hfun G + c ^ 2) ∂(gaussianMatrix N m) =
        ∫ G, (hfun G ^ 2 - 2 * c * hfun G) ∂(gaussianMatrix N m) +
          ∫ _G, c ^ 2 ∂(gaussianMatrix N m) :=
      integral_add (hint2.sub (hint.const_mul _)) (integrable_const _)
    have e2 : ∫ G, (hfun G ^ 2 - 2 * c * hfun G) ∂(gaussianMatrix N m) =
        ∫ G, hfun G ^ 2 ∂(gaussianMatrix N m) - ∫ G, 2 * c * hfun G ∂(gaussianMatrix N m) :=
      integral_sub hint2 (hint.const_mul _)
    rw [e1, e2, integral_const_mul, h2', ← hc, integral_const]
    simp
    ring
  rw [hexp] at hvar
  have h3 : c ^ 2 ≤ m := by linarith
  exact (le_abs_self c).trans (Real.abs_le_sqrt h3)

/-- On a standard Gaussian matrix the three bounds hold simultaneously with probability
at least `1 - 3 e^{-t²/2}`. -/
private lemma std_event {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m) (t : ℝ) (ht : 0 ≤ t) :
    1 - ENNReal.ofReal (3 * Real.exp (-t ^ 2 / 2)) ≤ (gaussianMatrix N m)
      {G | cmean G ⬝ᵥ cmean G ≤ (Real.sqrt m + t) ^ 2 / N ∧
        Real.sqrt N - (Real.sqrt m + t) ≤ sMin (Matrix.of G) ∧
        specNorm (Matrix.of G) ≤ Real.sqrt N + (Real.sqrt m + t)} := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hint, hbad⟩ := gaussian_concentration (p := N) (m := m) hfun 1 one_pos (hfun_lip hN) t ht
  have hgood := extreme_singular_values_deviation (N := N) (n := m) hm t ht
  have hmean := hfun_mean_le hN hm
  have hsub : {A : Fin N → Fin m → ℝ | Real.sqrt N - Real.sqrt m - t ≤ sMin (Matrix.of A) ∧
        specNorm (Matrix.of A) ≤ Real.sqrt N + Real.sqrt m + t} \
      {X | (∫ Y, hfun Y ∂(gaussianMatrix N m)) + 1 * t ≤ hfun X} ⊆
      {G | cmean G ⬝ᵥ cmean G ≤ (Real.sqrt m + t) ^ 2 / N ∧
        Real.sqrt N - (Real.sqrt m + t) ≤ sMin (Matrix.of G) ∧
        specNorm (Matrix.of G) ≤ Real.sqrt N + (Real.sqrt m + t)} := by
    rintro G ⟨hS, hB⟩
    have hS' : Real.sqrt N - Real.sqrt m - t ≤ sMin (Matrix.of G) ∧
        specNorm (Matrix.of G) ≤ Real.sqrt N + Real.sqrt m + t := hS
    have hlt : hfun G < (∫ Y, hfun Y ∂(gaussianMatrix N m)) + 1 * t := not_le.mp hB
    have hle : hfun G ≤ Real.sqrt m + t := by linarith
    have h0 : 0 ≤ hfun G := Real.sqrt_nonneg _
    refine ⟨?_, by linarith [hS'.1], by linarith [hS'.2]⟩
    rw [cmean_sq_eq hN G]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ h0 hle 2) hNpos.le
  have h3 : ENNReal.ofReal (3 * Real.exp (-t ^ 2 / 2)) =
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) + ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc 1 - ENNReal.ofReal (3 * Real.exp (-t ^ 2 / 2))
      = 1 - ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) - ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by
        rw [h3, tsub_tsub]
    _ ≤ (gaussianMatrix N m) {A | Real.sqrt N - Real.sqrt m - t ≤ sMin (Matrix.of A) ∧
          specNorm (Matrix.of A) ≤ Real.sqrt N + Real.sqrt m + t} -
        (gaussianMatrix N m) {X | (∫ Y, hfun Y ∂(gaussianMatrix N m)) + 1 * t ≤ hfun X} :=
        tsub_le_tsub hgood hbad
    _ ≤ (gaussianMatrix N m) ({A | Real.sqrt N - Real.sqrt m - t ≤ sMin (Matrix.of A) ∧
          specNorm (Matrix.of A) ≤ Real.sqrt N + Real.sqrt m + t} \
        {X | (∫ Y, hfun Y ∂(gaussianMatrix N m)) + 1 * t ≤ hfun X}) := le_measure_diff
    _ ≤ _ := measure_mono hsub

/-! ### Transfer to samples of `N(µ, C)` -/

/-- `A W Aᵀ` for a Gram-type matrix `W = c ∑ⱼ uⱼ uⱼᵀ`. -/
private lemma conj_gram {ι : Type} [Fintype ι] {N : ℕ} (A : Matrix ι ι ℝ) (c : ℝ)
    (u : Fin N → ι → ℝ) (a b : ι) :
    (A * (Matrix.of fun x y => c * ∑ j, u j x * u j y) * Aᵀ) a b =
      c * ∑ j, (A *ᵥ u j) a * (A *ᵥ u j) b := by
  have hL : (A * (Matrix.of fun x y => c * ∑ j, u j x * u j y) * Aᵀ) a b =
      ∑ y, (∑ x, A a x * (c * ∑ j, u j x * u j y)) * A b y := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  have hR : ∀ j, (A *ᵥ u j) a * (A *ᵥ u j) b =
      (∑ x, A a x * u j x) * ∑ y, A b y * u j y := fun j => rfl
  rw [hL]
  simp only [hR]
  calc ∑ y, (∑ x, A a x * (c * ∑ j, u j x * u j y)) * A b y
      = ∑ y, ∑ x, ∑ j, c * (A a x * (u j x * u j y) * A b y) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ y, ∑ j, ∑ x, c * (A a x * (u j x * u j y) * A b y) :=
        Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ j, ∑ y, ∑ x, c * (A a x * (u j x * u j y) * A b y) := Finset.sum_comm
    _ = c * ∑ j, (∑ x, A a x * u j x) * ∑ y, A b y * u j y := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul_sum, Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring

theorem solution {n : ℕ} (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 ≤ t)
    (μ : Fin n ⊕ Fin n → ℝ) (C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (hC : C.PosDef) :
    let χ : ℝ := Real.sqrt (2 * n) + t
    let ζ : ℝ := 2 * χ / Real.sqrt N + 2 * χ ^ 2 / N
    1 - ENNReal.ofReal (3 * Real.exp (-t ^ 2 / 2)) ≤
      (Measure.pi fun _ : Fin N => multivariateGaussian (WithLp.toLp 2 μ) C)
        {Y | let μhat : Fin n ⊕ Fin n → ℝ := fun a => (1 / (N : ℝ)) * ∑ j, WithLp.ofLp (Y j) a
              let Chat : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := Matrix.of fun a b =>
                (1 / (N : ℝ)) * ∑ j, (WithLp.ofLp (Y j) a - μhat a) * (WithLp.ofLp (Y j) b - μhat b)
              (μhat - μ) ⬝ᵥ (C⁻¹ *ᵥ (μhat - μ)) ≤ χ ^ 2 / N ∧
                (Chat - (1 - ζ) • C).PosSemidef ∧ ((1 + ζ) • C - Chat).PosSemidef} := by
  intro χ ζ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- no modes: every condition holds trivially
    have hset : {Y : Fin N → EuclideanSpace ℝ (Fin 0 ⊕ Fin 0) |
        let μhat : Fin 0 ⊕ Fin 0 → ℝ := fun a => (1 / (N : ℝ)) * ∑ j, WithLp.ofLp (Y j) a
        let Chat : Matrix (Fin 0 ⊕ Fin 0) (Fin 0 ⊕ Fin 0) ℝ := Matrix.of fun a b =>
          (1 / (N : ℝ)) * ∑ j, (WithLp.ofLp (Y j) a - μhat a) * (WithLp.ofLp (Y j) b - μhat b)
        (μhat - μ) ⬝ᵥ (C⁻¹ *ᵥ (μhat - μ)) ≤ χ ^ 2 / N ∧
          (Chat - (1 - ζ) • C).PosSemidef ∧ ((1 + ζ) • C - Chat).PosSemidef} = Set.univ := by
      ext Y
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      refine ⟨?_, ?_, ?_⟩
      · have h0 : ∀ v w : Fin 0 ⊕ Fin 0 → ℝ, v ⬝ᵥ w = 0 := fun v w => by
          simp [dotProduct]
        rw [h0]
        positivity
      · rw [Subsingleton.elim (_ - (1 - ζ) • C) 0]
        exact Matrix.PosSemidef.zero
      · rw [Subsingleton.elim ((1 + ζ) • C - _) 0]
        exact Matrix.PosSemidef.zero
    rw [hset, measure_univ]
    exact tsub_le_self
  · -- the main case
    have hm : 1 ≤ n + n := by omega
    set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv with he
    have hχ : χ = Real.sqrt ((n + n : ℕ) : ℝ) + t := by
      simp only [χ]
      congr 2
      push_cast
      ring
    have hχ0 : 0 ≤ χ := add_nonneg (Real.sqrt_nonneg _) ht
    -- the square root of the covariance
    set A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := CFC.sqrt C with hA
    have hA2 : A * A = C := CFC.sqrt_mul_sqrt_self C (Matrix.nonneg_iff_posSemidef.mpr hC.posSemidef)
    have hApsd : A.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C)
    have hAT : Aᵀ = A := by
      have h := hApsd.isHermitian
      rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    have hdetC : C.det ≠ 0 := hC.det_pos.ne'
    have hdetA : IsUnit A.det := by
      rw [isUnit_iff_ne_zero]
      intro h0
      apply hdetC
      rw [← hA2, Matrix.det_mul, h0, zero_mul]
    have hACA : Aᵀ * C⁻¹ * A = 1 := by
      rw [hAT, ← hA2, Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hdetA,
        Matrix.one_mul, Matrix.nonsing_inv_mul A hdetA]
    -- the affine map on rows and the measure identity
    set φ : (Fin (n + n) → ℝ) → EuclideanSpace ℝ (Fin n ⊕ Fin n) := fun r =>
      WithLp.toLp 2 μ + Matrix.toEuclideanCLM (𝕜 := ℝ) A (WithLp.toLp 2 (fun a => r (e a))) with hφ
    have hre : Measurable fun r : Fin (n + n) → ℝ => fun a : Fin n ⊕ Fin n => r (e a) :=
      measurable_pi_lambda _ fun a => measurable_pi_apply (e a)
    have haff : Measurable fun x : EuclideanSpace ℝ (Fin n ⊕ Fin n) =>
        WithLp.toLp 2 μ + Matrix.toEuclideanCLM (𝕜 := ℝ) A x :=
      measurable_const.add (Matrix.toEuclideanCLM (𝕜 := ℝ) A).continuous.measurable
    have hφm : Measurable φ := haff.comp ((WithLp.measurable_toLp 2 _).comp hre)
    have hreidx : (Measure.pi fun _ : Fin (n + n) => gaussianReal 0 1).map
        (fun r : Fin (n + n) → ℝ => fun a : Fin n ⊕ Fin n => r (e a)) =
        Measure.pi fun _ : Fin n ⊕ Fin n => gaussianReal 0 1 := by
      symm
      refine Measure.pi_eq fun s hs => ?_
      rw [Measure.map_apply hre (MeasurableSet.univ_pi hs)]
      have hpre : (fun r : Fin (n + n) → ℝ => fun a : Fin n ⊕ Fin n => r (e a)) ⁻¹'
          (Set.univ.pi s) = Set.univ.pi (fun k => s (e.symm k)) := by
        ext r
        simp only [Set.mem_preimage, Set.mem_univ_pi]
        constructor
        · intro h k
          simpa using h (e.symm k)
        · intro h a
          simpa using h (e a)
      rw [hpre, Measure.pi_pi]
      exact e.symm.prod_comp (fun a => gaussianReal 0 1 (s a))
    have hrow : multivariateGaussian (WithLp.toLp 2 μ) C =
        (Measure.pi fun _ : Fin (n + n) => gaussianReal 0 1).map φ := by
      unfold multivariateGaussian
      rw [← map_pi_eq_stdGaussian, ← hreidx, Measure.map_map (WithLp.measurable_toLp 2 _) hre,
        Measure.map_map haff ((WithLp.measurable_toLp 2 _).comp hre)]
      rfl
    have hprob : ∀ _ : Fin N, SigmaFinite
        (Measure.map φ (Measure.pi fun _ : Fin (n + n) => gaussianReal 0 1)) := fun _ => by
      have := Measure.isProbabilityMeasure_map (μ := Measure.pi fun _ : Fin (n + n) => gaussianReal 0 1)
        hφm.aemeasurable
      infer_instance
    have hpi : (Measure.pi fun _ : Fin N => multivariateGaussian (WithLp.toLp 2 μ) C) =
        (gaussianMatrix N (n + n)).map (fun G j => φ (G j)) := by
      rw [hrow]
      unfold gaussianMatrix
      exact (Measure.pi_map_pi (fun _ => hφm.aemeasurable)).symm
    have hΦm : Measurable fun G : Fin N → Fin (n + n) → ℝ => fun j => φ (G j) :=
      measurable_pi_lambda _ fun j => hφm.comp (measurable_pi_apply j)
    -- the event
    have hsub : {G : Fin N → Fin (n + n) → ℝ |
        cmean G ⬝ᵥ cmean G ≤ (Real.sqrt ((n + n : ℕ) : ℝ) + t) ^ 2 / N ∧
        Real.sqrt N - (Real.sqrt ((n + n : ℕ) : ℝ) + t) ≤ sMin (Matrix.of G) ∧
        specNorm (Matrix.of G) ≤ Real.sqrt N + (Real.sqrt ((n + n : ℕ) : ℝ) + t)} ⊆
        (fun G : Fin N → Fin (n + n) → ℝ => fun j => φ (G j)) ⁻¹'
        {Y | let μhat : Fin n ⊕ Fin n → ℝ := fun a => (1 / (N : ℝ)) * ∑ j, WithLp.ofLp (Y j) a
          let Chat : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := Matrix.of fun a b =>
            (1 / (N : ℝ)) * ∑ j, (WithLp.ofLp (Y j) a - μhat a) * (WithLp.ofLp (Y j) b - μhat b)
          (μhat - μ) ⬝ᵥ (C⁻¹ *ᵥ (μhat - μ)) ≤ χ ^ 2 / N ∧
            (Chat - (1 - ζ) • C).PosSemidef ∧ ((1 + ζ) • C - Chat).PosSemidef} := by
      rintro G ⟨hmean, hmin, hmax⟩
      rw [← hχ] at hmean hmin hmax
      obtain ⟨hlow, hupp⟩ := cov_bounds hN G χ hχ0 hmean hmin hmax
      -- rows indexed by quadratures
      set g : Fin N → (Fin n ⊕ Fin n) → ℝ := fun j a => G j (e a) with hg
      set gb : (Fin n ⊕ Fin n) → ℝ := fun a => cmean G (e a) with hgb
      have hY : ∀ j a, WithLp.ofLp (φ (G j)) a = μ a + (A *ᵥ g j) a := by
        intro j a
        simp only [hφ, Matrix.toEuclideanCLM_toLp, WithLp.ofLp_add, WithLp.ofLp_toLp, Pi.add_apply]
        rfl
      have hmu : (fun a => (1 / (N : ℝ)) * ∑ j, WithLp.ofLp (φ (G j)) a) = μ + A *ᵥ gb := by
        funext a
        simp only [hY, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Pi.add_apply, mul_add]
        have h1 : (1 / (N : ℝ)) * (N * μ a) = μ a := by field_simp
        have h2 : (1 / (N : ℝ)) * ∑ j, (A *ᵥ g j) a = (A *ᵥ gb) a := by
          simp only [Matrix.mulVec, dotProduct, hgb, hg, cmean]
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.mul_sum]
          ring
        rw [h1, h2]
      have hdiff : ∀ j a, WithLp.ofLp (φ (G j)) a - (μ + A *ᵥ gb) a = (A *ᵥ (g j - gb)) a := by
        intro j a
        rw [hY, Matrix.mulVec_sub]
        simp only [Pi.add_apply, Pi.sub_apply]
        ring
      have hW : (Matrix.of fun x y : Fin n ⊕ Fin n =>
          (1 / (N : ℝ)) * ∑ j, (g j - gb) x * (g j - gb) y) = (ccov G).submatrix e e := by
        ext x y
        simp only [Matrix.of_apply, Matrix.submatrix_apply, ccov, Pi.sub_apply, hg, hgb]
      have hChat : (Matrix.of fun a b : Fin n ⊕ Fin n => (1 / (N : ℝ)) * ∑ j,
          (WithLp.ofLp (φ (G j)) a - (μ + A *ᵥ gb) a) * (WithLp.ofLp (φ (G j)) b - (μ + A *ᵥ gb) b)) =
          A * (ccov G).submatrix e e * Aᵀ := by
        ext a b
        rw [← hW, conj_gram]
        simp only [Matrix.of_apply, hdiff]
      have hC' : C = A * (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) * Aᵀ := by
        rw [Matrix.mul_one, hAT, hA2]
      have hζ : ζ = 2 * χ / Real.sqrt N + 2 * χ ^ 2 / N := rfl
      have hAH : Aᴴ = Aᵀ := Matrix.conjTranspose_eq_transpose_of_trivial A
      have hone : (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ).submatrix e e = 1 :=
        Matrix.submatrix_one_equiv e
      have key : ∀ mh : Fin n ⊕ Fin n → ℝ, mh = μ + A *ᵥ gb →
          (mh - μ) ⬝ᵥ (C⁻¹ *ᵥ (mh - μ)) ≤ χ ^ 2 / N ∧
          ((Matrix.of fun a b : Fin n ⊕ Fin n => (1 / (N : ℝ)) * ∑ j,
            (WithLp.ofLp (φ (G j)) a - mh a) * (WithLp.ofLp (φ (G j)) b - mh b)) -
              (1 - ζ) • C).PosSemidef ∧
          ((1 + ζ) • C - (Matrix.of fun a b : Fin n ⊕ Fin n => (1 / (N : ℝ)) * ∑ j,
            (WithLp.ofLp (φ (G j)) a - mh a) * (WithLp.ofLp (φ (G j)) b - mh b))).PosSemidef := by
        intro mh hmh
        subst hmh
        rw [hChat]
        refine ⟨?_, ?_, ?_⟩
        · rw [add_sub_cancel_left]
          have hadj : ∀ w : Fin n ⊕ Fin n → ℝ, (A *ᵥ gb) ⬝ᵥ w = gb ⬝ᵥ (Aᵀ *ᵥ w) := fun w => by
            rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
          have h1 : (A *ᵥ gb) ⬝ᵥ (C⁻¹ *ᵥ (A *ᵥ gb)) = gb ⬝ᵥ gb := by
            rw [hadj, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hACA, Matrix.one_mulVec]
          have h2 : gb ⬝ᵥ gb = cmean G ⬝ᵥ cmean G := by
            simp only [dotProduct, hgb]
            exact e.sum_comp (fun k => cmean G k * cmean G k)
          rw [h1, h2]
          exact hmean
        · have e1 : A * (ccov G).submatrix e e * Aᵀ - (1 - ζ) • C =
              A * ((ccov G - (1 - ζ) • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ)).submatrix e e) *
                Aᴴ := by
            have e2 : (ccov G - (1 - ζ) • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ)).submatrix e e =
                (ccov G).submatrix e e - (1 - ζ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by
              rw [← hone]
              rfl
            rw [e2, hAH, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, ← hC']
          rw [e1]
          rw [← hζ] at hlow
          exact (hlow.submatrix e).mul_mul_conjTranspose_same A
        · have e1 : (1 + ζ) • C - A * (ccov G).submatrix e e * Aᵀ =
              A * (((1 + ζ) • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) - ccov G).submatrix e e) *
                Aᴴ := by
            have e2 : ((1 + ζ) • (1 : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) - ccov G).submatrix e e =
                (1 + ζ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) - (ccov G).submatrix e e := by
              rw [← hone]
              rfl
            rw [e2, hAH, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, ← hC']
          rw [e1]
          rw [← hζ] at hupp
          exact (hupp.submatrix e).mul_mul_conjTranspose_same A
      exact key _ hmu
    rw [hpi]
    exact (std_event hN hm t ht).trans
      ((measure_mono hsub).trans (Measure.le_map_apply hΦm.aemeasurable _))
