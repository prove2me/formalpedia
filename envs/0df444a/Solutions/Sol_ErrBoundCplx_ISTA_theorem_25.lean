-- Prove2me | solution 1 for ErrBoundCplx.ISTA.theorem_25
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T18:01:17.228989+00:00
-- url     : https://prove2.me/submissions/6b6e4589-c9a6-4380-a084-756c5d7781e5

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic
import Definitions.Def_ErrBoundCplx_ISTA_Lasso

set_option autoImplicit false

open scoped Matrix

namespace ISTA25Aux

open Filter Topology
open BoydADMM.Prox ErrBoundCplx.ISTA

lemma r_step (r e : ℕ → ℝ) (a b γ : ℝ) (ha : 0 < a) (hb : 0 < b) (hγ : 0 < γ)
    (hsd : ∀ k, r (k+1) + a * e k ^ 2 ≤ r k)
    (hkl : ∀ k, 2 * γ * r (k+1) ≤ b ^ 2 * e k ^ 2) (k : ℕ) :
    (1 + 2 * a * γ / b ^ 2) * r (k+1) ≤ r k := by
  have h1 := hsd k
  have h2 := mul_le_mul_of_nonneg_left (hkl k) ha.le
  have hb2 : 0 < b ^ 2 := by positivity
  have : 2 * a * γ / b ^ 2 * r (k+1) ≤ a * e k ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hb2]
    nlinarith
  nlinarith

lemma r_geom (r e : ℕ → ℝ) (a b γ : ℝ) (ha : 0 < a) (hb : 0 < b) (hγ : 0 < γ)
    (hsd : ∀ k, r (k+1) + a * e k ^ 2 ≤ r k)
    (hkl : ∀ k, 2 * γ * r (k+1) ≤ b ^ 2 * e k ^ 2) (k : ℕ) :
    r k ≤ r 0 / (1 + 2 * a * γ / b ^ 2) ^ k := by
  have hq : 0 < 1 + 2 * a * γ / b ^ 2 := by positivity
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← div_div, le_div_iff₀ hq]
    have := r_step r e a b γ ha hb hγ hsd hkl k
    linarith [mul_comm (r (k+1)) (1 + 2*a*γ/b^2)]

/-- the one-step length inequality -/
lemma e_step (r e : ℕ → ℝ) (a b γ t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (ht2 : t ^ 2 = 2 * γ) (hr : ∀ k, 0 ≤ r k) (he : ∀ k, 0 ≤ e k)
    (hsd : ∀ k, r (k+1) + a * e k ^ 2 ≤ r k)
    (hkl : ∀ k, 2 * γ * r (k+1) ≤ b ^ 2 * e k ^ 2) (k : ℕ) :
    2 * e (k+1) ≤ e k + 2 * b / (a * t) *
      (Real.sqrt (r (k+1)) - Real.sqrt (r (k+2))) := by
  set s1 := Real.sqrt (r (k+1)) with hs1
  set s2 := Real.sqrt (r (k+2)) with hs2
  have hs1sq : s1 ^ 2 = r (k+1) := Real.sq_sqrt (hr _)
  have hs2sq : s2 ^ 2 = r (k+2) := Real.sq_sqrt (hr _)
  have hs1n : 0 ≤ s1 := Real.sqrt_nonneg _
  have hs2n : 0 ≤ s2 := Real.sqrt_nonneg _
  have hdec : r (k+2) ≤ r (k+1) := by nlinarith [hsd (k+1), he (k+1)]
  have hs21 : s2 ≤ s1 := Real.sqrt_le_sqrt hdec
  -- t s1 ≤ b e_k
  have hts1 : t * s1 ≤ b * e k := by
    have h := hkl k
    have h2 : (t * s1) ^ 2 ≤ (b * e k) ^ 2 := by
      rw [mul_pow, mul_pow, ht2, hs1sq]; exact h
    exact (pow_le_pow_iff_left₀ (by positivity) (mul_nonneg hb.le (he k)) two_ne_zero).1 h2
  set Y := 2 * b / (a * t) * (s1 - s2) with hY
  have hY0 : 0 ≤ Y := by
    have : 0 ≤ s1 - s2 := by linarith
    positivity
  have hkey : a * t * e (k+1) ^ 2 ≤ a * t * (e k * Y) := by
    have h1 : a * e (k+1) ^ 2 ≤ 2 * s1 * (s1 - s2) := by
      have := hsd (k+1)
      have : k + 1 + 1 = k + 2 := rfl
      nlinarith
    have h3 : a * t * (e k * Y) = 2 * (b * e k) * (s1 - s2) := by
      rw [hY]; field_simp
    rw [h3]
    have : 0 ≤ s1 - s2 := by linarith
    nlinarith
  have hsq : e (k+1) ^ 2 ≤ e k * Y := le_of_mul_le_mul_left hkey (by positivity)
  nlinarith [sq_nonneg (e k - Y), he k, he (k+1)]

lemma e_sum (r e : ℕ → ℝ) (a b γ t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (ht2 : t ^ 2 = 2 * γ) (hr : ∀ k, 0 ≤ r k) (he : ∀ k, 0 ≤ e k)
    (hsd : ∀ k, r (k+1) + a * e k ^ 2 ≤ r k)
    (hkl : ∀ k, 2 * γ * r (k+1) ≤ b ^ 2 * e k ^ 2) (k N : ℕ) :
    ∑ j ∈ Finset.range (N+1), e (k+1+j) ≤ e k - e (k+1+N) + 2 * b / (a * t) *
      (Real.sqrt (r (k+1)) - Real.sqrt (r (k+2+N))) := by
  induction N with
  | zero =>
    have := e_step r e a b γ t ha hb ht ht2 hr he hsd hkl k
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, add_zero]
    linarith
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have := e_step r e a b γ t ha hb ht ht2 hr he hsd hkl (k+1+N)
    rw [show k + 1 + N + 1 = k + 1 + (N + 1) by ring,
      show k + 1 + N + 2 = k + 2 + (N + 1) by ring] at this
    rw [show k + 2 + N = k + 1 + (N + 1) by ring] at ih
    nlinarith

lemma e_tail (r e : ℕ → ℝ) (a b γ t : ℝ) (ha : 0 < a) (hb : 0 < b) (hγ : 0 < γ) (ht : 0 < t)
    (ht2 : t ^ 2 = 2 * γ) (hr : ∀ k, 0 ≤ r k) (he : ∀ k, 0 ≤ e k)
    (hsd : ∀ k, r (k+1) + a * e k ^ 2 ≤ r k)
    (hkl : ∀ k, 2 * γ * r (k+1) ≤ b ^ 2 * e k ^ 2) (k N : ℕ) :
    ∑ j ∈ Finset.range N, e (k+1+j) ≤
      (1 / Real.sqrt a + 2 * b / (a * t) / Real.sqrt (1 + 2 * a * γ / b ^ 2)) *
        Real.sqrt (r k) := by
  set q := 1 + 2 * a * γ / b ^ 2 with hq
  have hq0 : 0 < q := by positivity
  have hM : 0 ≤ 2 * b / (a * t) := by positivity
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  -- e k ≤ sqrt (r k) / sqrt a
  have hek : e k ≤ Real.sqrt (r k) / Real.sqrt a := by
    rw [le_div_iff₀ hsa]
    have h1 : a * e k ^ 2 ≤ r k := by nlinarith [hsd k, hr (k+1)]
    have h2 : (e k * Real.sqrt a) ^ 2 ≤ (Real.sqrt (r k)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt (hr k)]; nlinarith
    exact (pow_le_pow_iff_left₀ (mul_nonneg (he k) hsa.le) (Real.sqrt_nonneg _) two_ne_zero).1 h2
  have hrk : Real.sqrt (r (k+1)) ≤ Real.sqrt (r k) / Real.sqrt q := by
    rw [le_div_iff₀ hsq, ← Real.sqrt_mul (hr _)]
    apply Real.sqrt_le_sqrt
    have := r_step r e a b γ ha hb hγ hsd hkl k
    linarith [mul_comm q (r (k+1))]
  have hsum : ∑ j ∈ Finset.range N, e (k+1+j) ≤
      e k + 2 * b / (a * t) * Real.sqrt (r (k+1)) := by
    rcases N with _ | N
    · simp only [Finset.range_zero, Finset.sum_empty]
      exact add_nonneg (he k) (mul_nonneg hM (Real.sqrt_nonneg _))
    · have := e_sum r e a b γ t ha hb ht ht2 hr he hsd hkl k N
      have := he (k+1+N)
      have := Real.sqrt_nonneg (r (k+2+N))
      nlinarith
  calc ∑ j ∈ Finset.range N, e (k+1+j) ≤ e k + 2 * b / (a * t) * Real.sqrt (r (k+1)) := hsum
    _ ≤ Real.sqrt (r k) / Real.sqrt a + 2 * b / (a * t) * (Real.sqrt (r k) / Real.sqrt q) := by
        gcongr
    _ = _ := by ring

lemma sqrt_geom (r0 q : ℝ) (hq : 0 < q) (hr0 : 0 ≤ r0) (k : ℕ) :
    Real.sqrt (r0 / q ^ k) = Real.sqrt r0 / q ^ ((k : ℝ) / 2) := by
  rw [Real.sqrt_div' _ (by positivity)]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]
  ring_nf

lemma C_eq (a b γ : ℝ) (ha : 0 < a) (hb : 0 < b) (hγ : 0 < γ) :
    1 / Real.sqrt a * (1 + 1 / (a * b⁻¹ ^ 2 * γ * Real.sqrt (1 + 1 / (2 * a * b⁻¹ ^ 2 * γ)))) =
      1 / Real.sqrt a + 2 * b / (a * Real.sqrt (2 * γ)) / Real.sqrt (1 + 2 * a * γ / b ^ 2) := by
  set u := Real.sqrt a with hu
  set v := Real.sqrt (2 * γ) with hv
  set w := Real.sqrt (1 + 2 * a * γ / b ^ 2) with hw
  have hu0 : 0 < u := Real.sqrt_pos.2 ha
  have hv0 : 0 < v := Real.sqrt_pos.2 (by positivity)
  have hw0 : 0 < w := Real.sqrt_pos.2 (by positivity)
  have hu2 : u ^ 2 = a := Real.sq_sqrt ha.le
  have hv2 : v ^ 2 = 2 * γ := Real.sq_sqrt (by positivity)
  have hw2 : w ^ 2 = 1 + 2 * a * γ / b ^ 2 := Real.sq_sqrt (by positivity)
  have key : Real.sqrt (1 + 1 / (2 * a * b⁻¹ ^ 2 * γ)) = w * b / (u * v) := by
    rw [show 1 + 1 / (2 * a * b⁻¹ ^ 2 * γ) = (w * b / (u * v)) ^ 2 by
      rw [div_pow, mul_pow, mul_pow, hu2, hv2, hw2]; field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  have hγ' : γ = v ^ 2 / 2 := by linarith
  rw [key, ← hu2, hγ']
  field_simp

lemma adj {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin m))
    (z : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (Matrix.toEuclideanLin Aᵀ y) z = inner ℝ y (Matrix.toEuclideanLin A z) := by
  have h : Aᵀ = Aᴴ := (Matrix.conjTranspose_eq_transpose_of_trivial A).symm
  rw [h, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]

lemma mulT {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (Aᵀ * A) z = Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin A z) := by
  ext i
  simp [Matrix.toEuclideanLin, Matrix.mulVec_mulVec]

lemma Mzz {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (Matrix.toEuclideanLin (Aᵀ * A) z) z = ‖Matrix.toEuclideanLin A z‖ ^ 2 := by
  rw [mulT, adj, real_inner_self_eq_norm_sq]

lemma Mle {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin (Aᵀ * A) z‖ ≤ specNorm (Aᵀ * A) * ‖z‖ := by
  unfold specNorm
  exact (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (Aᵀ * A))).le_opNorm z

lemma Tsq_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin A z‖ ^ 2 ≤ specNorm (Aᵀ * A) * ‖z‖ ^ 2 := by
  rw [← Mzz]
  calc inner ℝ (Matrix.toEuclideanLin (Aᵀ * A) z) z ≤ ‖Matrix.toEuclideanLin (Aᵀ * A) z‖ * ‖z‖ :=
        real_inner_le_norm _ _
    _ ≤ specNorm (Aᵀ * A) * ‖z‖ * ‖z‖ := by gcongr; exact Mle A z
    _ = _ := by ring

lemma h_expand {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin m))
    (p z : EuclideanSpace ℝ (Fin n)) :
    1 / 2 * ‖Matrix.toEuclideanLin A (p + z) - d‖ ^ 2 =
      1 / 2 * ‖Matrix.toEuclideanLin A p - d‖ ^ 2 +
      inner ℝ (Matrix.toEuclideanLin (Aᵀ * A) p - Matrix.toEuclideanLin Aᵀ d) z +
      1 / 2 * ‖Matrix.toEuclideanLin A z‖ ^ 2 := by
  rw [map_add, show Matrix.toEuclideanLin A p + Matrix.toEuclideanLin A z - d =
      (Matrix.toEuclideanLin A p - d) + Matrix.toEuclideanLin A z by abel, norm_add_sq_real,
    mulT, ← map_sub, adj]
  ring

lemma l1_convex {n : ℕ} (p u : EuclideanSpace ℝ (Fin n)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    l1Norm (p + t • (u - p)) ≤ (1 - t) * l1Norm p + t * l1Norm u := by
  unfold l1Norm
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  calc |p i + t * (u i - p i)| = |(1 - t) * p i + t * u i| := by ring_nf
    _ ≤ |(1 - t) * p i| + |t * u i| := abs_add_le _ _
    _ = (1 - t) * |p i| + t * |u i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - t), abs_of_nonneg ht0]

lemma l1_nonneg {n : ℕ} (p : EuclideanSpace ℝ (Fin n)) : 0 ≤ l1Norm p :=
  Finset.sum_nonneg (fun i _ => abs_nonneg _)

lemma prox_subgrad {n : ℕ} (c : ℝ) (hc : 0 ≤ c) (v p : EuclideanSpace ℝ (Fin n))
    (h : IsProx Set.univ (fun z => c * l1Norm z) 1 v p) (u : EuclideanSpace ℝ (Fin n)) :
    c * l1Norm p + inner ℝ (v - p) (u - p) ≤ c * l1Norm u := by
  set D := c * l1Norm p + inner ℝ (v - p) (u - p) - c * l1Norm u with hD
  set K := ‖u - p‖ ^ 2 / 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → D ≤ t * K := by
    intro t ht0 ht1
    have h2 := h.2 (p + t • (u - p)) trivial
    have hc1 := mul_le_mul_of_nonneg_left (l1_convex p u t ht0.le ht1) hc
    have hn : ‖p + t • (u - p) - v‖ ^ 2 =
        ‖p - v‖ ^ 2 + 2 * t * inner ℝ (p - v) (u - p) + t ^ 2 * ‖u - p‖ ^ 2 := by
      rw [show p + t • (u - p) - v = (p - v) + t • (u - p) by abel, norm_add_sq_real,
        inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    simp only at h2
    rw [hn] at h2
    have hi : inner ℝ (v - p) (u - p) = - inner ℝ (p - v) (u - p) := by
      rw [← inner_neg_left, neg_sub]
    rw [hD, hK, hi]
    nlinarith
  by_contra hcon'
  have hcon : 0 < D := by rw [hD]; linarith [not_le.1 hcon']
  set t := min 1 (D / (K + 1)) with ht
  have ht0 : 0 < t := lt_min one_pos (div_pos hcon (by linarith))
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ D / (K + 1) := min_le_right _ _
  have := key t ht0 ht1
  have h3 : t * (K + 1) ≤ D := by rwa [le_div_iff₀ (by linarith)] at ht2
  nlinarith

lemma g_sub {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin m)) (μ : ℝ)
    (hμ : 0 < μ) (lam : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsISTASeq A d μ lam x)
    (k : ℕ) (hl : 0 < lam k) (u : EuclideanSpace ℝ (Fin n)) :
    μ * l1Norm (x (k+1)) - 1 / lam k * inner ℝ (x (k+1) - x k) (u - x (k+1)) -
      inner ℝ (Matrix.toEuclideanLin (Aᵀ * A) (x k) - Matrix.toEuclideanLin Aᵀ d) (u - x (k+1))
      ≤ μ * l1Norm u := by
  have h := prox_subgrad (lam k * μ) (by positivity) _ _ (hx k) u
  set G := Matrix.toEuclideanLin (Aᵀ * A) (x k) - Matrix.toEuclideanLin Aᵀ d with hG
  have e : x k - lam k • G - x (k+1) = -(x (k+1) - x k) - lam k • G := by abel
  rw [e, inner_sub_left, inner_neg_left, real_inner_smul_left] at h
  have h2 : lam k * (μ * l1Norm (x (k+1)) - 1 / lam k * inner ℝ (x (k+1) - x k) (u - x (k+1)) -
      inner ℝ G (u - x (k+1))) ≤ lam k * (μ * l1Norm u) := by
    have : lam k * (μ * l1Norm (x (k+1)) - 1 / lam k * inner ℝ (x (k+1) - x k) (u - x (k+1)) -
      inner ℝ G (u - x (k+1))) = lam k * μ * l1Norm (x (k+1)) +
        (-inner ℝ (x (k+1) - x k) (u - x (k+1)) - lam k * inner ℝ G (u - x (k+1))) := by
      field_simp
      ring
    rw [this]; linarith
  exact le_of_mul_le_mul_left h2 hl

lemma f_sub {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin m)) (μ : ℝ)
    (hμ : 0 < μ) (lam : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsISTASeq A d μ lam x)
    (k : ℕ) (hl : 0 < lam k) (u : EuclideanSpace ℝ (Fin n)) :
    lassoObj A d μ (x (k+1)) + inner ℝ (Matrix.toEuclideanLin (Aᵀ * A) (x (k+1) - x k) -
      (1 / lam k) • (x (k+1) - x k)) (u - x (k+1)) ≤ lassoObj A d μ u := by
  have hg := g_sub A d μ hμ lam x hx k hl u
  have hh := h_expand A d (x (k+1)) (u - x (k+1))
  rw [add_sub_cancel] at hh
  unfold lassoObj
  rw [hh, inner_sub_left, real_inner_smul_left, map_sub]
  have : inner ℝ (Matrix.toEuclideanLin (Aᵀ * A) (x (k+1)) - Matrix.toEuclideanLin Aᵀ d)
      (u - x (k+1)) = inner ℝ (Matrix.toEuclideanLin (Aᵀ * A) (x (k+1)) -
        Matrix.toEuclideanLin (Aᵀ * A) (x k)) (u - x (k+1)) +
      inner ℝ (Matrix.toEuclideanLin (Aᵀ * A) (x k) - Matrix.toEuclideanLin Aᵀ d)
        (u - x (k+1)) := by
    rw [← inner_add_left]; congr 1; abel
  rw [this]
  have : 0 ≤ ‖Matrix.toEuclideanLin A (u - x (k+1))‖ ^ 2 := by positivity
  linarith

lemma f_sd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin m)) (μ : ℝ)
    (hμ : 0 < μ) (lam : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsISTASeq A d μ lam x)
    (k : ℕ) (hl : 0 < lam k) :
    lassoObj A d μ (x (k+1)) + (1 / lam k - specNorm (Aᵀ * A) / 2) * ‖x (k+1) - x k‖ ^ 2
      ≤ lassoObj A d μ (x k) := by
  have hg := g_sub A d μ hμ lam x hx k hl (x k)
  have hh := h_expand A d (x k) (x (k+1) - x k)
  rw [add_sub_cancel] at hh
  have hT := Tsq_le A (x (k+1) - x k)
  have e1 : x k - x (k+1) = -(x (k+1) - x k) := by abel
  rw [e1, inner_neg_right, inner_neg_right, real_inner_self_eq_norm_sq] at hg
  unfold lassoObj
  rw [hh]
  nlinarith

lemma w_norm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (lk : ℝ) (hl : 0 < lk)
    (z : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin (Aᵀ * A) z - (1 / lk) • z‖ ≤ (1 / lk + specNorm (Aᵀ * A)) * ‖z‖ := by
  calc _ ≤ ‖Matrix.toEuclideanLin (Aᵀ * A) z‖ + ‖(1 / lk) • z‖ := norm_sub_le _ _
    _ ≤ specNorm (Aᵀ * A) * ‖z‖ + 1 / lk * ‖z‖ := by
        gcongr
        · exact Mle A z
        · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    _ = _ := by ring

lemma l1_ge_norm {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) : ‖y‖ ≤ l1Norm y := by
  have h1 : ‖y‖ ^ 2 ≤ l1Norm y ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    unfold l1Norm
    have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |y i|)
      (fun i _ => abs_nonneg _)
    simpa [Real.norm_eq_abs, sq_abs] using this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (l1_nonneg y) two_ne_zero).1 h1

lemma f_cont {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin m)) (μ : ℝ) :
    Continuous (lassoObj A d μ) := by
  unfold lassoObj l1Norm
  have hT : Continuous (Matrix.toEuclideanLin A) := LinearMap.continuous_of_finiteDimensional _
  fun_prop

lemma mu_l1_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin m)) (μ : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : μ * l1Norm y ≤ lassoObj A d μ y := by
  unfold lassoObj
  have : 0 ≤ ‖Matrix.toEuclideanLin A y - d‖ ^ 2 := by positivity
  linarith

lemma exists_min {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin m)) (μ : ℝ)
    (hμ : 0 < μ) : ∃ xh, ∀ y, lassoObj A d μ xh ≤ lassoObj A d μ y := by
  set K := {y : EuclideanSpace ℝ (Fin n) | lassoObj A d μ y ≤ lassoObj A d μ 0} with hK
  have hcl : IsClosed K := isClosed_le (f_cont A d μ) continuous_const
  have hbd : Bornology.IsBounded K := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨lassoObj A d μ 0 / μ, fun y hy => ?_⟩
    rw [le_div_iff₀ hμ]
    have := mu_l1_le A d μ y
    have := l1_ge_norm y
    have hy' : lassoObj A d μ y ≤ lassoObj A d μ 0 := hy
    nlinarith
  have hc : IsCompact K := Metric.isCompact_of_isClosed_isBounded hcl hbd
  obtain ⟨xh, hxK, hmin⟩ := hc.exists_isMinOn ⟨0, show lassoObj A d μ 0 ≤ lassoObj A d μ 0 from le_refl _⟩ (f_cont A d μ).continuousOn
  refine ⟨xh, fun y => ?_⟩
  by_cases hy : y ∈ K
  · exact hmin hy
  · have h0 : lassoObj A d μ xh ≤ lassoObj A d μ 0 := hxK
    have : lassoObj A d μ 0 < lassoObj A d μ y := lt_of_not_ge hy
    linarith

lemma min_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (d : EuclideanSpace ℝ (Fin m)) (μ : ℝ)
    (xh : EuclideanSpace ℝ (Fin n)) (h : ∀ y, lassoObj A d μ xh ≤ lassoObj A d μ y) :
    lassoMin A d μ = lassoObj A d μ xh := by
  unfold lassoMin
  apply le_antisymm
  · exact ciInf_le ⟨lassoObj A d μ xh, by rintro _ ⟨y, rfl⟩; exact h y⟩ xh
  · exact le_ciInf h

lemma kl_point {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (S : Set (EuclideanSpace ℝ (Fin n)))
    (fmin γ : ℝ) (hγ : 0 < γ) (xh : EuclideanSpace ℝ (Fin n)) (hxh : xh ∈ S)
    (hS : ∀ y ∈ S, f y = fmin) (hge : ∀ y, fmin ≤ f y)
    (p w : EuclideanSpace ℝ (Fin n)) (hsub : ∀ u, f p + inner ℝ w (u - p) ≤ f u)
    (hEB : 2 * γ * Metric.infDist p S ^ 2 ≤ f p - fmin) :
    2 * γ * (f p - fmin) ≤ ‖w‖ ^ 2 := by
  set r := f p - fmin with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith [hge p]
  have hI0 : 0 ≤ Metric.infDist p S := Metric.infDist_nonneg
  have hrw : r ≤ ‖w‖ * Metric.infDist p S := by
    rcases eq_or_lt_of_le (norm_nonneg w) with h0 | hpos
    · have hw : w = 0 := norm_eq_zero.1 h0.symm
      have := hsub xh
      rw [hS xh hxh, hw, inner_zero_left] at this
      rw [hw, norm_zero, zero_mul]; linarith
    · rw [mul_comm, ← div_le_iff₀ hpos]
      rw [Metric.le_infDist ⟨xh, hxh⟩]
      intro y hy
      rw [div_le_iff₀ hpos]
      have h1 := hsub y
      rw [hS y hy] at h1
      have h2 : inner ℝ w (y - p) ≥ -(‖w‖ * dist p y) := by
        rw [dist_eq_norm, ← norm_neg (p - y), neg_sub]
        have := abs_real_inner_le_norm w (y - p)
        linarith [neg_abs_le (inner ℝ w (y - p))]
      nlinarith
  have hsq : r ^ 2 ≤ ‖w‖ ^ 2 * Metric.infDist p S ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hr0 hrw 2
  have h3 : 2 * γ * r ^ 2 ≤ ‖w‖ ^ 2 * r := by
    have := mul_le_mul_of_nonneg_left hEB (sq_nonneg ‖w‖)
    nlinarith
  rcases eq_or_lt_of_le hr0 with h0 | hpos
  · rw [← h0]; simp
  · nlinarith

end ISTA25Aux

open ISTA25Aux in
open BoydADMM.Prox Filter Topology ErrBoundCplx.ISTA in open scoped Matrix in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m)) (μ : ℝ) (hμ : 0 < μ)
    (lam : ℕ → ℝ) (lamMinus lamPlus : ℝ) (hlm : 0 < lamMinus)
    (hlo : ∀ k, lamMinus ≤ lam k) (hhi : ∀ k, lam k ≤ lamPlus)
    (hLp : lamPlus * specNorm (Aᵀ * A) < 2)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsISTASeq A d μ lam x)
    (γR : ℝ) (hγ : 0 < γR)
    (hEB : ∀ y : EuclideanSpace ℝ (Fin n),
      l1Norm y ≤ max (lassoObj A d μ (x 0) / μ) (1 + ‖d‖ ^ 2 / (2 * μ)) →
      2 * γR * Metric.infDist y (lassoArgmin A d μ) ^ 2 ≤ lassoObj A d μ y - lassoMin A d μ) :
    let L : ℝ := specNorm (Aᵀ * A)
    let a : ℝ := 1 / lamPlus - L / 2
    let b : ℝ := 1 / lamMinus + L
    let q : ℝ := 1 + 2 * a * γR / b ^ 2
    let C : ℝ := 1 / Real.sqrt a *
      (1 + 1 / (a * b⁻¹ ^ 2 * γR * Real.sqrt (1 + 1 / (2 * a * b⁻¹ ^ 2 * γR))))
    ∃ xstar ∈ lassoArgmin A d μ, Tendsto x atTop (𝓝 xstar) ∧
      (∀ k : ℕ, lassoObj A d μ (x k) - lassoMin A d μ ≤
        (lassoObj A d μ (x 0) - lassoMin A d μ) / q ^ k) ∧
      ∀ k : ℕ, 1 ≤ k → ‖x k - xstar‖ ≤
        C * Real.sqrt (lassoObj A d μ (x 0) - lassoMin A d μ) / q ^ (((k : ℝ) - 1) / 2) := by
  intro L a b q C
  have hL0 : 0 ≤ L := norm_nonneg _
  have hlk : ∀ k, 0 < lam k := fun k => lt_of_lt_of_le hlm (hlo k)
  have hlp : 0 < lamPlus := lt_of_lt_of_le (hlk 0) (hhi 0)
  have ha : 0 < a := by
    show 0 < 1 / lamPlus - L / 2
    have : L / 2 < 1 / lamPlus := by
      rw [div_lt_div_iff₀ two_pos hlp]
      have : lamPlus * L < 2 := hLp
      linarith [mul_comm L lamPlus]
    linarith
  have hb : 0 < b := add_pos_of_pos_of_nonneg (by positivity) hL0
  have hcpos : 0 < 2 * a * γR / b ^ 2 := div_pos (mul_pos (mul_pos two_pos ha) hγ) (pow_pos hb 2)
  have hq0 : 0 < q := by show 0 < 1 + 2 * a * γR / b ^ 2; linarith
  have hq1 : 1 < q := by show 1 < 1 + 2 * a * γR / b ^ 2; linarith
  obtain ⟨xh, hxh⟩ := exists_min A d μ hμ
  have hmin := min_eq A d μ xh hxh
  have hxhS : xh ∈ lassoArgmin A d μ := by show lassoObj A d μ xh = lassoMin A d μ; exact hmin.symm
  have hge : ∀ y, lassoMin A d μ ≤ lassoObj A d μ y := fun y => by rw [hmin]; exact hxh y
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℝ, ∀ k, r k = lassoObj A d μ (x k) - lassoMin A d μ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ, ∀ k, e k = ‖x (k+1) - x k‖ := ⟨_, fun _ => rfl⟩
  have hr0 : ∀ k, 0 ≤ r k := fun k => by rw [hr]; linarith [hge (x k)]
  have he0 : ∀ k, 0 ≤ e k := fun k => by rw [he]; exact norm_nonneg _
  have hsd : ∀ k, r (k+1) + a * e k ^ 2 ≤ r k := by
    intro k
    have h1 := f_sd A d μ hμ lam x hx k (hlk k)
    have h2 : a ≤ 1 / lam k - L / 2 := by
      show 1 / lamPlus - L / 2 ≤ 1 / lam k - L / 2
      have := one_div_le_one_div_of_le (hlk k) (hhi k)
      linarith
    have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖x (k+1) - x k‖)
    rw [hr, hr, he]
    have : (1 / lam k - specNorm (Aᵀ * A) / 2) = 1 / lam k - L / 2 := rfl
    rw [this] at h1
    linarith
  have hmono : ∀ k, lassoObj A d μ (x k) ≤ lassoObj A d μ (x 0) := by
    intro k
    induction k with
    | zero => exact le_refl _
    | succ k ih =>
      have := hsd k
      have := he0 k
      rw [hr, hr] at *
      nlinarith [mul_nonneg ha.le (sq_nonneg (e k))]
  have hkl : ∀ k, 2 * γR * r (k+1) ≤ b ^ 2 * e k ^ 2 := by
    intro k
    have hball : l1Norm (x (k+1)) ≤ max (lassoObj A d μ (x 0) / μ) (1 + ‖d‖ ^ 2 / (2 * μ)) := by
      apply le_max_of_le_left
      rw [le_div_iff₀ hμ]
      have := mu_l1_le A d μ (x (k+1))
      have := hmono (k+1)
      linarith [mul_comm μ (l1Norm (x (k+1)))]
    have hk := kl_point (lassoObj A d μ) (lassoArgmin A d μ) (lassoMin A d μ) γR hγ xh hxhS
      (fun y hy => hy) hge (x (k+1)) _ (fun u => f_sub A d μ hμ lam x hx k (hlk k) u)
      (hEB (x (k+1)) hball)
    have hw := w_norm A (lam k) (hlk k) (x (k+1) - x k)
    have hwb : (1 / lam k + specNorm (Aᵀ * A)) * ‖x (k+1) - x k‖ ≤ b * e k := by
      rw [he]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      show 1 / lam k + L ≤ 1 / lamMinus + L
      have := one_div_le_one_div_of_le hlm (hlo k)
      linarith
    have hw2 := pow_le_pow_left₀ (norm_nonneg _) (hw.trans hwb) 2
    rw [hr]
    nlinarith
  have h36 : ∀ k, r k ≤ r 0 / q ^ k := fun k => r_geom r e a b γR ha hb hγ hsd hkl k
  set t := Real.sqrt (2 * γR) with ht
  have ht0 : 0 < t := Real.sqrt_pos.2 (by positivity)
  have ht2 : t ^ 2 = 2 * γR := Real.sq_sqrt (by positivity)
  have htail := fun k N => e_tail r e a b γR t ha hb hγ ht0 ht2 hr0 he0 hsd hkl k N
  set K := 1 / Real.sqrt a + 2 * b / (a * t) / Real.sqrt (1 + 2 * a * γR / b ^ 2) with hK
  have hK0 : 0 ≤ K := add_nonneg (by positivity)
    (div_nonneg (div_nonneg (by linarith) (mul_nonneg ha.le ht0.le)) (Real.sqrt_nonneg _))
  have hsum : Summable e := by
    refine summable_of_sum_range_le he0 (c := e 0 + K * Real.sqrt (r 0)) (fun N => ?_)
    have h1 : ∑ i ∈ Finset.range N, e i ≤ ∑ i ∈ Finset.range (N+1), e i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ N))
        (fun i _ _ => he0 i)
    rw [Finset.sum_range_succ'] at h1
    have h2 := htail 0 N
    have h3 : ∑ i ∈ Finset.range N, e (i + 1) = ∑ j ∈ Finset.range N, e (0 + 1 + j) :=
      Finset.sum_congr rfl (fun j _ => by rw [zero_add, add_comm])
    linarith
  have hdist : ∀ k, dist (x k) (x k.succ) ≤ e k := fun k => by
    rw [dist_comm, dist_eq_norm, he]
  have hcauchy : CauchySeq x :=
    cauchySeq_of_summable_dist (Summable.of_nonneg_of_le (fun _ => dist_nonneg) hdist hsum)
  obtain ⟨xs, hxs⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨xs, ?_, hxs, fun k => by rw [← hr, ← hr]; exact h36 k, ?_⟩
  · show lassoObj A d μ xs = lassoMin A d μ
    have hcont : Tendsto (fun k => lassoObj A d μ (x k)) atTop (𝓝 (lassoObj A d μ xs)) :=
      ((f_cont A d μ).tendsto xs).comp hxs
    have hup : Tendsto (fun k : ℕ => lassoMin A d μ + r 0 / q ^ k) atTop (𝓝 (lassoMin A d μ)) := by
      have := tendsto_const_nhds (x := r 0) |>.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hq1)
      simpa using (tendsto_const_nhds (x := lassoMin A d μ)).add this
    apply le_antisymm _ (hge xs)
    refine le_of_tendsto_of_tendsto' hcont hup (fun k => ?_)
    have := h36 k
    rw [hr] at this
    linarith
  · intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h1 := dist_le_tsum_of_dist_le_of_tendsto e hdist hsum hxs (j+1)
    have h2 : ∑' i, e (j + 1 + i) ≤ K * Real.sqrt (r j) :=
      Real.tsum_le_of_sum_range_le (fun _ => he0 _) (fun N => htail j N)
    have h3 : Real.sqrt (r j) ≤ Real.sqrt (r 0) / q ^ ((j : ℝ) / 2) := by
      rw [← sqrt_geom (r 0) q hq0 (hr0 0) j]
      exact Real.sqrt_le_sqrt (h36 j)
    have hCe : C = K := C_eq a b γR ha hb hγ
    have hexp : (((j + 1 : ℕ) : ℝ) - 1) / 2 = (j : ℝ) / 2 := by push_cast; ring
    rw [hexp, ← dist_eq_norm, ← hr 0, hCe]
    calc dist (x (j+1)) xs ≤ ∑' i, e (j + 1 + i) := h1
      _ ≤ K * Real.sqrt (r j) := h2
      _ ≤ K * (Real.sqrt (r 0) / q ^ ((j : ℝ) / 2)) := mul_le_mul_of_nonneg_left h3 hK0
      _ = K * Real.sqrt (r 0) / q ^ ((j : ℝ) / 2) := by ring
