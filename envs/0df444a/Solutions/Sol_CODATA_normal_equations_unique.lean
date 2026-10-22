-- Prove2me | solution 1 for CODATA.normal_equations_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:17:00.051004+00:00
-- url     : https://prove2.me/submissions/e68f35de-7660-409c-8fa8-4a0fe7dc7fd1

import Mathlib
import Definitions.Def_CODATA_lsa
import Definitions.Def_CODATA_uncert
import Definitions.Def_CODATA_values

open CODATA

noncomputable def g71c_B {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (v w : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * G i j * w j

lemma g71c_B_symm {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (hG : ∀ i j, G i j = G j i)
    (v w : Fin N → ℝ) : g71c_B G v w = g71c_B G w v := by
  unfold g71c_B; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  rw [hG]; ring

lemma g71c_B_sub_left {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (u v w : Fin N → ℝ) :
    g71c_B G (u - v) w = g71c_B G u w - g71c_B G v w := by
  unfold g71c_B; rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _; simp; ring

lemma g71c_B_sub_right {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (u v w : Fin N → ℝ) :
    g71c_B G u (v - w) = g71c_B G u v - g71c_B G u w := by
  unfold g71c_B; rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _; simp; ring

lemma g71c_B_mulVec {N M : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (A : Matrix (Fin N) (Fin M) ℝ)
    (d : Fin M → ℝ) (r : Fin N → ℝ) :
    g71c_B G (A.mulVec d) r = ∑ k, d k * ∑ i, ∑ j, A i k * G i j * r j := by
  unfold g71c_B
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  ring

lemma g71c_resid_add {N M : ℕ} (L : LSQ N M) (x d : Fin M → ℝ) :
    resid L (x + d) = resid L x - L.A.mulVec d := by
  funext i; simp [resid, Matrix.mulVec_add]; ring

lemma g71c_chi {N M : ℕ} (L : LSQ N M) (x : Fin M → ℝ) :
    chiSq L x = g71c_B L.G (resid L x) (resid L x) := rfl

lemma g71c_expand {N M : ℕ} (L : LSQ N M) (hG : ∀ i j, L.G i j = L.G j i) (x d : Fin M → ℝ) :
    chiSq L (x + d) = chiSq L x - 2 * ∑ k, d k * ∑ i, ∑ j, L.A i k * L.G i j * resid L x j
      + g71c_B L.G (L.A.mulVec d) (L.A.mulVec d) := by
  rw [g71c_chi, g71c_chi, g71c_resid_add, g71c_B_sub_left, g71c_B_sub_right, g71c_B_sub_right,
    g71c_B_symm L.G hG (resid L x) (L.A.mulVec d), g71c_B_mulVec]
  ring

/-!
# The normal equations characterize the minimizers

Section XII of the 2022 CODATA report describes the determination of
the recommended values as a least-squares adjustment: the adjusted
constants are chosen to minimize the chi-square statistic of the
weighted residuals. This milestone proves the classical equivalence
for the weighted model of `Def_CODATA_lsa`: when the weight matrix is
symmetric and strictly positive definite, the chi-square statistic is
a convex quadratic function of the adjusted constants, so its
minimizers are exactly the solutions of the normal equations; and when
the design matrix has full column rank, the solution of the normal
equations is unique. The milestone is proved on the way to the goal
theorem `CODATA.codata_self_consistent`. This statement replaces
`CODATA.normal_equations`, whose uniqueness clause quantified over an
arbitrary vector `x` without assuming that `x` solves the normal
equations; here uniqueness is stated as: any two solutions coincide.
-/

open CODATA
/-- For a least-squares problem whose weight matrix is symmetric and
strictly positive definite, the minimizers of the chi-square statistic
are exactly the solutions of the normal equations; and if the design
matrix has full column rank, then any two solutions of the normal
equations coincide. -/
theorem solution {N M : ℕ} (L : LSQ N M) (hG : IsSPD L.G)
    (hA : Function.Injective L.A.mulVec) (x : Fin M → ℝ) :
    (Minimizes L x ↔ SolvesNormal L x) ∧
      ∀ z w, SolvesNormal L z → SolvesNormal L w → z = w := by
  have hpos : ∀ v, 0 ≤ g71c_B L.G v v := by
    intro v
    by_cases hv : v = 0
    · subst hv; simp [g71c_B]
    · exact (hG.2 v hv).le
  refine ⟨⟨fun hmin => ?_, fun hn z => ?_⟩, fun z w hz hw => ?_⟩
  · -- minimizer ⇒ normal equations
    set g : Fin M → ℝ := fun k => ∑ i, ∑ j, L.A i k * L.G i j * resid L x j with hg
    have key : ∀ t : ℝ, 0 ≤ - 2 * t * ∑ k, g k * g k + t ^ 2 * g71c_B L.G (L.A.mulVec g) (L.A.mulVec g) := by
      intro t
      have h1 := hmin (x + t • g)
      rw [g71c_expand L hG.1] at h1
      have e1 : ∑ k, (t • g) k * ∑ i, ∑ j, L.A i k * L.G i j * resid L x j = t * ∑ k, g k * g k := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; simp [hg]; ring
      have e2 : g71c_B L.G (L.A.mulVec (t • g)) (L.A.mulVec (t • g))
          = t ^ 2 * g71c_B L.G (L.A.mulVec g) (L.A.mulVec g) := by
        rw [Matrix.mulVec_smul]; unfold g71c_B; rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; simp; ring
      rw [e1, e2] at h1; linarith
    set s := ∑ k, g k * g k
    set c := g71c_B L.G (L.A.mulVec g) (L.A.mulVec g)
    have hc : 0 ≤ c := hpos _
    have hs : 0 ≤ s := Finset.sum_nonneg (fun k _ => mul_self_nonneg _)
    have hs0 : s = 0 := by
      by_contra hne
      have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hne)
      have := key (s / (c + 1))
      have hc1 : 0 < c + 1 := by linarith
      have : -2 * (s / (c + 1)) * s + (s / (c + 1)) ^ 2 * c
          = s ^ 2 * (-(c + 2)) / (c + 1) ^ 2 := by field_simp; ring
      have : s ^ 2 * (-(c + 2)) / (c + 1) ^ 2 < 0 := by
        apply div_neg_of_neg_of_pos _ (by positivity)
        have : 0 < s ^ 2 := by positivity
        nlinarith
      linarith
    intro k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_self_nonneg (g k))).1 hs0 k (Finset.mem_univ _)
    exact mul_self_eq_zero.1 this
  · -- normal ⇒ minimizer
    have h1 := g71c_expand L hG.1 x (z - x)
    rw [add_sub_cancel] at h1
    rw [h1]
    have : ∑ k, (z - x) k * ∑ i, ∑ j, L.A i k * L.G i j * resid L x j = 0 := by
      apply Finset.sum_eq_zero; intro k _; rw [hn k, mul_zero]
    rw [this]; linarith [hpos (L.A.mulVec (z - x))]
  · -- uniqueness
    have hz' := g71c_expand L hG.1 z (w - z)
    have hw' := g71c_expand L hG.1 w (z - w)
    rw [add_sub_cancel] at hz' hw'
    have e1 : ∑ k, (w - z) k * ∑ i, ∑ j, L.A i k * L.G i j * resid L z j = 0 := by
      apply Finset.sum_eq_zero; intro k _; rw [hz k, mul_zero]
    have e2 : ∑ k, (z - w) k * ∑ i, ∑ j, L.A i k * L.G i j * resid L w j = 0 := by
      apply Finset.sum_eq_zero; intro k _; rw [hw k, mul_zero]
    rw [e1] at hz'; rw [e2] at hw'
    have h0 : g71c_B L.G (L.A.mulVec (z - w)) (L.A.mulVec (z - w)) = 0 := by
      linarith [hpos (L.A.mulVec (z - w)), hpos (L.A.mulVec (w - z))]
    by_contra hne
    have hv : L.A.mulVec (z - w) ≠ 0 := by
      intro h0'
      apply hne
      have : L.A.mulVec (z - w) = L.A.mulVec 0 := by rw [h0', Matrix.mulVec_zero]
      exact sub_eq_zero.1 (hA this)
    have := hG.2 _ hv
    unfold g71c_B at h0; linarith


