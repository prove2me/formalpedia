-- Prove2me | solution 1 for BosonicLearn.geometric_pgf_threshold
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T20:00:09.140897+00:00
-- url     : https://prove2.me/submissions/023867c1-f9d3-4f97-8749-9eeaf07f2852

import Mathlib

/-!
# Threshold separation for sums of independent geometric variables

Solution of `BosonicLearn.geometric_pgf_threshold` (arXiv:2609.26705, §5.7, Lemmas 13–14).
Everything is done on sequences `ℕ → ℝ` (no measure theory):

* `pgf_unique`: non-negative sequences with the same generating function on `(0, 1]` coincide;
* `conv`, `conv_pgf`, `conv_m1`, `conv_m2`: Cauchy products, their generating functions and moments;
* `exists_Kminus`: the law `p` of `K₋` (iterated Cauchy product of geometric laws), with mean
  `∑ λ⁻ᵢ` and second moment `(∑ λ⁻ᵢ)² + ∑ λ⁻ᵢ (1 + λ⁻ᵢ)`;
* `exists_J`: the law `q` of `J = ∑ Jᵢ` with generating function `∏ (1 + λ⁻ᵢ(1-z)) / (1 + λ⁺ᵢ(1-z))`,
  so that `p⁻ = p` and `p⁺ = p ⋆ q` by uniqueness;
* `diff_formula`, `diff_lower`: `Pr(K₊ > τ) - Pr(K₋ > τ) = ∑_{i ≤ τ} pᵢ Pr(J > τ - i)
  ≥ Pr(τ - h < K₋ ≤ τ) · Pr(J ≥ h)`;
* `concentration` (Chebyshev + covering): some window `(τ - h, τ]` has `p`-mass `≥ h / (10 s)`;
* `J_small`, `J_large`: lower-tail bounds for `J` read off from its generating function
  (`Pr(J = 0) ≤ 1 / (1 + δ/(1+Λ))`, and `Pr(J < h) ≤ 1/2` once `δ ≥ 6h + 3Λ`);
* `core`: the two cases `δ ≤ 12 + 6Λ` (`h = 1`) and `δ > 12 + 6Λ` (`h = ⌊δ/12⌋`), with
  `c = 1 / (480 + 70 Λ)`.
-/

noncomputable section

open Finset

/-- Cauchy product of two sequences. -/
private def conv (p q : ℕ → ℝ) (n : ℕ) : ℝ := ∑ kl ∈ antidiagonal n, p kl.1 * q kl.2

private lemma conv_nonneg {p q : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k) (n : ℕ) :
    0 ≤ conv p q n :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (hp _) (hq _)

private lemma hasSum_antidiag {f g : ℕ → ℝ} {a b : ℝ} (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k, 0 ≤ g k)
    (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun n => ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2) (a * b) := by
  have hfn : Summable fun k => ‖f k‖ := by
    have : (fun k => ‖f k‖) = f := funext fun k => Real.norm_of_nonneg (hf0 k)
    rw [this]; exact hf.summable
  have hgn : Summable fun k => ‖g k‖ := by
    have : (fun k => ‖g k‖) = g := funext fun k => Real.norm_of_nonneg (hg0 k)
    rw [this]; exact hg.summable
  have h1 := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn
  have h2 := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm
  rw [hf.tsum_eq, hg.tsum_eq] at h1
  rw [h1]
  exact h2.hasSum

private lemma conv_pgf {p q : ℕ → ℝ} {z a b : ℝ} (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k)
    (hz : 0 ≤ z) (ha : HasSum (fun k => p k * z ^ k) a) (hb : HasSum (fun k => q k * z ^ k) b) :
    HasSum (fun k => conv p q k * z ^ k) (a * b) := by
  have h := hasSum_antidiag (f := fun k => p k * z ^ k) (g := fun k => q k * z ^ k)
    (fun k => mul_nonneg (hp k) (pow_nonneg hz k)) (fun k => mul_nonneg (hq k) (pow_nonneg hz k))
    ha hb
  convert h using 1
  ext n
  unfold conv
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  have hk : kl.1 + kl.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
  rw [← hk, pow_add]
  ring

private lemma conv_m0 {p q : ℕ → ℝ} {a b : ℝ} (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k)
    (ha : HasSum p a) (hb : HasSum q b) : HasSum (conv p q) (a * b) :=
  hasSum_antidiag hp hq ha hb

private lemma conv_m1 {p q : ℕ → ℝ} {a b μ ν : ℝ} (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k)
    (ha : HasSum p a) (hb : HasSum q b)
    (hμ : HasSum (fun k : ℕ => (k : ℝ) * p k) μ) (hν : HasSum (fun k : ℕ => (k : ℝ) * q k) ν) :
    HasSum (fun k : ℕ => (k : ℝ) * conv p q k) (μ * b + a * ν) := by
  have h1 := hasSum_antidiag (f := fun k : ℕ => (k : ℝ) * p k) (g := q)
    (fun k => mul_nonneg (Nat.cast_nonneg k) (hp k)) hq hμ hb
  have h2 := hasSum_antidiag (f := p) (g := fun k : ℕ => (k : ℝ) * q k) hp
    (fun k => mul_nonneg (Nat.cast_nonneg k) (hq k)) ha hν
  convert h1.add h2 using 1
  ext n
  unfold conv
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  have hk : kl.1 + kl.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
  have : (n : ℝ) = (kl.1 : ℝ) + (kl.2 : ℝ) := by
    rw [← hk]; push_cast; rfl
  rw [this]
  ring

private lemma conv_m2 {p q : ℕ → ℝ} {a b μ ν S T : ℝ} (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k)
    (ha : HasSum p a) (hb : HasSum q b)
    (hμ : HasSum (fun k : ℕ => (k : ℝ) * p k) μ) (hν : HasSum (fun k : ℕ => (k : ℝ) * q k) ν)
    (hS : HasSum (fun k : ℕ => (k : ℝ) ^ 2 * p k) S) (hT : HasSum (fun k : ℕ => (k : ℝ) ^ 2 * q k) T) :
    HasSum (fun k : ℕ => (k : ℝ) ^ 2 * conv p q k) (S * b + 2 * (μ * ν) + a * T) := by
  have h1 := hasSum_antidiag (f := fun k : ℕ => (k : ℝ) ^ 2 * p k) (g := q)
    (fun k => mul_nonneg (by positivity) (hp k)) hq hS hb
  have h2 := hasSum_antidiag (f := fun k : ℕ => (k : ℝ) * p k) (g := fun k : ℕ => (k : ℝ) * q k)
    (fun k => mul_nonneg (Nat.cast_nonneg k) (hp k))
    (fun k => mul_nonneg (Nat.cast_nonneg k) (hq k)) hμ hν
  have h3 := hasSum_antidiag (f := p) (g := fun k : ℕ => (k : ℝ) ^ 2 * q k) hp
    (fun k => mul_nonneg (by positivity) (hq k)) ha hT
  convert (h1.add (h2.mul_left 2)).add h3 using 1
  ext n
  unfold conv
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  have hk : kl.1 + kl.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
  have : (n : ℝ) = (kl.1 : ℝ) + (kl.2 : ℝ) := by
    rw [← hk]; push_cast; rfl
  rw [this]
  ring

/-! ### Uniqueness of generating functions -/

private lemma pgf_zero_eq {p q : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k)
    (h : ∀ z : ℝ, 0 < z → z ≤ 1 →
      ∃ F, HasSum (fun k => p k * z ^ k) F ∧ HasSum (fun k => q k * z ^ k) F) :
    p 0 = q 0 := by
  obtain ⟨F1, hp1, hq1⟩ := h 1 one_pos le_rfl
  simp only [one_pow, mul_one] at hp1 hq1
  have hpt : HasSum (fun k => p (k + 1)) (F1 - p 0) := by
    have := (hasSum_nat_add_iff' 1).mpr hp1
    simpa using this
  have hqt : HasSum (fun k => q (k + 1)) (F1 - q 0) := by
    have := (hasSum_nat_add_iff' 1).mpr hq1
    simpa using this
  have hP : 0 ≤ F1 - p 0 := hpt.nonneg fun k => hp _
  have hQ : 0 ≤ F1 - q 0 := hqt.nonneg fun k => hq _
  have key : ∀ z : ℝ, 0 < z → z ≤ 1 → |p 0 - q 0| ≤ z * ((F1 - p 0) + (F1 - q 0)) := by
    intro z hz hz1
    obtain ⟨F, hpz, hqz⟩ := h z hz hz1
    have hpz' : HasSum (fun k => p (k + 1) * z ^ (k + 1)) (F - p 0) := by
      have := (hasSum_nat_add_iff' 1).mpr hpz
      simpa using this
    have hqz' : HasSum (fun k => q (k + 1) * z ^ (k + 1)) (F - q 0) := by
      have := (hasSum_nat_add_iff' 1).mpr hqz
      simpa using this
    have b1 : 0 ≤ F - p 0 := hpz'.nonneg fun k => mul_nonneg (hp _) (pow_nonneg hz.le _)
    have b2 : 0 ≤ F - q 0 := hqz'.nonneg fun k => mul_nonneg (hq _) (pow_nonneg hz.le _)
    have b3 : F - p 0 ≤ z * (F1 - p 0) := by
      refine hasSum_le (fun k => ?_) hpz' (hpt.mul_left z)
      have : z ^ (k + 1) ≤ z := by
        calc z ^ (k + 1) = z ^ k * z := pow_succ z k
          _ ≤ 1 * z := mul_le_mul_of_nonneg_right (pow_le_one₀ hz.le hz1) hz.le
          _ = z := one_mul z
      calc p (k + 1) * z ^ (k + 1) ≤ p (k + 1) * z := mul_le_mul_of_nonneg_left this (hp _)
        _ = z * p (k + 1) := mul_comm _ _
    have b4 : F - q 0 ≤ z * (F1 - q 0) := by
      refine hasSum_le (fun k => ?_) hqz' (hqt.mul_left z)
      have : z ^ (k + 1) ≤ z := by
        calc z ^ (k + 1) = z ^ k * z := pow_succ z k
          _ ≤ 1 * z := mul_le_mul_of_nonneg_right (pow_le_one₀ hz.le hz1) hz.le
          _ = z := one_mul z
      calc q (k + 1) * z ^ (k + 1) ≤ q (k + 1) * z := mul_le_mul_of_nonneg_left this (hq _)
        _ = z * q (k + 1) := mul_comm _ _
    have c1 : 0 ≤ z * (F1 - p 0) := mul_nonneg hz.le hP
    have c2 : 0 ≤ z * (F1 - q 0) := mul_nonneg hz.le hQ
    rw [abs_le]
    constructor <;> nlinarith
  by_contra hne
  have hd : 0 < |p 0 - q 0| := abs_pos.mpr (sub_ne_zero.mpr hne)
  set C := (F1 - p 0) + (F1 - q 0) with hC
  have hC0 : 0 ≤ C := add_nonneg hP hQ
  set z := min 1 (|p 0 - q 0| / (2 * (C + 1))) with hzdef
  have hz : 0 < z := lt_min one_pos (by positivity)
  have hz1 : z ≤ 1 := min_le_left _ _
  have hz2 : z ≤ |p 0 - q 0| / (2 * (C + 1)) := min_le_right _ _
  have := key z hz hz1
  have h3 : z * C ≤ |p 0 - q 0| / (2 * (C + 1)) * C := mul_le_mul_of_nonneg_right hz2 hC0
  have h4 : |p 0 - q 0| / (2 * (C + 1)) * C < |p 0 - q 0| := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

private lemma pgf_unique {p q : ℕ → ℝ} (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k)
    (h : ∀ z : ℝ, 0 < z → z ≤ 1 →
      ∃ F, HasSum (fun k => p k * z ^ k) F ∧ HasSum (fun k => q k * z ^ k) F) (n : ℕ) :
    p n = q n := by
  induction n generalizing p q with
  | zero => exact pgf_zero_eq hp hq h
  | succ n ih =>
    have h0 := pgf_zero_eq hp hq h
    refine ih (p := fun k => p (k + 1)) (q := fun k => q (k + 1)) (fun k => hp _) (fun k => hq _) ?_
    intro z hz hz1
    obtain ⟨F, hF1, hF2⟩ := h z hz hz1
    refine ⟨(F - p 0) / z, ?_, ?_⟩
    · have h1 : HasSum (fun k => p (k + 1) * z ^ (k + 1)) (F - p 0) := by
        have := (hasSum_nat_add_iff' 1).mpr hF1
        simpa using this
      have h2 : (fun k => p (k + 1) * z ^ k) = fun k => p (k + 1) * z ^ (k + 1) / z := by
        funext k
        rw [pow_succ, ← mul_assoc, mul_div_assoc, div_self hz.ne', mul_one]
      rw [h2]
      exact h1.div_const z
    · have h1 : HasSum (fun k => q (k + 1) * z ^ (k + 1)) (F - p 0) := by
        have := (hasSum_nat_add_iff' 1).mpr hF2
        rw [h0]
        simpa using this
      have h2 : (fun k => q (k + 1) * z ^ k) = fun k => q (k + 1) * z ^ (k + 1) / z := by
        funext k
        rw [pow_succ, ← mul_assoc, mul_div_assoc, div_self hz.ne', mul_one]
      rw [h2]
      exact h1.div_const z

/-! ### Tail sums and the convolution identity -/

private lemma tail_eq {p : ℕ → ℝ} (hp : HasSum p 1) (τ : ℕ) :
    (∑' k, if τ < k then p k else 0) = 1 - ∑ k ∈ range (τ + 1), p k := by
  have h1 : HasSum (fun k => if k ∈ range (τ + 1) then p k else 0) (∑ k ∈ range (τ + 1), p k) := by
    have h : HasSum (fun k => if k ∈ range (τ + 1) then p k else 0)
        (∑ k ∈ range (τ + 1), if k ∈ range (τ + 1) then p k else 0) :=
      hasSum_sum_of_ne_finset_zero (fun b hb => by simp [hb])
    convert h using 1
    exact Finset.sum_congr rfl fun k hk => by simp [hk]
  have h2 := hp.sub h1
  have h3 : (fun k => p k - if k ∈ range (τ + 1) then p k else 0)
      = fun k => if τ < k then p k else 0 := by
    ext k
    by_cases hk : τ < k
    · have : k ∉ range (τ + 1) := by rw [Finset.mem_range]; omega
      simp [hk, this]
    · have : k ∈ range (τ + 1) := by rw [Finset.mem_range]; omega
      simp [hk, this]
  rw [h3] at h2
  exact h2.tsum_eq

private lemma diff_formula {pm q : ℕ → ℝ} (hpm : HasSum pm 1) (hc : HasSum (conv pm q) 1)
    (τ : ℕ) :
    (∑' k, if τ < k then conv pm q k else 0) - (∑' k, if τ < k then pm k else 0)
      = ∑ i ∈ range (τ + 1), pm i * (1 - ∑ j ∈ range (τ + 1 - i), q j) := by
  rw [tail_eq hc, tail_eq hpm]
  have h1 : ∑ k ∈ range (τ + 1), conv pm q k
      = ∑ i ∈ range (τ + 1), pm i * ∑ j ∈ range (τ + 1 - i), q j := by
    unfold conv
    simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => pm i * q j)]
    rw [Finset.sum_range_diag_flip (τ + 1) (fun i j => pm i * q j)]
    simp_rw [Finset.mul_sum]
  rw [h1]
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib]
  ring

private lemma diff_lower {pm q : ℕ → ℝ} (hpm0 : ∀ k, 0 ≤ pm k) (hq0 : ∀ k, 0 ≤ q k)
    (hq : HasSum q 1) (τ h : ℕ) :
    (∑ i ∈ Ico (τ + 1 - h) (τ + 1), pm i) * (1 - ∑ j ∈ range h, q j)
      ≤ ∑ i ∈ range (τ + 1), pm i * (1 - ∑ j ∈ range (τ + 1 - i), q j) := by
  have hle1 : ∀ n, ∑ j ∈ range n, q j ≤ 1 := fun n => sum_le_hasSum _ (fun i _ => hq0 i) hq
  rw [Finset.sum_mul]
  calc ∑ i ∈ Ico (τ + 1 - h) (τ + 1), pm i * (1 - ∑ j ∈ range h, q j)
      ≤ ∑ i ∈ Ico (τ + 1 - h) (τ + 1), pm i * (1 - ∑ j ∈ range (τ + 1 - i), q j) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Finset.mem_Ico] at hi
        refine mul_le_mul_of_nonneg_left ?_ (hpm0 i)
        have : ∑ j ∈ range (τ + 1 - i), q j ≤ ∑ j ∈ range h, q j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
            (fun j _ _ => hq0 j)
        linarith
    _ ≤ ∑ i ∈ range (τ + 1), pm i * (1 - ∑ j ∈ range (τ + 1 - i), q j) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro i hi
          rw [Finset.mem_Ico] at hi
          rw [Finset.mem_range]
          exact hi.2
        · intro i _ _
          exact mul_nonneg (hpm0 i) (by linarith [hle1 (τ + 1 - i)])

/-! ### The geometric law and the laws of `K₋` and `J` -/

/-- The geometric law with mean `l`. -/
private def geo (l : ℝ) (k : ℕ) : ℝ := (1 + l)⁻¹ * (l / (1 + l)) ^ k

private lemma geo_nonneg {l : ℝ} (hl : 0 ≤ l) (k : ℕ) : 0 ≤ geo l k := by
  unfold geo; positivity

private lemma geo_pgf {l : ℝ} (hl : 0 ≤ l) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    HasSum (fun k => geo l k * z ^ k) (1 + l * (1 - z))⁻¹ := by
  have hl1 : 0 < 1 + l := by linarith
  have hr0 : 0 ≤ l / (1 + l) * z := by positivity
  have hr1 : l / (1 + l) * z < 1 := by
    have : l / (1 + l) < 1 := by rw [div_lt_one hl1]; linarith
    calc l / (1 + l) * z ≤ l / (1 + l) * 1 := mul_le_mul_of_nonneg_left hz1 (by positivity)
      _ < 1 := by rwa [mul_one]
  have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (1 + l)⁻¹
  have e1 : (fun k => geo l k * z ^ k) = fun k => (1 + l)⁻¹ * (l / (1 + l) * z) ^ k := by
    funext k
    unfold geo
    rw [mul_pow]
    ring
  have e2 : (1 + l * (1 - z))⁻¹ = (1 + l)⁻¹ * (1 - l / (1 + l) * z)⁻¹ := by
    rw [← mul_inv]
    congr 1
    field_simp
    ring
  rw [e1, e2]
  exact h

private lemma geo_one_sub {l : ℝ} (hl : 0 ≤ l) : 1 - l / (1 + l) = (1 + l)⁻¹ := by
  have hl1 : 0 < 1 + l := by linarith
  field_simp
  ring

private lemma geo_m1 {l : ℝ} (hl : 0 ≤ l) : HasSum (fun k : ℕ => (k : ℝ) * geo l k) l := by
  have hl1 : 0 < 1 + l := by linarith
  have hr : ‖l / (1 + l)‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity), div_lt_one hl1]; linarith
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hr).mul_left (1 + l)⁻¹
  have e1 : (fun k : ℕ => (k : ℝ) * geo l k)
      = fun k : ℕ => (1 + l)⁻¹ * ((k : ℝ) * (l / (1 + l)) ^ k) := by
    funext k
    unfold geo
    ring
  have e2 : (1 + l)⁻¹ * (l / (1 + l) / (1 - l / (1 + l)) ^ 2) = l := by
    have hne : 1 + l ≠ 0 := hl1.ne'
    rw [geo_one_sub hl]
    field_simp
  rw [e2] at h
  rw [e1]
  exact h

private lemma geo_m2 {l : ℝ} (hl : 0 ≤ l) :
    HasSum (fun k : ℕ => (k : ℝ) ^ 2 * geo l k) (l ^ 2 + l * (1 + l)) := by
  have hl1 : 0 < 1 + l := by linarith
  have hr : ‖l / (1 + l)‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity), div_lt_one hl1]; linarith
  have hA := hasSum_choose_mul_geometric_of_norm_lt_one 2 hr
  have hB := hasSum_coe_mul_geometric_of_norm_lt_one hr
  have hC := hasSum_geometric_of_norm_lt_one hr
  have h := (((hA.mul_left 2).sub (hB.mul_left 3)).sub (hC.mul_left 2)).mul_left (1 + l)⁻¹
  have e1 : (fun k : ℕ => (k : ℝ) ^ 2 * geo l k)
      = fun k : ℕ => (1 + l)⁻¹ * (2 * (((k + 2).choose 2 : ℕ) * (l / (1 + l)) ^ k)
          - 3 * ((k : ℝ) * (l / (1 + l)) ^ k) - 2 * (l / (1 + l)) ^ k) := by
    funext k
    unfold geo
    rw [Nat.cast_choose_two]
    push_cast
    ring
  have e2 : l ^ 2 + l * (1 + l) = (1 + l)⁻¹ * (2 * (1 / (1 - l / (1 + l)) ^ (2 + 1))
      - 3 * (l / (1 + l) / (1 - l / (1 + l)) ^ 2) - 2 * (1 - l / (1 + l))⁻¹) := by
    have hne : 1 + l ≠ 0 := hl1.ne'
    rw [geo_one_sub hl]
    simp only [inv_pow, inv_inv, div_inv_eq_mul]
    field_simp
    ring
  rw [e1, e2]
  exact h

/-- The law of `K₋`: existence, generating function, first two moments. -/
private lemma exists_Kminus {ι : Type*} (s : Finset ι) (l : ι → ℝ) (hl : ∀ i, 0 ≤ l i) :
    ∃ p : ℕ → ℝ, (∀ k, 0 ≤ p k) ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ 1 →
        HasSum (fun k => p k * z ^ k) (∏ i ∈ s, (1 + l i * (1 - z))⁻¹)) ∧
      HasSum p 1 ∧
      HasSum (fun k : ℕ => (k : ℝ) * p k) (∑ i ∈ s, l i) ∧
      HasSum (fun k : ℕ => (k : ℝ) ^ 2 * p k) ((∑ i ∈ s, l i) ^ 2 + ∑ i ∈ s, l i * (1 + l i)) := by
  classical
  have geo_m0 : ∀ {x : ℝ}, 0 ≤ x → HasSum (geo x) 1 := by
    intro x hx
    simpa using geo_pgf hx (z := 1) zero_le_one le_rfl
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨geo 0, geo_nonneg le_rfl, ?_, geo_m0 le_rfl, ?_, ?_⟩
    · intro z hz hz1
      simpa using geo_pgf le_rfl hz hz1
    · simpa using geo_m1 (l := 0) le_rfl
    · simpa using geo_m2 (l := 0) le_rfl
  | insert a s ha ih =>
    obtain ⟨p, hp0, hpgf, hm0, hm1, hm2⟩ := ih
    have hg0 := geo_nonneg (hl a)
    refine ⟨conv (geo (l a)) p, conv_nonneg hg0 hp0, ?_, ?_, ?_, ?_⟩
    · intro z hz hz1
      rw [Finset.prod_insert ha]
      exact conv_pgf hg0 hp0 hz (geo_pgf (hl a) hz hz1) (hpgf z hz hz1)
    · simpa using conv_m0 hg0 hp0 (geo_m0 (hl a)) hm0
    · rw [Finset.sum_insert ha]
      convert conv_m1 hg0 hp0 (geo_m0 (hl a)) hm0 (geo_m1 (hl a)) hm1 using 1
      ring
    · rw [Finset.sum_insert ha, Finset.sum_insert ha]
      convert conv_m2 hg0 hp0 (geo_m0 (hl a)) hm0 (geo_m1 (hl a)) hm1 (geo_m2 (hl a)) hm2 using 1
      ring

/-- The law of one summand `Jᵢ`: a mixture of the point mass at `0` and a geometric law. -/
private def mix (a b : ℝ) (k : ℕ) : ℝ := a / b * geo 0 k + (1 - a / b) * geo b k

private lemma mix_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (k : ℕ) : 0 ≤ mix a b k := by
  have hb : 0 ≤ b := ha.trans hab
  have h1 : a / b ≤ 1 := div_le_one_of_le₀ hab hb
  have h0 : 0 ≤ a / b := div_nonneg ha hb
  unfold mix
  exact add_nonneg (mul_nonneg h0 (geo_nonneg le_rfl k))
    (mul_nonneg (by linarith) (geo_nonneg hb k))

private lemma mix_pgf {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    HasSum (fun k => mix a b k * z ^ k) ((1 + a * (1 - z)) * (1 + b * (1 - z))⁻¹) := by
  have hb : 0 ≤ b := ha.trans hab
  have h := ((geo_pgf le_rfl hz hz1).mul_left (a / b)).add
    ((geo_pgf hb hz hz1).mul_left (1 - a / b))
  have e1 : (fun k => mix a b k * z ^ k)
      = fun k => a / b * (geo 0 k * z ^ k) + (1 - a / b) * (geo b k * z ^ k) := by
    funext k
    unfold mix
    ring
  have e2 : (1 + a * (1 - z)) * (1 + b * (1 - z))⁻¹
      = a / b * (1 + 0 * (1 - z))⁻¹ + (1 - a / b) * (1 + b * (1 - z))⁻¹ := by
    rcases hb.eq_or_lt with hb0 | hb0
    · have ha0 : a = 0 := le_antisymm (hb0 ▸ hab) ha
      subst hb0
      simp [ha0]
    · have h1 : 0 < 1 + b * (1 - z) := by nlinarith
      have hba : a / b * b = a := div_mul_cancel₀ a hb0.ne'
      have h2 : a / b * (1 + b * (1 - z)) = a / b + a * (1 - z) := by
        have : a / b * (1 + b * (1 - z)) = a / b + a / b * b * (1 - z) := by ring
        rw [this, hba]
      have h3 : a / b = (a / b + a * (1 - z)) * (1 + b * (1 - z))⁻¹ := by
        rw [← h2, mul_assoc, mul_inv_cancel₀ h1.ne', mul_one]
      rw [zero_mul, add_zero, inv_one, mul_one]
      calc (1 + a * (1 - z)) * (1 + b * (1 - z))⁻¹
          = (a / b + a * (1 - z)) * (1 + b * (1 - z))⁻¹
            + (1 - a / b) * (1 + b * (1 - z))⁻¹ := by ring
        _ = a / b + (1 - a / b) * (1 + b * (1 - z))⁻¹ := by rw [← h3]
  rw [e1, e2]
  exact h

/-- The law of `J`: existence and generating function. -/
private lemma exists_J {ι : Type*} (s : Finset ι) (lm lp : ι → ℝ) (h0 : ∀ i, 0 ≤ lm i)
    (hle : ∀ i, lm i ≤ lp i) :
    ∃ q : ℕ → ℝ, (∀ k, 0 ≤ q k) ∧
      ∀ z : ℝ, 0 ≤ z → z ≤ 1 → HasSum (fun k => q k * z ^ k)
        (∏ i ∈ s, ((1 + lm i * (1 - z)) * (1 + lp i * (1 - z))⁻¹)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨geo 0, geo_nonneg le_rfl, ?_⟩
    intro z hz hz1
    simpa using geo_pgf le_rfl hz hz1
  | insert a s ha ih =>
    obtain ⟨q, hq0, hpgf⟩ := ih
    have hg0 := mix_nonneg (h0 a) (hle a)
    refine ⟨conv (mix (lm a) (lp a)) q, conv_nonneg hg0 hq0, ?_⟩
    intro z hz hz1
    rw [Finset.prod_insert ha]
    exact conv_pgf hg0 hq0 hz (mix_pgf (h0 a) (hle a) hz hz1) (hpgf z hz hz1)

/-! ### Lower tail of `J` from its generating function -/

private lemma J_pgf_bound {ι : Type*} (s : Finset ι) (lm lp : ι → ℝ) {Λ : ℝ}
    (h0 : ∀ i, 0 ≤ lm i) (hle : ∀ i, lm i ≤ lp i) (hΛ : ∀ i, lp i ≤ Λ) (hΛ0 : 0 ≤ Λ)
    {w : ℝ} (hw : 0 ≤ w) :
    (∏ i ∈ s, ((1 + lm i * w) * (1 + lp i * w)⁻¹))
      * (1 + (∑ i ∈ s, (lp i - lm i)) * w / (1 + Λ * w)) ≤ 1 := by
  classical
  have ht : 0 < 1 + Λ * w := by positivity
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hP : 0 ≤ ∏ i ∈ s, ((1 + lm i * w) * (1 + lp i * w)⁻¹) :=
      Finset.prod_nonneg fun i _ => by
        have h1 : 0 ≤ lm i * w := mul_nonneg (h0 i) hw
        have h2 : 0 ≤ lp i * w := mul_nonneg ((h0 i).trans (hle i)) hw
        positivity
    have hD : 0 ≤ ∑ i ∈ s, (lp i - lm i) := Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hle i)
    set P := ∏ i ∈ s, ((1 + lm i * w) * (1 + lp i * w)⁻¹) with hPdef
    set D := ∑ i ∈ s, (lp i - lm i) with hDdef
    have hd : 0 ≤ lp a - lm a := sub_nonneg.mpr (hle a)
    have hu : 0 < 1 + lm a * w := by have := mul_nonneg (h0 a) hw; linarith
    have hv : 0 < 1 + lp a * w := by
      have := mul_nonneg ((h0 a).trans (hle a)) hw; linarith
    have hf0 : 0 ≤ (1 + lm a * w) * (1 + lp a * w)⁻¹ := by positivity
    have hf : (1 + lm a * w) * (1 + lp a * w)⁻¹ * (1 + (lp a - lm a) * w / (1 + Λ * w)) ≤ 1 := by
      have e : (1 + lm a * w) * (1 + lp a * w)⁻¹ * (1 + (lp a - lm a) * w / (1 + Λ * w))
          = (1 + lm a * w) * ((1 + Λ * w) + (lp a - lm a) * w)
            / ((1 + lp a * w) * (1 + Λ * w)) := by
        field_simp
      rw [e, div_le_one (by positivity)]
      have h1 : 0 ≤ (lp a - lm a) * w * ((Λ - lm a) * w) :=
        mul_nonneg (mul_nonneg hd hw)
          (mul_nonneg (sub_nonneg.mpr ((hle a).trans (hΛ a))) hw)
      nlinarith
    have hx : 0 ≤ (lp a - lm a) * w / (1 + Λ * w) := div_nonneg (mul_nonneg hd hw) ht.le
    have hX : 0 ≤ D * w / (1 + Λ * w) := div_nonneg (mul_nonneg hD hw) ht.le
    have hsplit : 1 + (lp a - lm a + D) * w / (1 + Λ * w)
        ≤ (1 + (lp a - lm a) * w / (1 + Λ * w)) * (1 + D * w / (1 + Λ * w)) := by
      have e : (lp a - lm a + D) * w / (1 + Λ * w)
          = (lp a - lm a) * w / (1 + Λ * w) + D * w / (1 + Λ * w) := by ring
      rw [e]
      nlinarith [mul_nonneg hx hX]
    calc (1 + lm a * w) * (1 + lp a * w)⁻¹ * P * (1 + (lp a - lm a + D) * w / (1 + Λ * w))
        ≤ (1 + lm a * w) * (1 + lp a * w)⁻¹ * P
          * ((1 + (lp a - lm a) * w / (1 + Λ * w)) * (1 + D * w / (1 + Λ * w))) :=
          mul_le_mul_of_nonneg_left hsplit (mul_nonneg hf0 hP)
      _ = ((1 + lm a * w) * (1 + lp a * w)⁻¹ * (1 + (lp a - lm a) * w / (1 + Λ * w)))
          * (P * (1 + D * w / (1 + Λ * w))) := by ring
      _ ≤ 1 * 1 := mul_le_mul hf ih (mul_nonneg hP (by linarith)) zero_le_one
      _ = 1 := one_mul 1

private lemma J_pgf_nonneg {ι : Type*} (s : Finset ι) (lm lp : ι → ℝ)
    (h0 : ∀ i, 0 ≤ lm i) (hle : ∀ i, lm i ≤ lp i) {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ ∏ i ∈ s, ((1 + lm i * w) * (1 + lp i * w)⁻¹) :=
  Finset.prod_nonneg fun i _ => by
    have h1 : 0 ≤ lm i * w := mul_nonneg (h0 i) hw
    have h2 : 0 ≤ lp i * w := mul_nonneg ((h0 i).trans (hle i)) hw
    positivity

/-- `Pr(J = 0) ≤ 1 / (1 + δ / (1 + Λ))`. -/
private lemma J_small {ι : Type*} (s : Finset ι) (lm lp : ι → ℝ) {Λ : ℝ}
    (h0 : ∀ i, 0 ≤ lm i) (hle : ∀ i, lm i ≤ lp i) (hΛ : ∀ i, lp i ≤ Λ) (hΛ0 : 0 ≤ Λ)
    {q : ℕ → ℝ} (hq0 : ∀ k, 0 ≤ q k)
    (hq : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → HasSum (fun k => q k * z ^ k)
      (∏ i ∈ s, ((1 + lm i * (1 - z)) * (1 + lp i * (1 - z))⁻¹))) :
    q 0 * (1 + (∑ i ∈ s, (lp i - lm i)) / (1 + Λ)) ≤ 1 := by
  have h := hq 0 le_rfl zero_le_one
  have h1 : ∑ k ∈ range 1, q k * (0 : ℝ) ^ k
      ≤ ∏ i ∈ s, ((1 + lm i * (1 - 0)) * (1 + lp i * (1 - 0))⁻¹) :=
    sum_le_hasSum _ (fun i _ => mul_nonneg (hq0 i) (by positivity)) h
  have h2 : q 0 ≤ ∏ i ∈ s, ((1 + lm i * (1 - 0)) * (1 + lp i * (1 - 0))⁻¹) := by
    simpa using h1
  have hb := J_pgf_bound s lm lp h0 hle hΛ hΛ0 (w := 1 - 0) (by norm_num)
  have hD : 0 ≤ ∑ i ∈ s, (lp i - lm i) := Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hle i)
  have hB : 0 ≤ 1 + (∑ i ∈ s, (lp i - lm i)) / (1 + Λ) := by positivity
  have e : 1 + (∑ i ∈ s, (lp i - lm i)) * (1 - 0) / (1 + Λ * (1 - 0))
      = 1 + (∑ i ∈ s, (lp i - lm i)) / (1 + Λ) := by norm_num
  rw [e] at hb
  exact (mul_le_mul_of_nonneg_right h2 hB).trans hb

/-- `Pr(J < h) ≤ 1/2` once `δ ≥ 6 h + 3 Λ`. -/
private lemma J_large {ι : Type*} (s : Finset ι) (lm lp : ι → ℝ) {Λ : ℝ}
    (h0 : ∀ i, 0 ≤ lm i) (hle : ∀ i, lm i ≤ lp i) (hΛ : ∀ i, lp i ≤ Λ) (hΛ0 : 0 ≤ Λ)
    {q : ℕ → ℝ} (hq0 : ∀ k, 0 ≤ q k)
    (hq : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → HasSum (fun k => q k * z ^ k)
      (∏ i ∈ s, ((1 + lm i * (1 - z)) * (1 + lp i * (1 - z))⁻¹)))
    {h : ℕ} (hh : 1 ≤ h) (hδ : 6 * (h : ℝ) + 3 * Λ ≤ ∑ i ∈ s, (lp i - lm i)) :
    ∑ j ∈ range h, q j ≤ 1 / 2 := by
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hhpos : (0 : ℝ) < h := by linarith
  set w : ℝ := 1 / (2 * h) with hwdef
  have hw0 : 0 < w := by positivity
  have hw1 : w ≤ 1 / 2 := by
    rw [hwdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hz0 : 0 ≤ 1 - w := by linarith
  have hz1 : 1 - w ≤ 1 := by linarith
  set G := ∏ i ∈ s, ((1 + lm i * (1 - (1 - w))) * (1 + lp i * (1 - (1 - w)))⁻¹) with hG
  have hsum : ∑ j ∈ range h, q j * (1 - w) ^ j ≤ G :=
    sum_le_hasSum _ (fun i _ => mul_nonneg (hq0 i) (pow_nonneg hz0 i)) (hq (1 - w) hz0 hz1)
  have hzh : 1 / 2 ≤ (1 - w) ^ h := by
    have hb := one_add_mul_le_pow (a := -w) (by linarith) h
    have e : 1 + (h : ℝ) * -w = 1 / 2 := by
      rw [hwdef]; field_simp; ring
    rw [e] at hb
    have e2 : (1 : ℝ) + -w = 1 - w := by ring
    rwa [e2] at hb
  have hlow : 1 / 2 * ∑ j ∈ range h, q j ≤ ∑ j ∈ range h, q j * (1 - w) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.mem_range] at hj
    have : (1 - w) ^ h ≤ (1 - w) ^ j := pow_le_pow_of_le_one hz0 hz1 hj.le
    calc 1 / 2 * q j = q j * (1 / 2) := mul_comm _ _
      _ ≤ q j * (1 - w) ^ j := mul_le_mul_of_nonneg_left (hzh.trans this) (hq0 j)
  have hb := J_pgf_bound s lm lp h0 hle hΛ hΛ0 (w := 1 - (1 - w)) (by linarith)
  have hG0 : 0 ≤ G := J_pgf_nonneg s lm lp h0 hle (by linarith)
  have hden : 0 < 1 + Λ * (1 - (1 - w)) := by
    have : 0 ≤ Λ * (1 - (1 - w)) := mul_nonneg hΛ0 (by linarith)
    linarith
  have h3 : 3 ≤ (∑ i ∈ s, (lp i - lm i)) * (1 - (1 - w)) / (1 + Λ * (1 - (1 - w))) := by
    rw [le_div_iff₀ hden]
    have e : 3 * (1 + Λ * (1 - (1 - w))) = w * (6 * (h : ℝ) + 3 * Λ) := by
      rw [hwdef]; field_simp; ring
    rw [e]
    calc w * (6 * (h : ℝ) + 3 * Λ) ≤ w * ∑ i ∈ s, (lp i - lm i) :=
          mul_le_mul_of_nonneg_left hδ hw0.le
      _ = (∑ i ∈ s, (lp i - lm i)) * (1 - (1 - w)) := by ring
  have h4 : G * 4 ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hG0) hb
    linarith
  linarith

/-! ### Concentration of `K₋` (Chebyshev and a covering argument) -/

private lemma chebyshev_bulk {p : ℕ → ℝ} {μ S s : ℝ} (hp0 : ∀ k, 0 ≤ p k) (h0 : HasSum p 1)
    (h1 : HasSum (fun k : ℕ => (k : ℝ) * p k) μ) (h2 : HasSum (fun k : ℕ => (k : ℝ) ^ 2 * p k) S)
    (hs : 0 < s) (hv : S - μ ^ 2 ≤ s ^ 2) :
    3 / 4 ≤ ∑ i ∈ Ico ⌈μ - 2 * s⌉₊ (⌈μ - 2 * s⌉₊ + ⌈4 * s⌉₊), p i := by
  set A := Ico ⌈μ - 2 * s⌉₊ (⌈μ - 2 * s⌉₊ + ⌈4 * s⌉₊) with hA
  have hvar : HasSum (fun k : ℕ => ((k : ℝ) - μ) ^ 2 * p k / (4 * s ^ 2))
      ((S - μ ^ 2) / (4 * s ^ 2)) := by
    have h := ((h2.sub (h1.mul_left (2 * μ))).add (h0.mul_left (μ ^ 2))).div_const (4 * s ^ 2)
    have e1 : (fun k : ℕ => ((k : ℝ) - μ) ^ 2 * p k / (4 * s ^ 2))
        = fun k : ℕ => ((k : ℝ) ^ 2 * p k - 2 * μ * ((k : ℝ) * p k) + μ ^ 2 * p k) / (4 * s ^ 2) := by
      funext k; ring
    have e2 : (S - μ ^ 2) / (4 * s ^ 2) = (S - 2 * μ * μ + μ ^ 2 * 1) / (4 * s ^ 2) := by ring
    rw [e1, e2]
    exact h
  have hin : HasSum (fun k => if k ∈ A then p k else 0) (∑ k ∈ A, p k) := by
    have h : HasSum (fun k => if k ∈ A then p k else 0)
        (∑ k ∈ A, if k ∈ A then p k else 0) :=
      hasSum_sum_of_ne_finset_zero (fun b hb => by simp [hb])
    convert h using 1
    exact Finset.sum_congr rfl fun k hk => by simp [hk]
  have hout := h0.sub hin
  have hle : 1 - ∑ k ∈ A, p k ≤ (S - μ ^ 2) / (4 * s ^ 2) := by
    refine hasSum_le (fun k => ?_) hout hvar
    by_cases hk : k ∈ A
    · simp only [hk, if_true, sub_self]
      have := hp0 k
      positivity
    · simp only [hk, if_false, sub_zero]
      have hfar : 4 * s ^ 2 ≤ ((k : ℝ) - μ) ^ 2 := by
        rw [hA, Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
        rcases hk with hk | hk
        · have : (k : ℝ) < μ - 2 * s := Nat.lt_ceil.mp hk
          nlinarith
        · have h3 : ((⌈μ - 2 * s⌉₊ + ⌈4 * s⌉₊ : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
          push_cast at h3
          have h4 : μ - 2 * s ≤ ⌈μ - 2 * s⌉₊ := Nat.le_ceil _
          have h5 : 4 * s ≤ ⌈4 * s⌉₊ := Nat.le_ceil _
          nlinarith
      rw [le_div_iff₀ (by positivity)]
      calc p k * (4 * s ^ 2) ≤ p k * ((k : ℝ) - μ) ^ 2 := mul_le_mul_of_nonneg_left hfar (hp0 k)
        _ = ((k : ℝ) - μ) ^ 2 * p k := mul_comm _ _
  have hq : (S - μ ^ 2) / (4 * s ^ 2) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith

private lemma block_sum {p : ℕ → ℝ} {h : ℕ} (hh : 1 ≤ h) {ε : ℝ}
    (hW : ∀ τ, ∑ i ∈ Ico (τ + 1 - h) (τ + 1), p i ≤ ε) (a n : ℕ) :
    ∑ i ∈ Ico a (a + n * h), p i ≤ n * ε := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ (n + 1) * h := Nat.mul_pos (Nat.succ_pos n) hh
    have h2 : (n + 1) * h = n * h + h := Nat.succ_mul n h
    have e1 : a + (n + 1) * h - 1 + 1 = a + (n + 1) * h := by omega
    have e2 : a + (n + 1) * h - 1 + 1 - h = a + n * h := by omega
    have hw := hW (a + (n + 1) * h - 1)
    rw [e2, e1] at hw
    rw [← Finset.sum_Ico_consecutive p (show a ≤ a + n * h by omega)
      (show a + n * h ≤ a + (n + 1) * h by omega)]
    push_cast
    linarith

private lemma concentration {p : ℕ → ℝ} {μ S s : ℝ} (hp0 : ∀ k, 0 ≤ p k) (h0 : HasSum p 1)
    (h1 : HasSum (fun k : ℕ => (k : ℝ) * p k) μ) (h2 : HasSum (fun k : ℕ => (k : ℝ) ^ 2 * p k) S)
    (hs : 1 ≤ s) (hv : S - μ ^ 2 ≤ s ^ 2) {h : ℕ} (hh : 1 ≤ h) (hhs : (h : ℝ) ≤ s) :
    ∃ τ : ℕ, (h : ℝ) / (10 * s) ≤ ∑ i ∈ Ico (τ + 1 - h) (τ + 1), p i := by
  by_contra! hcon
  have hs0 : 0 < s := by linarith
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hbulk := chebyshev_bulk hp0 h0 h1 h2 hs0 hv
  set a := ⌈μ - 2 * s⌉₊ with ha
  set L := ⌈4 * s⌉₊ with hL
  set n := L / h + 1 with hn
  have hLn : L ≤ n * h := by
    have := Nat.div_add_mod L h
    have := Nat.mod_lt L (show 0 < h by omega)
    rw [hn, Nat.add_mul, one_mul, Nat.mul_comm]
    omega
  have hblock := block_sum hh (fun τ => (hcon τ).le) a n
  have hsub : ∑ i ∈ Ico a (a + L), p i ≤ ∑ i ∈ Ico a (a + n * h), p i :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Ico_subset_Ico le_rfl (by omega)) (fun i _ _ => hp0 i)
  have hLr : (L : ℝ) < 4 * s + 1 := Nat.ceil_lt_add_one (by linarith)
  have hnr : (n : ℝ) ≤ L / h + 1 := by
    rw [hn]; push_cast
    have := Nat.cast_div_le (α := ℝ) (m := L) (n := h)
    linarith
  have hnh : (n : ℝ) * ((h : ℝ) / (10 * s)) ≤ 6 / 10 := by
    have e : (n : ℝ) * ((h : ℝ) / (10 * s)) = (n : ℝ) * h / (10 * s) := by ring
    rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
    have h3 : (n : ℝ) * h ≤ L + h := by
      calc (n : ℝ) * h ≤ (L / h + 1) * h := mul_le_mul_of_nonneg_right hnr (by linarith)
        _ = L + h := by field_simp
    nlinarith
  linarith

/-! ### Assembly -/

private lemma core {p q : ℕ → ℝ} {δ Λ s : ℝ} (hp0 : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k)
    (hm0 : HasSum p 1) (hq1 : HasSum q 1) (hΛ : 0 < Λ) (hδ : 0 < δ) (hδs : δ ≤ s) (hs1 : 1 ≤ s)
    (hconc : ∀ h : ℕ, 1 ≤ h → (h : ℝ) ≤ s →
      ∃ τ : ℕ, (h : ℝ) / (10 * s) ≤ ∑ i ∈ Ico (τ + 1 - h) (τ + 1), p i)
    (hsmall : q 0 * (1 + δ / (1 + Λ)) ≤ 1)
    (hlarge : ∀ h : ℕ, 1 ≤ h → 6 * (h : ℝ) + 3 * Λ ≤ δ → ∑ j ∈ range h, q j ≤ 1 / 2) :
    ∃ τ : ℕ, 1 / (480 + 70 * Λ) * δ / s ≤
      (∑' k, if τ < k then conv p q k else 0) - ∑' k, if τ < k then p k else 0 := by
  have hs0 : 0 < s := by linarith
  have hconv1 : HasSum (conv p q) 1 := by simpa using conv_m0 hp0 hq0 hm0 hq1
  have key : ∀ (h τ : ℕ), (∑ i ∈ Ico (τ + 1 - h) (τ + 1), p i) * (1 - ∑ j ∈ range h, q j)
      ≤ (∑' k, if τ < k then conv p q k else 0) - ∑' k, if τ < k then p k else 0 := by
    intro h τ
    rw [diff_formula hm0 hconv1 τ]
    exact diff_lower hp0 hq0 hq1 τ h
  have hW0 : ∀ (h τ : ℕ), 0 ≤ ∑ i ∈ Ico (τ + 1 - h) (τ + 1), p i :=
    fun h τ => Finset.sum_nonneg fun i _ => hp0 i
  by_cases hcase : δ ≤ 12 + 6 * Λ
  · obtain ⟨τ, hτ⟩ := hconc 1 le_rfl (by simpa using hs1)
    refine ⟨τ, le_trans ?_ (key 1 τ)⟩
    have hq01 : q 0 ≤ 1 := by
      simpa using sum_le_hasSum (range 1) (fun i _ => hq0 i) hq1
    have a1 : q 0 * (1 + Λ + δ) ≤ 1 + Λ := by
      have e : q 0 * (1 + δ / (1 + Λ)) = q 0 * (1 + Λ + δ) / (1 + Λ) := by field_simp
      rw [e, div_le_one (by positivity)] at hsmall
      exact hsmall
    have a2 : δ / (13 + 7 * Λ) ≤ 1 - ∑ j ∈ range 1, q j := by
      rw [Finset.sum_range_one, div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hq01) (sub_nonneg.mpr hcase)]
    have a3 : 1 / (10 * s) ≤ ∑ i ∈ Ico (τ + 1 - 1) (τ + 1), p i := by simpa using hτ
    calc 1 / (480 + 70 * Λ) * δ / s ≤ 1 / (10 * s) * (δ / (13 + 7 * Λ)) := by
          rw [div_le_iff₀ hs0]
          have e : 1 / (10 * s) * (δ / (13 + 7 * Λ)) * s = δ / (130 + 70 * Λ) := by
            field_simp
            ring
          rw [e, one_div_mul_eq_div]
          exact div_le_div_of_nonneg_left hδ.le (by positivity) (by linarith)
      _ ≤ _ := mul_le_mul a3 a2 (by positivity) (hW0 1 τ)
  · rw [not_le] at hcase
    have hh1 : 1 ≤ ⌊δ / 12⌋₊ :=
      Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ (by norm_num)]; linarith)
    have hhle : (⌊δ / 12⌋₊ : ℝ) ≤ δ / 12 := Nat.floor_le (by positivity)
    have hhge : δ / 12 < ⌊δ / 12⌋₊ + 1 := Nat.lt_floor_add_one _
    have hh1' : (1 : ℝ) ≤ ⌊δ / 12⌋₊ := by exact_mod_cast hh1
    obtain ⟨τ, hτ⟩ := hconc ⌊δ / 12⌋₊ hh1 (by linarith)
    have b1 := hlarge ⌊δ / 12⌋₊ hh1 (by linarith)
    refine ⟨τ, le_trans ?_ (key ⌊δ / 12⌋₊ τ)⟩
    calc 1 / (480 + 70 * Λ) * δ / s ≤ (⌊δ / 12⌋₊ : ℝ) / (10 * s) * (1 / 2) := by
          rw [div_le_iff₀ hs0]
          have e : (⌊δ / 12⌋₊ : ℝ) / (10 * s) * (1 / 2) * s = (⌊δ / 12⌋₊ : ℝ) / 20 := by
            field_simp
            ring
          rw [e, one_div_mul_eq_div]
          have c1 : δ / (480 + 70 * Λ) ≤ δ / 480 :=
            div_le_div_of_nonneg_left hδ.le (by norm_num) (by linarith)
          linarith
      _ ≤ _ := mul_le_mul hτ (by linarith) (by norm_num) (hW0 _ τ)

theorem solution :
    ∀ Λ : ℝ, 0 < Λ → ∃ c : ℝ, 0 < c ∧
      ∀ (m : ℕ) (lp lm : Fin m → ℝ), (∀ i, 0 ≤ lm i) → (∀ i, lm i ≤ lp i) → (∀ i, lp i ≤ Λ) →
      ∀ (pp pm : ℕ → ℝ), (∀ k, 0 ≤ pp k) → (∀ k, 0 ≤ pm k) →
        (∀ z : ℝ, 0 ≤ z → z ≤ 1 →
          HasSum (fun k => pp k * z ^ k) (∏ i, (1 + lp i * (1 - z))⁻¹)) →
        (∀ z : ℝ, 0 ≤ z → z ≤ 1 →
          HasSum (fun k => pm k * z ^ k) (∏ i, (1 + lm i * (1 - z))⁻¹)) →
        0 < ∑ i, (lp i - lm i) →
        (∑ i, (lp i - lm i)) ^ 2 ≤ 1 + ∑ i, lm i * (1 + lm i) →
        ∃ τ : ℕ, c * (∑ i, (lp i - lm i)) / Real.sqrt (1 + ∑ i, lm i * (1 + lm i)) ≤
          (∑' k, if τ < k then pp k else 0) - ∑' k, if τ < k then pm k else 0 := by
  intro Λ hΛ
  refine ⟨1 / (480 + 70 * Λ), by positivity, ?_⟩
  intro m lp lm h0 hle hΛb pp pm hpp0 hpm0 hppgf hpmgf hδ hδs
  obtain ⟨p, hp0, hpgf, hm0, hm1, hm2⟩ := exists_Kminus Finset.univ lm h0
  obtain ⟨q, hq0, hqgf⟩ := exists_J Finset.univ lm lp h0 hle
  have hpm : pm = p := funext fun n => pgf_unique hpm0 hp0
    (fun z hz hz1 => ⟨_, hpmgf z hz.le hz1, hpgf z hz.le hz1⟩) n
  have hq1 : HasSum q 1 := by simpa using hqgf 1 zero_le_one le_rfl
  have hpp : pp = conv p q := funext fun n => pgf_unique hpp0 (conv_nonneg hp0 hq0)
    (fun z hz hz1 => ⟨_, hppgf z hz.le hz1, by
      have h := conv_pgf hp0 hq0 hz.le (hpgf z hz.le hz1) (hqgf z hz.le hz1)
      have e : (∏ i, (1 + lm i * (1 - z))⁻¹)
          * ∏ i, ((1 + lm i * (1 - z)) * (1 + lp i * (1 - z))⁻¹)
          = ∏ i, (1 + lp i * (1 - z))⁻¹ := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        have : 0 < 1 + lm i * (1 - z) := by nlinarith [h0 i]
        rw [← mul_assoc, inv_mul_cancel₀ this.ne', one_mul]
      rw [e] at h
      exact h⟩) n
  subst hpm hpp
  have hv0 : 0 ≤ ∑ i, lm i * (1 + lm i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (h0 i) (by linarith [h0 i])
  have hs1 : 1 ≤ Real.sqrt (1 + ∑ i, lm i * (1 + lm i)) := by
    rw [Real.one_le_sqrt]; linarith
  have hs2 : Real.sqrt (1 + ∑ i, lm i * (1 + lm i)) ^ 2 = 1 + ∑ i, lm i * (1 + lm i) :=
    Real.sq_sqrt (by linarith)
  have hδs' : ∑ i, (lp i - lm i) ≤ Real.sqrt (1 + ∑ i, lm i * (1 + lm i)) :=
    (Real.le_sqrt' hδ).mpr hδs
  exact core hp0 hq0 hm0 hq1 hΛ hδ hδs' hs1
    (fun h hh hhs => concentration hp0 hm0 hm1 hm2 hs1 (by rw [hs2]; linarith) hh hhs)
    (J_small Finset.univ lm lp h0 hle hΛb hΛ.le hq0 hqgf)
    (fun h hh hδh => J_large Finset.univ lm lp h0 hle hΛb hΛ.le hq0 hqgf hh hδh)
