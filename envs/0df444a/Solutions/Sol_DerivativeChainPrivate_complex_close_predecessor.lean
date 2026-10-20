-- Prove2me | solution 1 for DerivativeChainPrivate.complex_close_predecessor
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-17T03:08:51.895608+00:00
-- url     : https://prove2.me/submissions/14c733c5-7036-44df-b715-0354a8a4177d

-- D3/k=1 attempt: complex one-step anchored (disk) lemma.
-- Statement: barycentric w (real weights) of unit-disk points has a
-- predecessor within √(1−|w|²). Proved via re/im split + D1-style energy
-- identity per component + D2-style min selection. No sorry (attempt).
import Mathlib

open scoped BigOperators

set_option autoImplicit false

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty)
    (p : ι → ℝ) (a : ι → ℂ) (b : ℂ)
    (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1)
    (hbre : b.re = ∑ i ∈ s, p i * (a i).re)
    (hbim : b.im = ∑ i ∈ s, p i * (a i).im)
    (hmem : ∀ i ∈ s, ‖a i‖ ≤ 1) :
    ∃ i ∈ s, ‖a i - b‖ ^ 2 ≤ 1 - ‖b‖ ^ 2 := by
  -- energy identity per component (D1 pattern twice)
  have e_re : ∑ i ∈ s, p i * ((a i).re - b.re) ^ 2
      = ∑ i ∈ s, p i * (a i).re ^ 2 - b.re ^ 2 := by
    have hexpand : ∀ i : ι, p i * ((a i).re - b.re) ^ 2
        = p i * (a i).re ^ 2 - 2 * b.re * (p i * (a i).re)
          + b.re ^ 2 * p i := by
      intro i
      ring
    have hsum_eq : ∑ i ∈ s, p i * ((a i).re - b.re) ^ 2
        = ∑ i ∈ s, (p i * (a i).re ^ 2 - 2 * b.re * (p i * (a i).re)
          + b.re ^ 2 * p i) :=
      Finset.sum_congr rfl (fun i _ => hexpand i)
    have hmid : ∑ i ∈ s, (2 * b.re * (p i * (a i).re))
        = 2 * b.re * ∑ i ∈ s, p i * (a i).re := by
      rw [Finset.mul_sum]
    have hlast : ∑ i ∈ s, (b.re ^ 2 * p i) = b.re ^ 2 * ∑ i ∈ s, p i := by
      rw [Finset.mul_sum]
    rw [hsum_eq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      hmid, hlast, ← hbre, hsum]
    ring
  have e_im : ∑ i ∈ s, p i * ((a i).im - b.im) ^ 2
      = ∑ i ∈ s, p i * (a i).im ^ 2 - b.im ^ 2 := by
    have hexpand : ∀ i : ι, p i * ((a i).im - b.im) ^ 2
        = p i * (a i).im ^ 2 - 2 * b.im * (p i * (a i).im)
          + b.im ^ 2 * p i := by
      intro i
      ring
    have hsum_eq : ∑ i ∈ s, p i * ((a i).im - b.im) ^ 2
        = ∑ i ∈ s, (p i * (a i).im ^ 2 - 2 * b.im * (p i * (a i).im)
          + b.im ^ 2 * p i) :=
      Finset.sum_congr rfl (fun i _ => hexpand i)
    have hmid : ∑ i ∈ s, (2 * b.im * (p i * (a i).im))
        = 2 * b.im * ∑ i ∈ s, p i * (a i).im := by
      rw [Finset.mul_sum]
    have hlast : ∑ i ∈ s, (b.im ^ 2 * p i) = b.im ^ 2 * ∑ i ∈ s, p i := by
      rw [Finset.mul_sum]
    rw [hsum_eq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      hmid, hlast, ← hbim, hsum]
    ring
  -- assemble with ‖z‖² = re² + im²
  have hnsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := fun z =>
    (RCLike.normSq_eq_def' z).symm.trans (RCLike.normSq_apply z)
  have hnorm : ∀ i : ι, ‖a i - b‖ ^ 2
      = ((a i).re - b.re) ^ 2 + ((a i).im - b.im) ^ 2 := by
    intro i
    rw [hnsq, Complex.sub_re, Complex.sub_im]
    ring
  have havg : ∑ i ∈ s, p i * ‖a i - b‖ ^ 2 ≤ 1 - ‖b‖ ^ 2 := by
    have hsplit : ∑ i ∈ s, p i * ‖a i - b‖ ^ 2
        = ∑ i ∈ s, p i * ((a i).re - b.re) ^ 2
          + ∑ i ∈ s, p i * ((a i).im - b.im) ^ 2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hnorm i]
      ring
    have hsec : ∑ i ∈ s, p i * ((a i).re ^ 2 + (a i).im ^ 2) ≤ 1 := by
      have ht : ∀ i ∈ s, p i * ((a i).re ^ 2 + (a i).im ^ 2) ≤ p i * 1 := by
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (hp i hi)
        have h1 : (a i).re ^ 2 + (a i).im ^ 2 ≤ 1 := by
          have hsq : (a i).re ^ 2 + (a i).im ^ 2 = ‖a i‖ ^ 2 := by
            rw [hnsq]
            ring
          rw [hsq]
          nlinarith [hmem i hi, norm_nonneg (a i)]
        linarith
      calc ∑ i ∈ s, p i * ((a i).re ^ 2 + (a i).im ^ 2)
            ≤ ∑ i ∈ s, p i * 1 := Finset.sum_le_sum ht
        _ = ∑ i ∈ s, p i := by simp
        _ = 1 := hsum
    have hb2 : ‖b‖ ^ 2 = b.re ^ 2 + b.im ^ 2 := by
      rw [hnsq]
      ring
    rw [hsplit, e_re, e_im, hb2]
    have hsplit2 : ∑ i ∈ s, p i * (a i).re ^ 2
        + ∑ i ∈ s, p i * (a i).im ^ 2
        = ∑ i ∈ s, p i * ((a i).re ^ 2 + (a i).im ^ 2) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    linarith
  -- min selection (D2 Step 3 pattern)
  obtain ⟨i₀, hi₀mem, hi₀min⟩ :=
    Finset.exists_min_image s (fun i => ‖a i - b‖ ^ 2) hs
  have hmin_le : ∀ i ∈ s, ‖a i₀ - b‖ ^ 2 ≤ ‖a i - b‖ ^ 2 := by
    intro i hi
    exact hi₀min i hi
  have hsingle : ‖a i₀ - b‖ ^ 2 ≤ ∑ i ∈ s, p i * ‖a i - b‖ ^ 2 := by
    have hbase : ‖a i₀ - b‖ ^ 2 = ∑ i ∈ s, p i * ‖a i₀ - b‖ ^ 2 := by
      conv_lhs => rw [← one_mul (‖a i₀ - b‖ ^ 2), ← hsum, Finset.sum_mul]
    rw [hbase]
    exact Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_left (hmin_le i hi) (hp i hi))
  exact ⟨i₀, hi₀mem, le_trans hsingle havg⟩
