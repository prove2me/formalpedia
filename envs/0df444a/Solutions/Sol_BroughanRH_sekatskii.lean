-- Prove2me | solution 1 for BroughanRH.sekatskii
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:42:24.301879+00:00
-- url     : https://prove2.me/submissions/87f0f1f2-9a9b-4c2f-adc7-6e842a2beb13
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_ConnesRZ_actual_zero_reciprocal_square_summable

open Complex

lemma zs_unit_re (v : ℂ) (hv : ‖v‖ = 1) : (1 - v).re = ‖1 - v‖ ^ 2 / 2 := by
  have h1 : v.re ^ 2 + v.im ^ 2 = 1 := by
    have := Complex.sq_norm v
    rw [hv, Complex.normSq_apply] at this
    nlinarith
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  nlinarith

lemma zs_pow_bound (w : ℂ) (hw : ‖w‖ = 1) (n : ℕ) : ‖1 - w ^ n‖ ≤ n * ‖1 - w‖ := by
  induction n with
  | zero => simp
  | succ k ih =>
    have : 1 - w ^ (k + 1) = (1 - w ^ k) + w ^ k * (1 - w) := by ring
    rw [this]
    calc ‖(1 - w ^ k) + w ^ k * (1 - w)‖ ≤ ‖1 - w ^ k‖ + ‖w ^ k * (1 - w)‖ := norm_add_le _ _
      _ ≤ k * ‖1 - w‖ + ‖1 - w‖ := by
          gcongr
          rw [norm_mul, norm_pow, hw]; simp
      _ = ((k + 1 : ℕ) : ℝ) * ‖1 - w‖ := by push_cast; ring

lemma zs_re_bounds (w : ℂ) (hw : ‖w‖ = 1) (n : ℕ) :
    0 ≤ (1 - w ^ n).re ∧ (1 - w ^ n).re ≤ (n : ℝ) ^ 2 * ‖1 - w‖ ^ 2 / 2 := by
  have hwn : ‖w ^ n‖ = 1 := by rw [norm_pow, hw, one_pow]
  rw [zs_unit_re _ hwn]
  refine ⟨by positivity, ?_⟩
  have := zs_pow_bound w hw n
  have h0 : 0 ≤ ‖1 - w ^ n‖ := norm_nonneg _
  have : ‖1 - w ^ n‖ ^ 2 ≤ (n * ‖1 - w‖) ^ 2 := by gcongr
  nlinarith

/-- Under RH, every critical-strip zero lies on the critical line. -/
lemma zs_re_half (s : ℂ) (hs : ConnesRZ.IsCriticalZero s) : s.re = 1 / 2 := by
  obtain ⟨hz, h0, h1⟩ := hs
  refine riemann_hypothesis s hz ?_ ?_
  · rintro ⟨n, rfl⟩
    simp at h0
    have : (0:ℝ) ≤ n := n.cast_nonneg
    linarith
  · rintro rfl; simp at h1

lemma zs_normSq_shift (s : ℂ) (hs : s.re = 1 / 2) :
    Complex.normSq ((s - 1 / 2) / Complex.I) = s.im ^ 2 := by
  rw [Complex.normSq_div, Complex.normSq_I, div_one, Complex.normSq_apply]
  simp [hs]; ring

theorem solution :
    let Z := {s : ℂ // ConnesRZ.IsCriticalZero s}
    ∀ a : ℝ, a < 1/2 → ∀ n : ℕ, 0 < n →
      let u (ρ : Z) : ℝ := (ConnesRZ.zeroMult ρ.val : ℝ) * (1 - ((ρ.val - (a : ℂ)) / (ρ.val + (a : ℂ)-1))^n).re
      Summable u ∧ 0 ≤ ∑' ρ : Z, u ρ := by
  intro Z a ha n hn u
  set b := 1 / 2 - a with hb
  have hb0 : 0 < b := by rw [hb]; linarith
  have hbd : ∀ ρ : Z, 0 ≤ u ρ ∧ u ρ ≤ (2 * (n : ℝ) ^ 2 * (b ^ 2 + 1)) *
      ((ConnesRZ.zeroMult ρ.1 : ℝ) / (1 + Complex.normSq ((ρ.1 - 1 / 2) / Complex.I))) := by
    intro ρ
    have hre := zs_re_half ρ.val ρ.2
    set γ := ρ.val.im with hγ
    have hden : Complex.normSq (ρ.val + (a : ℂ) - 1) = b ^ 2 + γ ^ 2 := by
      rw [Complex.normSq_apply]; simp [hre, hb]; ring_nf <;> rfl
    have hnum : Complex.normSq (ρ.val - (a : ℂ)) = b ^ 2 + γ ^ 2 := by
      rw [Complex.normSq_apply]; simp [hre, hb]; ring_nf <;> rfl
    have hpos : 0 < b ^ 2 + γ ^ 2 := by positivity
    have hne : ρ.val + (a : ℂ) - 1 ≠ 0 := by
      intro h; rw [h, Complex.normSq_zero] at hden; linarith
    set w := (ρ.val - (a : ℂ)) / (ρ.val + (a : ℂ) - 1) with hw
    have hwn : ‖w‖ = 1 := by
      rw [hw, norm_div]
      have : ‖ρ.val - (a : ℂ)‖ = ‖ρ.val + (a : ℂ) - 1‖ := by
        rw [← Real.sqrt_sq (norm_nonneg (ρ.val - (a : ℂ))),
          ← Real.sqrt_sq (norm_nonneg (ρ.val + (a : ℂ) - 1)),
          Complex.sq_norm, Complex.sq_norm, hden, hnum]
      rw [this, div_self (norm_ne_zero_iff.mpr hne)]
    have h1w : ‖1 - w‖ ^ 2 = 4 * b ^ 2 / (b ^ 2 + γ ^ 2) := by
      have : 1 - w = (-(2 * b : ℝ) : ℂ) / (ρ.val + (a : ℂ) - 1) := by
        rw [hw]; field_simp; push_cast; rw [hb]; push_cast; ring
      rw [this, Complex.sq_norm, Complex.normSq_div, hden, Complex.normSq_neg, Complex.normSq_ofReal]; ring
    obtain ⟨b0, b1⟩ := zs_re_bounds w hwn n
    rw [h1w] at b1
    rw [zs_normSq_shift _ hre]
    have hm : (0 : ℝ) ≤ ConnesRZ.zeroMult ρ.val := Nat.cast_nonneg _
    refine ⟨mul_nonneg hm b0, ?_⟩
    have hg : 0 ≤ γ ^ 2 := sq_nonneg _
    have key : (n : ℝ) ^ 2 * (4 * b ^ 2 / (b ^ 2 + γ ^ 2)) / 2 ≤
        2 * (n : ℝ) ^ 2 * (b ^ 2 + 1) / (1 + γ ^ 2) := by
      have e : (n : ℝ) ^ 2 * (4 * b ^ 2 / (b ^ 2 + γ ^ 2)) / 2 = 2 * (n : ℝ) ^ 2 * b ^ 2 / (b ^ 2 + γ ^ 2) := by ring
      rw [e, div_le_div_iff₀ hpos (by positivity)]
      have : (0:ℝ) ≤ (n:ℝ)^2 := sq_nonneg _
      have hb2 : 0 ≤ b ^ 2 := sq_nonneg _
      have : b ^ 2 * (1 + γ ^ 2) ≤ (b ^ 2 + 1) * (b ^ 2 + γ ^ 2) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ 2 * (n:ℝ)^2)]
    calc (ConnesRZ.zeroMult ρ.val : ℝ) * (1 - w ^ n).re
        ≤ (ConnesRZ.zeroMult ρ.val : ℝ) * (2 * (n : ℝ) ^ 2 * (b ^ 2 + 1) / (1 + γ ^ 2)) :=
          mul_le_mul_of_nonneg_left (b1.trans key) hm
      _ = _ := by ring
  have hsum : Summable u :=
    Summable.of_nonneg_of_le (fun ρ => (hbd ρ).1) (fun ρ => (hbd ρ).2)
      (ConnesRZ.actual_zero_reciprocal_square_summable.mul_left _)
  exact ⟨hsum, tsum_nonneg (fun ρ => (hbd ρ).1)⟩
