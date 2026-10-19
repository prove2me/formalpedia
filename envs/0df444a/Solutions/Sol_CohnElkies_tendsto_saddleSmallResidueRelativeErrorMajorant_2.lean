-- Prove2me | solution 2 for CohnElkies.tendsto_saddleSmallResidueRelativeErrorMajorant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:13:06.970409+00:00
-- url     : https://prove2.me/submissions/672da248-0fe3-4745-a40b-ad8828b8cb1b

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    (K C : ℝ) :
    Tendsto (saddleSmallResidueRelativeErrorMajorant K C)
      atTop (𝓝 0) := by
  have hE0 : ∀ (j : ℕ) {c : ℝ}, 0 < c →
      Tendsto (fun x : ℝ => x ^ j * Real.exp (-(c * x))) atTop (𝓝 0) := by
    intro j c hc
    have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero j).comp
      (Tendsto.const_mul_atTop hc tendsto_id)
    have h2 := h1.const_mul ((c ^ j)⁻¹)
    rw [mul_zero] at h2
    refine h2.congr (fun x => ?_)
    simp only [Function.comp, id]
    rw [mul_pow]
    field_simp
  have hE : ∀ (j : ℕ) {c : ℝ}, 0 < c →
      Tendsto (fun ℓ : ℝ => Real.log ℓ ^ j * Real.exp (-(c * Real.log ℓ))) atTop (𝓝 0) :=
    fun j c hc => (hE0 j hc).comp Real.tendsto_log_atTop
  have hN : Tendsto (fun ℓ : ℝ => (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ) atTop (𝓝 0) := by
    have hup := (((hE 2 one_pos).const_mul 400).add ((hE 1 one_pos).const_mul 40)).add (hE 0 one_pos)
    simp only [mul_zero, add_zero] at hup
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    · filter_upwards [eventually_gt_atTop 0] with ℓ hℓ
      exact div_nonneg (sq_nonneg _) hℓ.le
    · filter_upwards [eventually_gt_atTop 1] with ℓ hℓ
      have hl : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ.le
      have hc : (saddleSmallResidueTruncation ℓ : ℝ) ≤ 20 * Real.log ℓ + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
      have hn0 : (0:ℝ) ≤ saddleSmallResidueTruncation ℓ := Nat.cast_nonneg _
      have hexp : Real.exp (-Real.log ℓ) = ℓ⁻¹ := by
        rw [Real.exp_neg, Real.exp_log (by linarith)]
      simp only [one_mul, pow_one, pow_zero, hexp]
      rw [div_eq_mul_inv]
      have hinv : 0 < ℓ⁻¹ := inv_pos.mpr (by linarith)
      have hsq : (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 ≤ (20 * Real.log ℓ + 1) ^ 2 :=
        pow_le_pow_left₀ hn0 hc 2
      have := mul_le_mul_of_nonneg_right hsq hinv.le
      nlinarith [this]
  have hexpK : Tendsto (fun ℓ : ℝ => Real.exp (K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ))
      atTop (𝓝 1) := by
    have hNK := hN.const_mul K
    rw [mul_zero] at hNK
    have := (Real.continuous_exp.tendsto 0).comp hNK
    simp only [mul_zero, Real.exp_zero] at this
    refine this.congr (fun ℓ => ?_)
    simp only [Function.comp]
    ring_nf
  have hP : Tendsto (fun ℓ : ℝ => (2 * (Real.log ℓ / 8 + C) + (Real.log ℓ / 8 + C) ^ 2) *
      Real.exp (2 * C - (3 / 4 : ℝ) * Real.log ℓ)) atTop (𝓝 0) := by
    have h := (((hE 2 (c := 3/4) (by norm_num)).const_mul (1/64)).add
      ((hE 1 (c := 3/4) (by norm_num)).const_mul ((2 + 2 * C) / 8))).add
      ((hE 0 (c := 3/4) (by norm_num)).const_mul (2 * C + C ^ 2))
    have h' := h.const_mul (Real.exp (2 * C))
    simp only [mul_zero, add_zero] at h'
    refine h'.congr (fun ℓ => ?_)
    rw [show 2 * C - (3 / 4 : ℝ) * Real.log ℓ = 2 * C + (-((3 / 4 : ℝ) * Real.log ℓ)) by ring,
      Real.exp_add]
    ring
  have h2 : Tendsto (fun ℓ : ℝ => Real.exp (3 * C - (77 / 8 : ℝ) * Real.log ℓ)) atTop (𝓝 0) := by
    have h' := (hE 0 (c := 77/8) (by norm_num)).const_mul (Real.exp (3 * C))
    rw [mul_zero] at h'
    refine h'.congr (fun ℓ => ?_)
    rw [show 3 * C - (77 / 8 : ℝ) * Real.log ℓ = 3 * C + (-((77 / 8 : ℝ) * Real.log ℓ)) by ring,
      Real.exp_add]
    ring
  unfold saddleSmallResidueRelativeErrorMajorant saddleSmallResidueCoefficientMajorant
    saddleSmallResidueTailMajorant
  have hfin := ((hexpK.const_mul K).mul hP).add (h2.const_mul 2)
  simp only [mul_one, mul_zero, add_zero] at hfin
  refine hfin.congr (fun ℓ => ?_)
  ring

