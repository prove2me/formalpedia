-- Prove2me | solution 1 for CohnElkies.antiFourierWitness_cappedWeightedMellinStrip_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/c3d53f5c-af03-44c2-8746-16ccba544343

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_antiFourierWitness_normalizedMellinStrip_uniform_bound
import Theorems.Thm_CohnElkies_lowerStripCappedGammaOuter_abs_re_le_linear

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) {R : ℝ}
    (w : AntiFourierWitness d R) (D : ℝ) :
    ∃ c < Real.pi /
        (((d : ℝ) / 2) - (-((d : ℝ) / 2))),
      ∃ B : ℝ,
        Asymptotics.IsBigO
          (Filter.comap
              (fun z : ℂ => |z.re|) Filter.atTop ⊓
            Filter.principal
              (Complex.im ⁻¹'
                Ioo (-((d : ℝ) / 2))
                    ((d : ℝ) / 2)))
          (fun z : ℂ =>
            Complex.exp
                (-(lowerStripCappedGammaOuter
                  ((d : ℝ) / 2) R D z)) *
              normalizedRadialMellinStrip
                hd w.function R z)
          (fun z : ℂ =>
            Real.exp
              (B * Real.exp (c * |z.re|))) := by
  let ℓ : ℝ := (d : ℝ) / 2
  have hℓ : 0 < ℓ :=
    half_pos (Nat.cast_pos.mpr hd)
  obtain ⟨G, hG, houter⟩ :=
    lowerStripCappedGammaOuter_abs_re_le_linear
      hd R D
  obtain ⟨K, hK, hwitness⟩ :=
    antiFourierWitness_normalizedMellinStrip_uniform_bound
      hd w
  let c : ℝ := Real.pi / (4 * ℓ)
  have hc : 0 < c := by
    try dsimp [c]
    positivity
  have hclt : c < Real.pi / (ℓ - (-ℓ)) := by
    try dsimp [c]
    apply (div_lt_div_iff₀
      (by positivity : 0 < 4 * ℓ)
      (by linarith : 0 < ℓ - (-ℓ))).2
    nlinarith [Real.pi_pos, hℓ]
  let B : ℝ := G * (1 + 1 / c)
  refine ⟨c, hclt, B, ?_⟩
  apply Asymptotics.IsBigO.of_bound (K + 1)
  apply Filter.eventually_inf_principal.mpr
  refine Filter.Eventually.of_forall ?_
  intro z hz
  have hzbelow : -ℓ < z.im := hz.1
  have hzabove : z.im < ℓ := hz.2
  have hZ := hwitness z hzbelow.le hzabove.le
  have hW := houter z hz
  have hre :
      -(lowerStripCappedGammaOuter ℓ R D z).re ≤
        G * (1 + |z.re|) := by
    exact le_trans
      (neg_le_abs _) hW
  have hexpcomparison :
      G * (1 + |z.re|) ≤
        B * Real.exp (c * |z.re|) := by
    have hx : 0 ≤ |z.re| := abs_nonneg _
    have hcinv : 0 ≤ 1 / c := by positivity
    have hsmall :
        1 + |z.re| ≤
          (1 + 1 / c) *
            Real.exp (c * |z.re|) := by
      calc
        1 + |z.re| ≤
            (1 + 1 / c) *
              (1 + c * |z.re|) := by
          have hcx : 0 ≤ c * |z.re| :=
            mul_nonneg hc.le hx
          have hrecip : (1 / c) * c = 1 := by
            field_simp [hc.ne']
          nlinarith [mul_nonneg hcinv hcx]
        _ ≤ (1 + 1 / c) *
              Real.exp (c * |z.re|) := by
          apply mul_le_mul_of_nonneg_left
            (show 1 + c * |z.re| ≤
              Real.exp (c * |z.re|) by
              simpa [add_comm] using!
                Real.add_one_le_exp (c * |z.re|))
            (by positivity)
    try dsimp [B]
    calc
      G * (1 + |z.re|) ≤
          G * ((1 + 1 / c) *
            Real.exp (c * |z.re|)) :=
        mul_le_mul_of_nonneg_left hsmall hG
      _ = G * (1 + 1 / c) *
          Real.exp (c * |z.re|) := by ring
  rw [norm_mul, Complex.norm_exp,
    Complex.neg_re, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp
        (-(lowerStripCappedGammaOuter ℓ R D z).re) *
        ‖normalizedRadialMellinStrip
          hd w.function R z‖ ≤
      Real.exp
        (G * (1 + |z.re|)) * K := by
      apply mul_le_mul
        (Real.exp_le_exp.mpr hre) hZ
        (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp
        (B * Real.exp (c * |z.re|)) * K := by
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr hexpcomparison) hK
    _ ≤ (K + 1) *
        Real.exp
          (B * Real.exp (c * |z.re|)) := by
      nlinarith [Real.exp_pos
        (B * Real.exp (c * |z.re|))]
end CohnElkies
