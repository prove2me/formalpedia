-- Prove2me | solution 1 for CohnElkies.lowerStripCappedGammaOuter_abs_re_le_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/10ac6553-6825-4c20-a47a-75e8a185fe2d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerStripCappedGammaOuter_re_dimension
import Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_poisson_abs_le_linear

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
    {d : ℕ} (hd : 0 < d) (R D : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ z : ℂ,
        z ∈ Complex.im ⁻¹'
          Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2) →
        |(lowerStripCappedGammaOuter
          ((d : ℝ) / 2) R D z).re| ≤
          B * (1 + |z.re|) := by
  let ℓ : ℝ := (d : ℝ) / 2
  have hℓ : 0 < ℓ :=
    half_pos (Nat.cast_pos.mpr hd)
  obtain ⟨B, hB, hbound⟩ :=
    lowerGammaBoundaryCapped_poisson_abs_le_linear
      hd R D
  refine ⟨B, hB, ?_⟩
  intro z hz
  have hzbelow : -ℓ < z.im := hz.1
  have hzabove : z.im < ℓ := hz.2
  let σ : ℝ := z.im / ℓ
  have hσbelow : -1 < σ := by
    try dsimp [σ]
    apply (lt_div_iff₀ hℓ).2
    simpa using! hzbelow
  have hσabove : σ < 1 := by
    try dsimp [σ]
    apply (div_lt_iff₀ hℓ).2
    simpa using! hzabove
  have hzrep :
      (z.re : ℂ) +
        Complex.I * ((σ * ℓ : ℝ) : ℂ) = z := by
    apply Complex.ext
    · simp
    · simp [σ, hℓ.ne']
  have hreal := lowerStripCappedGammaOuter_re_dimension
    hd hσbelow hσabove z.re (R := R) (D := D)
  rw [hzrep] at hreal
  rw [hreal]
  exact hbound σ hσbelow hσabove z.re
end CohnElkies
