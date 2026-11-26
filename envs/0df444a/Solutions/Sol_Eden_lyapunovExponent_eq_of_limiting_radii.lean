-- Prove2me | solution 1 for Eden.lyapunovExponent_eq_of_limiting_radii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:17:25.364468+00:00
-- url     : https://prove2.me/submissions/b351c1a9-2c76-4b71-a2da-61e17000fc7c

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SpectrumTable
import Theorems.Thm_Eden_lyapunovExponent_eq_radiusPairSpectrum
import Theorems.Thm_Eden_descending_radiusPairSpectrum_swap

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace) {s₁ s₂ : ℝ}
    (h : (limitingSquaredRadius (radiusSq₁ p) = s₁ ∧
        limitingSquaredRadius (radiusSq₂ p) = s₂) ∨
      (limitingSquaredRadius (radiusSq₁ p) = s₂ ∧
        limitingSquaredRadius (radiusSq₂ p) = s₁)) :
    lyapunovExponent c p = descending (radiusPairSpectrum c s₁ s₂) := by
  rw [lyapunovExponent_eq_radiusPairSpectrum]
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂]
  · rw [h₁, h₂, descending_radiusPairSpectrum_swap c s₂ s₁]
end Eden
