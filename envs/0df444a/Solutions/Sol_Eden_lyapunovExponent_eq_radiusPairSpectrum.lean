-- Prove2me | solution 1 for Eden.lyapunovExponent_eq_radiusPairSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:15:39.545361+00:00
-- url     : https://prove2.me/submissions/b59a7847-8bde-4438-9b23-b7ebdf1531f6

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SpectrumTable
import Theorems.Thm_Eden_lyapunovExponent_eq_descending


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace) :
    lyapunovExponent c p = descending (radiusPairSpectrum c
      (limitingSquaredRadius (radiusSq₁ p)) (limitingSquaredRadius (radiusSq₂ p))) := by
  funext i
  exact lyapunovExponent_eq_descending c p i
end Eden
