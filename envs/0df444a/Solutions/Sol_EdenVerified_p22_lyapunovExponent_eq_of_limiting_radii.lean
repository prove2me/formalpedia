-- Prove2me | solution 1 for EdenVerified.p22_lyapunovExponent_eq_of_limiting_radii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:33:48.529739+00:00
-- url     : https://prove2.me/submissions/00353281-d77b-4ebe-9f06-5a6f48ee7600

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_lyapunovExponent_eq_of_limiting_radii


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) (p : PhaseSpace) {s₁ s₂ : ℝ}
    (h : (limitingSquaredRadius (radiusSq₁ p) = s₁ ∧
        limitingSquaredRadius (radiusSq₂ p) = s₂) ∨
      (limitingSquaredRadius (radiusSq₁ p) = s₂ ∧
        limitingSquaredRadius (radiusSq₂ p) = s₁)),
    lyapunovExponent c p = descending (radiusPairSpectrum c s₁ s₂) :=
  @Eden.lyapunovExponent_eq_of_limiting_radii
end EdenVerified
