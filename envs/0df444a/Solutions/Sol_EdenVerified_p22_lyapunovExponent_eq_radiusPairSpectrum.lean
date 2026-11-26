-- Prove2me | solution 1 for EdenVerified.p22_lyapunovExponent_eq_radiusPairSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:33:18.428749+00:00
-- url     : https://prove2.me/submissions/a1dfcd26-929a-46d0-b275-eafeb5772aca

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_lyapunovExponent_eq_radiusPairSpectrum


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) (p : PhaseSpace),
    lyapunovExponent c p = descending (radiusPairSpectrum c
      (limitingSquaredRadius (radiusSq₁ p)) (limitingSquaredRadius (radiusSq₂ p))) :=
  @Eden.lyapunovExponent_eq_radiusPairSpectrum
end EdenVerified
