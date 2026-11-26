-- Prove2me | solution 1 for Eden.exponentSum_on_torus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:17:06.724874+00:00
-- url     : https://prove2.me/submissions/cc490921-497f-4240-8250-533e28349967

import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_ExponentSums
import Theorems.Thm_Eden_descending_radiusPairSpectrum_one_one
import Theorems.Thm_Eden_lyapunovExponent_eq_radiusPairSpectrum


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) {p : PhaseSpace}
    (hp : p ∈ torus) : lyapunovExponent c p = ![2, 2, 0, 0, -c] := by
  rw [lyapunovExponent_eq_radiusPairSpectrum, hp.1, hp.2.1]
  norm_num [limitingSquaredRadius]
  exact descending_radiusPairSpectrum_one_one hc
end Eden
