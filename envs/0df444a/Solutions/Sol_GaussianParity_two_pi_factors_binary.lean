-- Prove2me | solution 1 for GaussianParity.two_pi_factors_binary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/15b1495f-1e6d-436e-a346-886f6ac11e09

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_gaussianMul_pi_pi
import Theorems.Thm_GaussianParity_dividePi_exact_iff


set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (u v : GInt) (hu : PiDvd u) (hv : PiDvd v) :
    BinaryDivisible 1 (gaussianMul u v) := by
  refine ⟨mulI (gaussianMul (dividePi u) (dividePi v)), ?_⟩
  change scale 2 (mulI (gaussianMul (dividePi u) (dividePi v))) = gaussianMul u v
  rw [← gaussianMul_pi_pi, (dividePi_exact_iff u).mpr hu,
      (dividePi_exact_iff v).mpr hv]
end GaussianParity
