-- Prove2me | solution 1 for GaussianParity.pi_not_binary_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/4428a661-e53f-4d68-8c1e-c9b7f2e72193

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution :
    PiPowerDivisible 1 ⟨1,1⟩ ∧ ¬ BinaryDivisible 1 ⟨1,1⟩ := by
  constructor
  · exact ⟨⟨1,0⟩, rfl⟩
  · intro ⟨w, hw⟩
    have hr := congrArg GInt.re hw
    simp [scale] at hr
    omega
end GaussianParity
