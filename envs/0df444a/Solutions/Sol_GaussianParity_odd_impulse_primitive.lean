-- Prove2me | solution 1 for GaussianParity.odd_impulse_primitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/a59d69e2-cb45-4956-8b6c-b97352556150

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_bothOdd_repeatNegI

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (q : Nat) :
    ¬ BinaryDivisible 1 (repeatNegI (q+1) (mulPi ⟨1,0⟩)) := by
  intro ⟨w, hw⟩
  have hp : BothOdd (mulPi ⟨1,0⟩) := by simp [BothOdd, mulPi]
  have hb := bothOdd_repeatNegI (q+1) _ hp
  have hr := congrArg GInt.re hw
  simp only [scale, BothOdd] at hr hb
  omega
end GaussianParity
