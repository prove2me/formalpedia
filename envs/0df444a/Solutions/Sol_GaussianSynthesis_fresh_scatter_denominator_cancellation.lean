-- Prove2me | solution 1 for GaussianSynthesis.fresh_scatter_denominator_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/a8b67d6d-dd7a-4cad-b8d6-03cf06322aaa

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution
    (T selectedInsideG selectedOutsideG selectedD selectedB N k : Int)
    (hD : selectedD = k*T-selectedInsideG)
    (hB : selectedB = 2*selectedOutsideG)
    (hN : N = -32*T) :
    scatterNumerator64 selectedB selectedD N k =
      32*(selectedInsideG+selectedOutsideG-T) := by
  simp only [scatterNumerator64]
  subst selectedD
  subst selectedB
  subst N
  grind
end GaussianSynthesis
