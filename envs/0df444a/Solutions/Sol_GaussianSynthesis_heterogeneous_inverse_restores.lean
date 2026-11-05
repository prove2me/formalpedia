-- Prove2me | solution 1 for GaussianSynthesis.heterogeneous_inverse_restores
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/404b62fd-51ac-4f0f-9a86-dccdd881aa45

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_rawC_inverse_exact
import Theorems.Thm_GaussianParity_SameValue_trans
import Theorems.Thm_GaussianParity_alignedButterfly_input_exact


set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (x y : Fraction) :
    SameValue (packedLeft (rawCInverse (rawAlignedC x y))) x ∧
    SameValue (packedRight (rawCInverse (rawAlignedC x y))) y := by
  have hc := rawC_inverse_exact
    (raiseTo x (commonExponent x y)).numerator
    (raiseTo y (commonExponent x y)).numerator (commonExponent x y)
  have ha := alignedButterfly_input_exact x y
  exact ⟨SameValue.trans hc.1 ha.1,SameValue.trans hc.2 ha.2⟩
end GaussianSynthesis
