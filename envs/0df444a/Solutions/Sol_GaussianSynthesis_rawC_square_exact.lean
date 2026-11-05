-- Prove2me | solution 1 for GaussianSynthesis.rawC_square_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/d7b3fb60-567e-4524-89e3-47fd8c6dd8c7

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_rawC_left_square
import Theorems.Thm_GaussianSynthesis_rawC_right_square
import Theorems.Thm_GaussianSynthesis_two_pi_numerator_sameValue

set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (u v : GInt) (e : Nat) :
    let p := rawC u v e
    let q := rawC p.left p.right p.exponent
    SameValue (packedLeft q) ⟨v,e⟩ ∧ SameValue (packedRight q) ⟨u,e⟩ := by
  simp only [rawC, packedLeft, packedRight]
  rw [rawC_left_square, rawC_right_square]
  exact ⟨two_pi_numerator_sameValue v e,two_pi_numerator_sameValue u e⟩
end GaussianSynthesis
