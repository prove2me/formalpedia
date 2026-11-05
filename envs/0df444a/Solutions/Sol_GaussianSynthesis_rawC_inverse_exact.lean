-- Prove2me | solution 1 for GaussianSynthesis.rawC_inverse_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/66aa7e30-3f8e-4e79-af57-73db307ff7ef

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_rawC_square_exact

set_option autoImplicit true
open GaussianSynthesis
open GaussianParity
namespace GaussianSynthesis
theorem _root_.solution (u v : GInt) (e : Nat) :
    SameValue (packedLeft (rawCInverse (rawC u v e))) ⟨u,e⟩ ∧
    SameValue (packedRight (rawCInverse (rawC u v e))) ⟨v,e⟩ := by
  have h := rawC_square_exact u v e
  exact ⟨h.2,h.1⟩
end GaussianSynthesis
