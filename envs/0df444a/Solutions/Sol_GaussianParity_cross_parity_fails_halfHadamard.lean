-- Prove2me | solution 1 for GaussianParity.cross_parity_fails_halfHadamard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.342874+00:00
-- url     : https://prove2.me/submissions/2c859f10-1ba6-40ef-bbf0-b2e355438c4b

import Std
import Definitions.Def_DyadicCertificates

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution :
    ¬ (scaleTwo (halfHadamard ⟨1, 0⟩ ⟨0, 1⟩).1 = add ⟨1, 0⟩ ⟨0, 1⟩) := by
  decide
end GaussianParity
