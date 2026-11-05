-- Prove2me | solution 1 for GaussianSynthesis.producer_projection_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/2a41e3ba-7bc7-4a4d-98a0-79b92f6016db

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution {A B : Type}
    (P : A → B) (Q : B → A) (hQP : ∀ x, Q (P x) = x) (d : B) :
    P (Q (P (Q d))) = P (Q d) := by rw [hQP (Q d)]
end GaussianSynthesis
