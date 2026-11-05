-- Prove2me | solution 1 for GaussianSynthesis.image_difference_recovers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/f15fcf10-f93c-4b3b-aec3-de71bf8ab94b

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution {A B : Type}
    (P : A → B) (Q : B → A) (hQP : ∀ x, Q (P x) = x)
    (d : B) (x : A) (hd : d = P x) :
    Q d = x ∧ P (Q d) = d := by
  constructor
  · rw [hd,hQP]
  · rw [hd,hQP]
end GaussianSynthesis
