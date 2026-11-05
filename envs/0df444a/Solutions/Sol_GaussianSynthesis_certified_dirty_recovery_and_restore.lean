-- Prove2me | solution 1 for GaussianSynthesis.certified_dirty_recovery_and_restore
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/df7d6f21-303e-44cb-8b98-4d9dc7690f86

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_image_difference_recovers

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution {A B : Type} [Sub B]
    (P : A → B) (Q : B → A) (hQP : ∀ x, Q (P x) = x)
    (old updated : B) (x : A)
    (himage : updated-old = P x)
    (hrestore : updated-(updated-old) = old) :
    Q (updated-old) = x ∧
    P (Q (updated-old)) = updated-old ∧
    updated-P (Q (updated-old)) = old := by
  have h := image_difference_recovers P Q hQP (updated-old) x himage
  exact ⟨h.1,h.2,by rw [h.2]; exact hrestore⟩
end GaussianSynthesis
