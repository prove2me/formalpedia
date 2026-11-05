-- Prove2me | solution 1 for GaussianSynthesis.recoverIfImage_rejects
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/6407bf07-dcef-4143-8035-52fd106d4e72

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_producer_image_iff_roundtrip

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution {A B : Type} [DecidableEq B]
    (P : A → B) (Q : B → A) (hQP : ∀ x, Q (P x) = x) (d : B) :
    recoverIfImage P Q d = none ↔ ¬ ∃ x, P x = d := by
  unfold recoverIfImage
  rw [producer_image_iff_roundtrip P Q hQP d]
  by_cases h : P (Q d) = d <;> simp [h]
end GaussianSynthesis
