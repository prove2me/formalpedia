-- Prove2me | solution 1 for GaussianSynthesis.producer_image_iff_roundtrip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/61d652d1-43e9-4159-b4e0-bf4fafbdb9de

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution {A B : Type}
    (P : A → B) (Q : B → A) (hQP : ∀ x, Q (P x) = x) (d : B) :
    (∃ x, P x = d) ↔ P (Q d) = d := by
  constructor
  · intro ⟨x,hx⟩
    rw [← hx,hQP x]
  · intro h
    exact ⟨Q d,h⟩
end GaussianSynthesis
