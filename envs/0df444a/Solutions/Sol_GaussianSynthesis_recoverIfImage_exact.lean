-- Prove2me | solution 1 for GaussianSynthesis.recoverIfImage_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/1ab333af-97d8-4759-85c8-cf36a7b638e5

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_producer_image_iff_roundtrip

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution {A B : Type} [DecidableEq B]
    (P : A → B) (Q : B → A) (hQP : ∀ x, Q (P x) = x) (d : B) (x : A) :
    recoverIfImage P Q d = some x ↔ P x = d := by
  unfold recoverIfImage
  by_cases h : P (Q d) = d
  · simp only [h,↓reduceIte,Option.some.injEq]
    constructor
    · intro hx
      rw [← hx]
      exact h
    · intro hx
      rw [← hx,hQP]
  · simp only [h,↓reduceIte]
    constructor
    · intro impossible
      cases impossible
    · intro hx
      have hc := (producer_image_iff_roundtrip P Q hQP d).mp ⟨x,hx⟩
      exact False.elim (h hc)
end GaussianSynthesis
