-- Prove2me | solution 1 for FamousTheorems.affine_communication_lemma_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:05:43.044588+00:00
-- url     : https://prove2.me/submissions/6632b357-f20f-4aaa-b5e1-c3e869a5e76d

import Mathlib

open Opposite

theorem solution {X : AlgebraicGeometry.Scheme} {P : X.affineOpens → Prop} {ι : Sort*} (U : ι → X.affineOpens)
    (hU : ⨆ i, (U i : X.Opens) = ⊤) (V : X.affineOpens)
    (hbasic : ∀ (U : X.affineOpens) (f : X.presheaf.obj (op U)), P U → P (X.affineBasicOpen f))
    (hglue : ∀ (U : X.affineOpens) (s : Finset (X.presheaf.obj (op U))),
      Ideal.span (s : Set (X.presheaf.obj (op U))) = ⊤ → (∀ f : s, P (X.affineBasicOpen f.1)) → P U)
    (hP : ∀ i, P (U i)) : P V :=
  AlgebraicGeometry.of_affine_open_cover U hU V hbasic hglue hP
