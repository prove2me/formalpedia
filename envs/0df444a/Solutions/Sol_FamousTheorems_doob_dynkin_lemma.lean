-- Prove2me | solution 1 for FamousTheorems.doob_dynkin_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:46:27.294735+00:00
-- url     : https://prove2.me/submissions/528945d0-833a-4258-b414-c8a712b431f6

import Mathlib

theorem solution {X Y Z : Type*} [mY : MeasurableSpace Y] [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    {f : X → Y} {g : X → Z} (hg : @Measurable X Z (MeasurableSpace.comap f mY) _ g) :
    ∃ h : Y → Z, Measurable h ∧ g = h ∘ f :=
  Measurable.exists_eq_measurable_comp hg
