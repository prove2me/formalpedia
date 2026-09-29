-- Prove2me | solution 1 for FamousTheorems.liouville_theorem_complex
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:11:20.319398+00:00
-- url     : https://prove2.me/submissions/943dd673-ecbc-4d01-90a9-2af0fb938f7c

import Mathlib

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} (hf : Differentiable ℂ f) (hb : Bornology.IsBounded (Set.range f)) (z w : E) :
    f z = f w :=
  hf.apply_eq_apply_of_bounded hb z w
