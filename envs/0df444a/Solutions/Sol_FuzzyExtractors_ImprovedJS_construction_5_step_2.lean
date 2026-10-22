-- Prove2me | solution 1 for FuzzyExtractors.ImprovedJS.construction_5_step_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:11:28.684341+00:00
-- url     : https://prove2.me/submissions/fdb731d4-5af9-4e59-bdb6-edb0267c399b

import Mathlib
import Definitions.Def_FuzzyExtractors_ImprovedJS_Basic

set_option autoImplicit false
open FuzzyExtractors.ImprovedJS

theorem solution {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] (s t : ℕ) (hts : t ≤ s)
    (w : Finset 𝔽) (hw : w.card = s) (k : Fin t) :
    sketchCoeffs s t w k = (-1) ^ ((k : ℕ) + 1) * w.val.esymm ((k : ℕ) + 1) := by
  have hk : (k : ℕ) < t := k.2
  have hcard : Multiset.card w.val = s := hw
  have h1 : s - 1 - (k : ℕ) ≤ Multiset.card w.val := by omega
  have h2 := Multiset.prod_X_sub_C_coeff w.val h1
  have h3 : Multiset.card w.val - (s - 1 - (k : ℕ)) = (k : ℕ) + 1 := by omega
  rw [h3] at h2
  unfold sketchCoeffs charPoly
  exact h2
