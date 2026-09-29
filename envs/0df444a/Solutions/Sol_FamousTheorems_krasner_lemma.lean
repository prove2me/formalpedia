-- Prove2me | solution 1 for FamousTheorems.krasner_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:11:32.611191+00:00
-- url     : https://prove2.me/submissions/6b506f97-e1c6-4119-a8b8-583e4969319f

import Mathlib

theorem solution {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L]
    [NormedAlgebra K L] [Algebra.IsAlgebraic K L] {x y : L} (hx : (minpoly K x).Separable)
    (sp : ((minpoly K x).map (algebraMap K L)).Splits) (hy : IsIntegral K y)
    (h : ∀ x' : L, IsConjRoot K x x' → x ≠ x' → ‖x - y‖ < ‖x - x'‖) :
    x ∈ IntermediateField.adjoin K {y} :=
  IsKrasner.krasner hx sp hy h
