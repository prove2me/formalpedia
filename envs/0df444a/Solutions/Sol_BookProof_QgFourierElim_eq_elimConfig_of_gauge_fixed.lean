-- Prove2me | solution 1 for BookProof.QgFourierElim.eq_elimConfig_of_gauge_fixed
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-01T18:43:32.424196+00:00
-- url     : https://prove2.me/submissions/19c14f6d-2394-47b7-970d-96e297ad09fa

-- Generated from ChapterQgFourierElimination.lean — solution of BookProof.QgFourierElim.eq_elimConfig_of_gauge_fixed
import Mathlib
import Definitions.Def_ChapterQgFourierElimination
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgVielbeinModeInstance
import Definitions.Def_ChapterQgContinuumModeInstance
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterQgFourierElimForms
open BookProof.QgFourierElim




open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgVielbeinModeInstance BookProof.QgContinuumModeInstance
open BookProof.FarisLavine BookProof.QgOuterFockCoreFL

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (k : Mom) (w : Comp → ℂ)
    (h : ∀ mu nu i, formValue k (dGaugeF mu nu i) w = 0) :
    w = elimConfig k (fun p => w (eIdx p.1 p.2)) := by

  funext c
  match c with
  | Sum.inl (nu, i) => rfl
  | Sum.inr (mu, nu, i) =>
      have h1 := h mu nu i
      rw [formValue_dGauge] at h1
      change w (dIdx mu nu i) = Complex.I * ((k mu : ℤ) : ℂ) * w (eIdx nu i)
      linear_combination h1
