-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_martingale_increment_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:00:56.440591+00:00
-- url     : https://prove2.me/submissions/dcdf4839-cc86-4ed9-932f-732563969fec

import Mathlib.Probability.Martingale.Basic
open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
noncomputable section

/-
Adapted from dufeteller/lean-lsv, LSV/MartingaleQuadraticIncrement.lean,
martingale_increment_condExp_zero, commit a5f604de2e1ae431de4cbecde23e5694a12ba719.
Upstream CC BY 4.0, attribution to original source authors.
-/

theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω] [Preorder ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ι (inferInstance : MeasurableSpace Ω))
    (M : ι → Ω → ℝ) (hM : Martingale M ℱ μ) (s t : ι) (hst : s ≤ t) :
    condExp (ℱ s) μ (fun z => M t z - M s z) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
  have he := condExp_sub (hM.integrable t) (hM.integrable s) (m := ℱ s)
  refine he.trans ?_
  filter_upwards [hM.condExp_ae_eq hst, hM.condExp_ae_eq (le_refl s)] with z ht hs
  change condExp (ℱ s) μ (M t) z - condExp (ℱ s) μ (M s) z = 0
  rw [ht, hs, sub_self]

