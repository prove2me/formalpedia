-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_quadratic_martingale_increment_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:02:43.245214+00:00
-- url     : https://prove2.me/submissions/96ab8cbf-af8d-407d-87a0-497cd6012900

import Mathlib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Theorems.Thm_AvramDividend_Classical_avram_lsv_martingale_increment_condExp_zero
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
set_option autoImplicit false
noncomputable section

/-
Adapted from dufeteller/lean-lsv, LSV/MartingaleQuadraticIncrement.lean,
martingale_quadratic_increment_condExp_zero and martingale_increment_condExp_zero,
commit a5f604de2e1ae431de4cbecde23e5694a12ba719.
Original authors credited in source repository; CC BY 4.0.
Adaptation inlines the martingale increment identity to avoid importing LSV.
-/

theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω] [Preorder ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ι (inferInstance : MeasurableSpace Ω))
    (M A : ι → Ω → ℝ) (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t z => (M t z)^2 - A t z) ℱ μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (s t : ι) (hst : s ≤ t) :
    condExp (ℱ s) μ (fun z => (M t z - M s z)^2 - (A t z - A s z))
      =ᵐ[μ] (fun _ => (0 : ℝ)) := by
  let Q := fun t z => (M t z)^2 - A t z
  let R := fun z => M t z - M s z
  have hR : MemLp R 2 μ := (hM2 t).sub (hM2 s)
  have hRi : Integrable R μ := hR.integrable (by norm_num)
  have hprod : Integrable (fun z => M s z * R z) μ := (hM2 s).integrable_mul hR
  have hp := condExp_mul_of_stronglyMeasurable_left (hM.stronglyMeasurable s) hprod hRi
  have hz := AvramDividend.Classical.avram_lsv_martingale_increment_condExp_zero
    μ ℱ M hM s t hst
  have hprod0 : condExp (ℱ s) μ (fun z => M s z * R z) =ᵐ[μ]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hp, hz] with z hp hz
    change condExp (ℱ s) μ (fun z => M s z * R z) z =
      M s z * condExp (ℱ s) μ R z at hp
    rw [hp, hz, mul_zero]
  have hQd : Integrable (fun z => Q t z - Q s z) μ :=
    (hQ.integrable t).sub (hQ.integrable s)
  have he : (fun z => (M t z - M s z)^2 - (A t z - A s z)) =
      (fun z => (Q t z - Q s z) - 2 * (M s z * R z)) := by
    funext z
    dsimp [Q, R]
    ring
  rw [he]
  have hsub := condExp_sub hQd (hprod.const_mul 2) (m := ℱ s)
  have hmul := condExp_smul (m := ℱ s) (μ := μ) (2 : ℝ)
    (fun z => M s z * R z)
  have hQ0 := AvramDividend.Classical.avram_lsv_martingale_increment_condExp_zero
    μ ℱ Q hQ s t hst
  filter_upwards [hsub, hmul, hQ0, hprod0] with z hs hm hq hp
  change condExp (ℱ s) μ (fun z => (Q t z - Q s z) -
      2 * (M s z * R z)) z =
    condExp (ℱ s) μ (fun z => Q t z - Q s z) z -
      condExp (ℱ s) μ (fun z => 2 * (M s z * R z)) z at hs
  change condExp (ℱ s) μ (fun z => 2 * (M s z * R z)) z =
    2 * condExp (ℱ s) μ (fun z => M s z * R z) z at hm
  rw [hs, hm, hq, hp]
  simp

