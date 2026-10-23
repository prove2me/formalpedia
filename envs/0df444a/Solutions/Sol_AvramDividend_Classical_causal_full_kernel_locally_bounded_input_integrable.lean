-- Prove2me | solution 1 for AvramDividend.Classical.causal_full_kernel_locally_bounded_input_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:44:54.449764+00:00
-- url     : https://prove2.me/submissions/de2a84f6-d85c-4d01-a207-4e90a8ed9f8b

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_locally_bounded_input_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K V : ℝ → ℝ) (β : ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C)
    (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun s : ℝ => (β + K (x - s)) * V s)
      (Ioc (0 : ℝ) x) volume := by
  have hKpart :=
    causal_l1_kernel_locally_bounded_input_integrable K V hK hVc hVb x hx
  have hVcont : ContinuousOn V (Ioc (0 : ℝ) x) :=
    hVc.mono (by intro s hs; exact hs.1)
  have hVmeas : AEStronglyMeasurable V
      (volume.restrict (Ioc (0 : ℝ) x)) :=
    hVcont.aestronglyMeasurable measurableSet_Ioc
  obtain ⟨C, hC⟩ := hVb x hx
  have hVbound : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) x),
      ‖V s‖ ≤ |C| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact le_trans (by simpa only [Real.norm_eq_abs] using hC s hs)
      (le_abs_self C)
  have hβconst : IntegrableOn (fun _ : ℝ => β)
      (Ioc (0 : ℝ) x) volume :=
    integrableOn_const (hs := (measure_Ioc_lt_top : volume (Ioc (0 : ℝ) x) < ⊤).ne)
  have hβpart : IntegrableOn (fun s : ℝ => β * V s)
      (Ioc (0 : ℝ) x) volume := by
    have hb := hβconst.bdd_mul hVmeas hVbound
    change Integrable (fun s : ℝ => β * V s)
      (volume.restrict (Ioc (0 : ℝ) x))
    simpa only [mul_comm] using hb
  have hsum := hβpart.add hKpart
  have hfun :
      (fun s : ℝ => (β + K (x - s)) * V s) =
      ((fun s : ℝ => β * V s) +
        (fun s : ℝ => K (x - s) * V s)) := by
    funext s
    simp only [Pi.add_apply]
    ring
  rw [hfun]
  exact hsum
