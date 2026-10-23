-- Prove2me | solution 2 for AvramDividend.Classical.causal_l1_fullkernel_primitive_fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T20:54:04.664544+00:00
-- url     : https://prove2.me/submissions/5682cc4d-60b5-467f-aa6b-9f0190cf6e9e

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_triangle_fubini
import Theorems.Thm_AvramDividend_Classical_causal_constant_kernel_primitive_identity
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_continuous_input_integrable
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_outer_integrable
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_primitive_product_integrable
import Theorems.Thm_AvramDividend_Classical_causal_primitive_C1_locally_bounded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Separate constant and L1 kernel contributions in the causal Fubini identity. -/
theorem solution
    (K g : ℝ → ℝ) (β : ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    (∫ t in Ioc (0 : ℝ) x,
      (∫ s in Ioc (0 : ℝ) t,
        (β + K (t - s)) * g s ∂volume) ∂volume) =
    (∫ s in Ioc (0 : ℝ) x,
      (β + K (x - s)) *
        (∫ t in Ioc (0 : ℝ) s, g t ∂volume) ∂volume) := by
  let G : ℝ → ℝ := fun s => ∫ t in Ioc (0 : ℝ) s, g t ∂volume
  obtain ⟨hGc, hGb⟩ := causal_primitive_C1_locally_bounded g hg
  have hGcont : ContinuousOn G (Ioc (0 : ℝ) x) :=
    hGc.continuousOn.mono (by intro s hs; exact hs.1)
  have hGmeas : AEStronglyMeasurable G (volume.restrict (Ioc (0 : ℝ) x)) :=
    hGcont.aestronglyMeasurable measurableSet_Ioc
  obtain ⟨C, hC⟩ := hGb x hx
  have hbound : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) x), ‖G s‖ ≤ |C| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact le_trans (by simpa [G, Real.norm_eq_abs] using hC s hs) (le_abs_self C)
  have hβconst : IntegrableOn (fun _ : ℝ => β) (Ioc (0 : ℝ) x) volume :=
    integrableOn_const (hs := (measure_Ioc_lt_top : volume (Ioc (0 : ℝ) x) < ⊤).ne)
  have hβG : IntegrableOn (fun s : ℝ => β * G s) (Ioc (0 : ℝ) x) volume := by
    have h := hβconst.bdd_mul hGmeas hbound
    change Integrable (fun s : ℝ => β * G s) (volume.restrict (Ioc (0 : ℝ) x))
    simpa only [mul_comm] using h
  have hβouter : IntegrableOn
      (fun t : ℝ => ∫ s in Ioc (0 : ℝ) t, β * g s ∂volume)
      (Ioc (0 : ℝ) x) volume := by
    simpa only [integral_const_mul] using hβG
  have hKouter := causal_l1_convolution_outer_integrable K g hK hg x hx
  have hKprimitive := causal_l1_kernel_primitive_product_integrable K g hK hg x hx
  have hβinner (t : ℝ) (ht : 0 < t) :
      IntegrableOn (fun s : ℝ => β * g s) (Ioc (0 : ℝ) t) volume := by
    have hc : ContinuousOn g (Icc (0 : ℝ) t) :=
      hg.mono (by intro s hs; exact hs.1)
    exact (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).const_mul β
  have hL :
      (∫ t in Ioc (0 : ℝ) x,
        ∫ s in Ioc (0 : ℝ) t, (β + K (t - s)) * g s ∂volume) =
      (∫ t in Ioc (0 : ℝ) x,
        (∫ s in Ioc (0 : ℝ) t, β * g s ∂volume) +
        (∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume) ∂volume) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    calc
      (∫ s in Ioc (0 : ℝ) t, (β + K (t - s)) * g s ∂volume) =
        ∫ s in Ioc (0 : ℝ) t, β * g s + K (t - s) * g s ∂volume := by
          congr 1; funext s; ring
      _ = _ := integral_add (hβinner t ht.1)
        (causal_l1_kernel_continuous_input_integrable K g hK hg t ht.1)
  have hR :
      (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * G s ∂volume) =
      (∫ s in Ioc (0 : ℝ) x, β * G s ∂volume) +
      (∫ s in Ioc (0 : ℝ) x, K (x - s) * G s ∂volume) := by
    calc
      _ = ∫ s in Ioc (0 : ℝ) x, β * G s + K (x - s) * G s ∂volume := by
        congr 1; funext s; ring
      _ = _ := integral_add hβG hKprimitive
  calc
    (∫ t in Ioc (0 : ℝ) x,
      ∫ s in Ioc (0 : ℝ) t, (β + K (t - s)) * g s ∂volume) =
      (∫ t in Ioc (0 : ℝ) x,
        (∫ s in Ioc (0 : ℝ) t, β * g s ∂volume) +
        (∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume) ∂volume) := hL
    _ = (∫ t in Ioc (0 : ℝ) x, ∫ s in Ioc (0 : ℝ) t, β * g s ∂volume ∂volume) +
        (∫ t in Ioc (0 : ℝ) x, ∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume ∂volume) :=
      integral_add hβouter hKouter
    _ = (∫ s in Ioc (0 : ℝ) x, β * G s ∂volume) +
        (∫ s in Ioc (0 : ℝ) x, K (x - s) * G s ∂volume) := by
      exact congrArg₂ (· + ·)
        (causal_constant_kernel_primitive_identity g β x)
        (causal_l1_kernel_triangle_fubini K g hK hg x hx)
    _ = (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * G s ∂volume) := hR.symm
