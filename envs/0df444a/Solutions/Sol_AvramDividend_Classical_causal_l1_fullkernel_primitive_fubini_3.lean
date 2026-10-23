-- Prove2me | solution 3 for AvramDividend.Classical.causal_l1_fullkernel_primitive_fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:17:07.342212+00:00
-- url     : https://prove2.me/submissions/8d4ff44a-4756-4bc1-a1f8-a353f1207b0e

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_primitive_C1_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_continuous_input_integrable
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_outer_integrable
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_primitive_product_integrable
import Theorems.Thm_AvramDividend_Classical_causal_constant_kernel_primitive_identity
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_triangle_fubini
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

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
  let G : ℝ → ℝ := fun t => ∫ s in Ioc (0 : ℝ) t, g s ∂volume
  obtain ⟨hGdiff, hGbound⟩ := causal_primitive_C1_locally_bounded g hg
  obtain ⟨C, hC⟩ := hGbound x hx
  have hCnonneg : 0 ≤ C := le_trans (abs_nonneg (G x)) (hC x ⟨hx, le_rfl⟩)
  have hGcont : ContinuousOn G (Ioc (0 : ℝ) x) :=
    hGdiff.continuousOn.mono (by intro t ht; exact ht.1)
  have hGmeas : AEStronglyMeasurable G (volume.restrict (Ioc (0 : ℝ) x)) :=
    hGcont.aestronglyMeasurable measurableSet_Ioc
  have hGint : Integrable G (volume.restrict (Ioc (0 : ℝ) x)) := by
    have hc : Integrable (fun _ : ℝ => C) (volume.restrict (Ioc (0 : ℝ) x)) :=
      integrable_const C
    apply hc.mono hGmeas
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg hCnonneg] using hC t ht
  have hgint (t : ℝ) (ht : 0 < t) : IntegrableOn g (Ioc (0 : ℝ) t) volume := by
    have hgi : ContinuousOn g (Icc (0 : ℝ) t) :=
      hg.mono (by intro s hs; exact hs.1)
    exact hgi.integrableOn_Icc.mono_set (by intro s hs; exact ⟨le_of_lt hs.1, hs.2⟩)
  have hinner (t : ℝ) (ht : 0 < t) :
      (∫ s in Ioc (0 : ℝ) t, (β + K (t - s)) * g s ∂volume) =
        (∫ s in Ioc (0 : ℝ) t, β * g s ∂volume) +
        (∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume) := by
    have hki := causal_l1_kernel_continuous_input_integrable K g hK hg t ht
    calc
      (∫ s in Ioc (0 : ℝ) t, (β + K (t - s)) * g s ∂volume) =
          ∫ s in Ioc (0 : ℝ) t, β * g s + K (t - s) * g s ∂volume := by
            apply integral_congr_ae
            filter_upwards [] with s
            ring
      _ = (∫ s in Ioc (0 : ℝ) t, β * g s ∂volume) +
          (∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume) :=
            integral_add ((hgint t ht).const_mul β) hki
  have hβouter : IntegrableOn
      (fun t : ℝ => ∫ s in Ioc (0 : ℝ) t, β * g s ∂volume)
      (Ioc (0 : ℝ) x) volume := by
    have heq :
        (fun t : ℝ => ∫ s in Ioc (0 : ℝ) t, β * g s ∂volume) =
        (fun t : ℝ => β * G t) := by
      funext t
      simp only [G, integral_const_mul]
    rw [heq]
    exact hGint.const_mul β
  have hKouter : IntegrableOn
      (fun t : ℝ => ∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume)
      (Ioc (0 : ℝ) x) volume :=
    causal_l1_convolution_outer_integrable K g hK hg x hx
  have hβG : IntegrableOn (fun s : ℝ => β * G s) (Ioc (0 : ℝ) x) volume :=
    hGint.const_mul β
  have hKG : IntegrableOn (fun s : ℝ => K (x - s) * G s)
      (Ioc (0 : ℝ) x) volume := by
    simpa only [G] using causal_l1_kernel_primitive_product_integrable K g hK hg x hx
  have hconst := causal_constant_kernel_primitive_identity g β x
  have htri := causal_l1_kernel_triangle_fubini K g hK hg x hx
  calc
    (∫ t in Ioc (0 : ℝ) x,
      (∫ s in Ioc (0 : ℝ) t,
        (β + K (t - s)) * g s ∂volume) ∂volume) =
        ∫ t in Ioc (0 : ℝ) x,
          (∫ s in Ioc (0 : ℝ) t, β * g s ∂volume) +
          (∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume) ∂volume := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
          exact hinner t ht.1
    _ = (∫ t in Ioc (0 : ℝ) x,
          (∫ s in Ioc (0 : ℝ) t, β * g s ∂volume) ∂volume) +
        (∫ t in Ioc (0 : ℝ) x,
          (∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume) ∂volume) := by
          exact integral_add hβouter hKouter
    _ = (∫ s in Ioc (0 : ℝ) x, β * G s ∂volume) +
        (∫ s in Ioc (0 : ℝ) x, K (x - s) * G s ∂volume) := by
          simpa only [G] using congrArg₂ (· + ·) hconst htri
    _ = (∫ s in Ioc (0 : ℝ) x,
          β * G s + K (x - s) * G s ∂volume) :=
          (integral_add hβG hKG).symm
    _ = ∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * G s ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with s
          ring
    _ = (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) *
            (∫ t in Ioc (0 : ℝ) s, g t ∂volume) ∂volume) := rfl
