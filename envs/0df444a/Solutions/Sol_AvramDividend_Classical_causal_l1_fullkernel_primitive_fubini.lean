-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_fullkernel_primitive_fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T20:52:28.162798+00:00
-- url     : https://prove2.me/submissions/a360d2c8-6413-45e6-9c17-edde72851ba2

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_primitive_C1_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_continuous_input_integrable
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_primitive_product_integrable
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_outer_integrable
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
      (∫ s in Ioc (0 : ℝ) t, (β + K (t - s)) * g s ∂volume) ∂volume) =
    (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
      (∫ t in Ioc (0 : ℝ) s, g t ∂volume) ∂volume) := by
  let G : ℝ → ℝ := fun s => ∫ t in Ioc (0 : ℝ) s, g t ∂volume
  have hGcont : ContinuousOn G (Ioc (0 : ℝ) x) :=
    (causal_primitive_C1_locally_bounded g hg).1.continuousOn.mono
      (by intro s hs; exact hs.1)
  have hGmeas : AEStronglyMeasurable G (volume.restrict (Ioc (0 : ℝ) x)) := hGcont.aestronglyMeasurable measurableSet_Ioc
  obtain ⟨C, hC⟩ := (causal_primitive_C1_locally_bounded g hg).2 x hx
  have hGbound : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) x), ‖G s‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simpa only [G, Real.norm_eq_abs] using hC s hs
  have hGint : IntegrableOn G (Ioc (0 : ℝ) x) volume :=
    IntegrableOn.of_bound (by simp [Real.volume_Ioc]) hGmeas C hGbound
  have hβint : IntegrableOn (fun s : ℝ => β * G s) (Ioc (0 : ℝ) x) volume := hGint.const_mul β
  have hKGint := causal_l1_kernel_primitive_product_integrable K g hK hg x hx
  have hKouter := causal_l1_convolution_outer_integrable K g hK hg x hx
  have hβouter : IntegrableOn (fun t : ℝ => ∫ s in Ioc (0 : ℝ) t,
      β * g s ∂volume) (Ioc (0 : ℝ) x) volume := by
    simpa only [integral_const_mul] using hβint
  have hInner (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) x) :
      (∫ s in Ioc (0 : ℝ) t, (β + K (t - s)) * g s ∂volume) =
      (∫ s in Ioc (0 : ℝ) t, β * g s ∂volume) +
      (∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume) := by
    have hgi : IntegrableOn g (Ioc (0 : ℝ) t) volume :=
      (hg.mono (by intro s hs; exact hs.1)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hKi := (causal_l1_kernel_continuous_input_integrable K g hK hg) t ht.1
    calc
      _ = ∫ s in Ioc (0 : ℝ) t, β * g s + K (t - s) * g s ∂volume := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro s hs; ring
      _ = _ := integral_add (hgi.const_mul β) hKi
  have hLsplit :
      (∫ t in Ioc (0 : ℝ) x,
        (∫ s in Ioc (0 : ℝ) t, (β + K (t - s)) * g s ∂volume) ∂volume) =
      (∫ t in Ioc (0 : ℝ) x, (∫ s in Ioc (0 : ℝ) t, β * g s ∂volume) ∂volume) +
      (∫ t in Ioc (0 : ℝ) x, (∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume) ∂volume) := by
    calc
      _ = ∫ t in Ioc (0 : ℝ) x, ((∫ s in Ioc (0 : ℝ) t,
          β * g s ∂volume) + (∫ s in Ioc (0 : ℝ) t,
          K (t - s) * g s ∂volume)) ∂volume := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht; exact hInner t ht
      _ = _ := integral_add hβouter hKouter
  have hRsplit :
      (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * G s ∂volume) =
      (∫ s in Ioc (0 : ℝ) x, β * G s ∂volume) +
      (∫ s in Ioc (0 : ℝ) x, K (x - s) * G s ∂volume) := by
    calc
      _ = ∫ s in Ioc (0 : ℝ) x, (β * G s + K (x - s) * G s) ∂volume := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro s hs; ring
      _ = _ := integral_add hβint hKGint
  calc
    _ = (∫ t in Ioc (0 : ℝ) x, (∫ s in Ioc (0 : ℝ) t, β * g s ∂volume) ∂volume) +
        (∫ t in Ioc (0 : ℝ) x, (∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume) ∂volume) := hLsplit
    _ = (∫ s in Ioc (0 : ℝ) x, β * G s ∂volume) +
        (∫ s in Ioc (0 : ℝ) x, K (x - s) * G s ∂volume) := by
      rw [causal_constant_kernel_primitive_identity g β x,
        causal_l1_kernel_triangle_fubini K g hK hg x hx]
    _ = _ := hRsplit.symm
