-- Prove2me | solution 1 for AvramDividend.Classical.causal_full_kernel_convolution_continuousOn_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:08:18.315676+00:00
-- url     : https://prove2.me/submissions/3b37ed82-6f92-412a-a813-e39eb37ebc6b

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousOn
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_continuousOn_nonnegative_of_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_continuous_input_primitive_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_locally_bounded_input_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- The drift-plus-L1 causal convolution is continuous through time zero. -/
theorem solution
    (K V : ℝ → ℝ) (β : ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ici (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C) :
    ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * V s ∂volume)
      (Ici (0 : ℝ)) := by
  let P : ℝ → ℝ := fun x => ∫ s in Ioc (0 : ℝ) x, V s ∂volume
  let C : ℝ → ℝ := fun x =>
    ∫ s in Ioc (0 : ℝ) x, K (x - s) * V s ∂volume
  have hP : ContinuousOn P (Ici (0 : ℝ)) :=
    causal_continuous_input_primitive_continuousOn_nonnegative V hVc
  have hC : ContinuousOn C (Ici (0 : ℝ)) :=
    causal_l1_convolution_continuousOn_nonnegative_of_locally_bounded
      K V hK hVc hVb
  have hPC : ContinuousOn (fun x => β * P x + C x) (Ici (0 : ℝ)) :=
    (continuousOn_const.mul hP).add hC
  apply hPC.congr
  intro x hx
  change 0 ≤ x at hx
  rcases eq_or_lt_of_le hx with rfl | hpos
  · simp [P, C]
  · have hVint : IntegrableOn V (Ioc (0 : ℝ) x) volume :=
      (hVc.mono (by intro y hy; exact hy.1)).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
    have hKint : IntegrableOn (fun s : ℝ => K (x - s) * V s)
        (Ioc (0 : ℝ) x) volume :=
      causal_l1_kernel_locally_bounded_input_integrable
        K V hK (hVc.mono Set.Ioi_subset_Ici_self) hVb x hpos
    have hSplit :
        (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * V s ∂volume) =
          β * P x + C x := by
      calc
        _ = ∫ s in Ioc (0 : ℝ) x,
              β * V s + K (x - s) * V s ∂volume := by
            apply setIntegral_congr_fun measurableSet_Ioc
            intro s hs
            ring
        _ = (∫ s in Ioc (0 : ℝ) x, β * V s ∂volume) +
            (∫ s in Ioc (0 : ℝ) x, K (x - s) * V s ∂volume) :=
              integral_add (hVint.const_mul β) hKint
        _ = β * P x + C x := by rw [integral_const_mul]
    exact hSplit
