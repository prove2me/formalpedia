-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b20_original_finite_horizon_physical_U_left_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:17:48.824034+00:00
-- url     : https://prove2.me/submissions/c8cceb2b-c8d7-4d35-aa60-547c3ab732fb

import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys126_original_finite_horizon_zero_source_prepayment_leftLim
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift) :
    ContinuousWithinAt
      (fun r : ℝ≥0 => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) r)
      (Ioc 0 t) t := by
  let f : ℝ≥0 → ℝ := fun r =>
    x + (r : ℝ) * X.drift - Function.leftLim (fun s : ℝ≥0 => D s ω) r
  have hmono : Monotone (fun r : ℝ≥0 => D r ω) := hD.1.1.2.1 ω
  have hDleft : ContinuousWithinAt
      (Function.leftLim (fun s : ℝ≥0 => D s ω)) (Iic t) t :=
    continuousWithinAt_leftLim_Iic (hmono.tendsto_leftLim t)
  have hlin : ContinuousAt (fun r : ℝ≥0 => x + (r : ℝ) * X.drift) t := by
    fun_prop
  have hleft : ContinuousWithinAt f (Ioc 0 t) t :=
    (hlin.continuousWithinAt.sub hDleft).mono (fun _ hr => hr.2)
  have heq (r : ℝ≥0) (hrpos : 0 < r) (hrS : r ≤ S) :
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) r = f r := by
    exact avram_bvb_phys126_original_finite_horizon_zero_source_prepayment_leftLim
      X x C D hD ω S r hrS
      (nhdsLT_neBot_of_exists_lt ⟨0, hrpos⟩) hsource
  apply hleft.congr
  · intro r hr
    exact heq r hr.1 (hr.2.trans ht)
  · exact heq t htpos ht
