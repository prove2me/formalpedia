-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_kernel_triangle_fubini_two_local_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:34:28.74518+00:00
-- url     : https://prove2.me/submissions/1c3a5aa6-39b2-464c-992d-ee6766a8428c

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_triangle_fubini_two_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Local L1 regularity suffices for finite-horizon causal triangle Fubini. -/
theorem solution
    (K g : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hK : IntegrableOn K (Ioc (0 : ℝ) x) volume)
    (hg : IntegrableOn g (Ioc (0 : ℝ) x) volume) :
    (∫ t in Ioc (0 : ℝ) x,
      (∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume) ∂volume) =
    (∫ s in Ioc (0 : ℝ) x,
      K (x - s) * (∫ t in Ioc (0 : ℝ) s, g t ∂volume) ∂volume) := by
  let Ktr : ℝ → ℝ := (Iic x).indicator K
  have hIndicator :
      (Ioi (0 : ℝ)).indicator Ktr =
        (Ioc (0 : ℝ) x).indicator K := by
    funext s
    by_cases h0 : 0 < s
    · by_cases hsx : s ≤ x
      · have hIoi : s ∈ Ioi (0 : ℝ) := h0
        have hIic : s ∈ Iic x := hsx
        have hIoc : s ∈ Ioc (0 : ℝ) x := ⟨h0, hsx⟩
        simp [Ktr, Set.indicator_of_mem hIoi,
          Set.indicator_of_mem hIic, Set.indicator_of_mem hIoc]
      · have hIoi : s ∈ Ioi (0 : ℝ) := h0
        have hIic : s ∉ Iic x := hsx
        have hIoc : s ∉ Ioc (0 : ℝ) x := by
          intro hs
          exact hsx hs.2
        simp [Ktr, Set.indicator_of_mem hIoi,
          Set.indicator_of_notMem hIic, Set.indicator_of_notMem hIoc]
    · have hIoi : s ∉ Ioi (0 : ℝ) := h0
      have hIoc : s ∉ Ioc (0 : ℝ) x := by
        intro hs
        exact h0 hs.1
      simp [Ktr, Set.indicator_of_notMem hIoi,
        Set.indicator_of_notMem hIoc]
  have hKtrGlobal :
      Integrable ((Ioi (0 : ℝ)).indicator Ktr) volume := by
    rw [hIndicator]
    exact (integrable_indicator_iff measurableSet_Ioc).2 hK
  have hKtr : IntegrableOn Ktr (Ioi (0 : ℝ)) volume :=
    (integrable_indicator_iff measurableSet_Ioi).1 hKtrGlobal
  have hTriangle := causal_l1_kernel_triangle_fubini_two_L1
    Ktr g x hx hKtr hg
  calc
    (∫ t in Ioc (0 : ℝ) x,
      (∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume) ∂volume) =
      (∫ t in Ioc (0 : ℝ) x,
        (∫ s in Ioc (0 : ℝ) t, Ktr (t - s) * g s ∂volume) ∂volume) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          have hle : t - s ≤ x := by linarith [ht.2, hs.1]
          simp [Ktr, Set.indicator_of_mem (show t - s ∈ Iic x from hle)]
    _ = ∫ s in Ioc (0 : ℝ) x,
        Ktr (x - s) * (∫ t in Ioc (0 : ℝ) s, g t ∂volume) ∂volume :=
      hTriangle
    _ = ∫ s in Ioc (0 : ℝ) x,
        K (x - s) * (∫ t in Ioc (0 : ℝ) s, g t ∂volume) ∂volume := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          have hle : x - s ≤ x := by linarith [hs.1]
          simp [Ktr, Set.indicator_of_mem (show x - s ∈ Iic x from hle)]

