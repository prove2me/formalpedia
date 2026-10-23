-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_truncated_convolution_time_primitive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:48:49.685983+00:00
-- url     : https://prove2.me/submissions/c7ae18fc-86b8-4e57-8057-dc5c9ad967bb

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_causal_l1_truncated_convolution_fubini_swap
import Theorems.Thm_AvramDividend_Classical_causal_truncated_shift_integral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Fubini reduces the time-integrated convolution to the kernel times input primitive. -/
theorem solution
    (K g : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    (∫ t in Ioc (0 : ℝ) x,
      ∫ u : ℝ,
        ((Ioi (0 : ℝ)).indicator K) u *
        ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume ∂volume) =
    (∫ u in Ioc (0 : ℝ) x,
      K u * (∫ s in Ioc (0 : ℝ) (x - u), g s ∂volume) ∂volume) := by
  let G : ℝ → ℝ := fun v =>
    ∫ s in Ioc (0 : ℝ) v, g s ∂volume
  have heval (u : ℝ) :
      (∫ t in Ioc (0 : ℝ) x,
        ((Ioi (0 : ℝ)).indicator K) u *
        ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume) =
      ((Ioc (0 : ℝ) x).indicator (fun v => K v * G (x - v))) u := by
    by_cases hu : u ∈ Ioc (0 : ℝ) x
    · have hup : u ∈ Ioi (0 : ℝ) := hu.1
      simpa only [Set.indicator_of_mem hu, Set.indicator_of_mem hup,
        integral_const_mul, G] using
        congrArg (fun a : ℝ => K u * a)
          (AvramDividend.Classical.causal_truncated_shift_integral
            g u x (le_of_lt hu.1) hu.2)
    · by_cases hp : 0 < u
      · have hToo : x < u := by
          have hnot : ¬ u ≤ x := by
            intro hux
            exact hu ⟨hp, hux⟩
          exact lt_of_not_ge hnot
        have hzero :
            (∫ t in Ioc (0 : ℝ) x,
              ((Ioi (0 : ℝ)).indicator K) u *
              ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume) = 0 := by
          calc
            _ = ∫ t in Ioc (0 : ℝ) x, (0 : ℝ) ∂volume := by
              apply integral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
              have hnot : t - u ∉ Ioc (0 : ℝ) x := by
                intro hs
                linarith [ht.2, hs.1, hToo]
              simp only [Set.indicator_of_notMem hnot, mul_zero]
            _ = 0 := by simp
        simpa only [Set.indicator_of_notMem hu] using hzero
      · have hup : u ∉ Ioi (0 : ℝ) := hp
        simp only [Set.indicator_of_notMem hu,
          Set.indicator_of_notMem hup, zero_mul, integral_zero]
  calc
    (∫ t in Ioc (0 : ℝ) x,
      ∫ u : ℝ,
        ((Ioi (0 : ℝ)).indicator K) u *
        ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume ∂volume) =
      (∫ u : ℝ,
        ∫ t in Ioc (0 : ℝ) x,
          ((Ioi (0 : ℝ)).indicator K) u *
          ((Ioc (0 : ℝ) x).indicator g) (t - u) ∂volume ∂volume) :=
        AvramDividend.Classical.causal_l1_truncated_convolution_fubini_swap
          K g hK hg x hx
    _ = ∫ u : ℝ,
        ((Ioc (0 : ℝ) x).indicator (fun v => K v * G (x - v))) u ∂volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall heval
    _ = ∫ u in Ioc (0 : ℝ) x, K u * G (x - u) ∂volume :=
      MeasureTheory.integral_indicator measurableSet_Ioc
    _ = ∫ u in Ioc (0 : ℝ) x,
      K u * (∫ s in Ioc (0 : ℝ) (x - u), g s ∂volume) ∂volume := rfl
