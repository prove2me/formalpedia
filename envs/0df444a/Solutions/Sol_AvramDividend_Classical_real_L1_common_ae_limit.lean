-- Prove2me | solution 1 for AvramDividend.Classical.real_L1_common_ae_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T13:12:03.23228+00:00
-- url     : https://prove2.me/submissions/c858fbc9-627b-43fd-9b3d-1eae3127934f

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_real_L1_tendstoInMeasure
import Theorems.Thm_AvramDividend_Classical_ae_eq_of_common_tendstoInMeasure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Fn Gn : ℕ → Ω → ℝ) (F G : Ω → ℝ)
    (hFn : ∀ n, StronglyMeasurable (Fn n))
    (hGn : ∀ n, StronglyMeasurable (Gn n))
    (hF : StronglyMeasurable F) (hG : StronglyMeasurable G)
    (hIntF : ∀ n, Integrable (fun ω => Fn n ω - F ω) P)
    (hIntG : ∀ n, Integrable (fun ω => Gn n ω - G ω) P)
    (hEq : ∀ n, Fn n =ᵐ[P] Gn n)
    (hLimF : Tendsto
      (fun n : ℕ => ∫ ω, |Fn n ω - F ω| ∂P) atTop (nhds 0))
    (hLimG : Tendsto
      (fun n : ℕ => ∫ ω, |Gn n ω - G ω| ∂P) atTop (nhds 0)) :
    F =ᵐ[P] G := by
  exact ae_eq_of_common_tendstoInMeasure
    P Fn Gn F G hEq
    (real_L1_tendstoInMeasure P Fn F hFn hF hIntF hLimF)
    (real_L1_tendstoInMeasure P Gn G hGn hG hIntG hLimG)
