-- Prove2me | solution 1 for AvramDividend.Classical.causal_convolution_contDiffOn_one_of_monotone_C1_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:25:18.530464+00:00
-- url     : https://prove2.me/submissions/cb76df37-1654-4002-92ca-62c21f28f462

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_monotone_C1_kernel_window_integrable_primitive
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_primitive_C1_of_Ici_input

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hg0 : g 0 = 0)
    (hgmono : MonotoneOn g (Ici (0 : ℝ)))
    (hgC1 : ContDiffOn ℝ 1 g (Ioi (0 : ℝ))) :
    ContDiffOn ℝ 1
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        f s * g (x - s) ∂volume) (Ioi (0 : ℝ)) := by
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  let R : ℝ := x + 1
  have hR : 0 < R := by dsimp [R]; linarith
  obtain ⟨k, hk, hwindow⟩ :=
    causal_monotone_C1_kernel_window_integrable_primitive
      g hg0 hg hgmono hgC1 R hR
  let G : ℝ → ℝ := fun y => ∫ t in Ioc (0 : ℝ) y, k t ∂volume
  have hC1 : ContDiffOn ℝ 1
      (fun y : ℝ => ∫ s in Ioc (0 : ℝ) y, f s * G (y - s) ∂volume)
      (Ioi (0 : ℝ)) := by
    exact causal_l1_kernel_primitive_C1_of_Ici_input
      f k G hf hk (by intro y hy; rfl)
  have hEq : ∀ y ∈ Ioo (0 : ℝ) R,
      (∫ s in Ioc (0 : ℝ) y, f s * g (y - s) ∂volume) =
      (∫ s in Ioc (0 : ℝ) y, f s * G (y - s) ∂volume) := by
    intro y hy
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have hys : 0 ≤ y - s := sub_nonneg.mpr hs.2
    have heq : G (y - s) = g (y - s) := by
      rcases eq_or_lt_of_le hys with hzero | hpos
      · rw [← hzero]
        simp [G, hg0]
      · exact hwindow (y - s) hpos (by
          have hspos : 0 < s := hs.1
          have hyR : y < R := hy.2
          linarith)
    change f s * g (y - s) = f s * G (y - s)
    rw [heq]
  have hCwin : ContDiffOn ℝ 1
      (fun y : ℝ => ∫ s in Ioc (0 : ℝ) y, f s * g (y - s) ∂volume)
      (Ioo (0 : ℝ) R) := by
    apply (hC1.mono (by intro y hy; exact hy.1)).congr
    intro y hy
    exact hEq y hy
  refine ⟨Ioo (0 : ℝ) R, isOpen_Ioo, ?_, ?_⟩
  · exact ⟨hx, by dsimp [R]; linarith⟩
  · exact hCwin.mono (by intro y hy; exact hy.2)
