-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.exists_antideriv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:29:49.738885+00:00
-- url     : https://prove2.me/submissions/b9f63add-c0d4-403c-89ca-a1383b68c6dc

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.exists_antideriv
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_contDiff
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_continuous
import Theorems.Thm_BookProof_WeakSecondDeriv_exists_supp
import Theorems.Thm_BookProof_WeakSecondDeriv_eq_zero_out
import Theorems.Thm_BookProof_WeakSecondDeriv_integral_eq_intervalIntegral
open BookProof.WeakSecondDeriv




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {g : ℝ → ℝ} (h : IsTestFun g) (h0 : ∫ x, g x = 0) :
    ∃ G : ℝ → ℝ, IsTestFun G ∧ deriv G = g := by

  obtain ⟨R, hR, hsupp⟩ := exists_supp h
  set G : ℝ → ℝ := fun x => ∫ t in (-R - 1)..x, g t with hG
  have hderiv : ∀ x, HasDerivAt G (g x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (h.continuous.intervalIntegrable _ _)
      (h.continuous.stronglyMeasurableAtFilter _ _) h.continuous.continuousAt
  have hdG : deriv G = g := funext fun x => (hderiv x).deriv
  refine ⟨G, ⟨?_, ?_⟩, hdG⟩
  · rw [contDiff_infty_iff_deriv]
    exact ⟨fun x => (hderiv x).differentiableAt, by rw [hdG]; exact h.contDiff⟩
  · apply HasCompactSupport.intro (isCompact_Icc (a := -R - 1) (b := R + 1))
    intro x hx
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · have hz : G x = ∫ _t in (-R - 1)..x, (0 : ℝ) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_comm, uIcc_of_le (by linarith)] at ht
        refine eq_zero_out hsupp ?_
        simp only [mem_Icc, not_and_or, not_le]
        exact Or.inl (by linarith [ht.2])
      simpa using hz
    · change (∫ t in (-R - 1)..x, g t) = 0
      rw [← integral_eq_intervalIntegral (R := R) hR (fun y hy => eq_zero_out hsupp hy)
        (by linarith) (by linarith)]
      exact h0
