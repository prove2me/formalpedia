-- Prove2me | solution 1 for AvramDividend.Classical.tilted_scale_contDiffOn_of_integrated_tail_representation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T04:23:15.610196+00:00
-- url     : https://prove2.me/submissions/cb58ec04-4da0-4990-ac1b-655fe02bbdcd

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    (W : ℝ → ℝ) (φ : ℝ) (μ : Measure ℝ)
    (hcont : ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi 0))
    (hexp : ∀ a b : ℝ, 0 < a → a ≤ b →
      W b = W a * Real.exp (∫ t in a..b, φ + μ.real (Ici t)))
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by
  set g : ℝ → ℝ := fun t => μ.real (Ici t) with hg
  have hII : ∀ x : ℝ, 0 < x → IntervalIntegrable g volume 1 x := by
    intro x hx
    apply ContinuousOn.intervalIntegrable
    apply hcont.mono
    intro t ht
    rw [Set.mem_uIcc] at ht
    simp only [Set.mem_Ioi]
    rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  set F : ℝ → ℝ := fun x => ∫ t in (1:ℝ)..x, g t with hF
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt F (g x) x := by
    intro x hx
    apply intervalIntegral.integral_hasDerivAt_right (hII x hx)
    · exact hcont.stronglyMeasurableAtFilter isOpen_Ioi x hx
    · exact hcont.continuousAt (isOpen_Ioi.mem_nhds hx)
  have hsplit : ∀ x : ℝ, 0 < x →
      (∫ t in (1:ℝ)..x, φ + g t) = φ * (x - 1) + F x := by
    intro x hx
    rw [intervalIntegral.integral_add intervalIntegrable_const (hII x hx)]
    simp [hF]; ring
  have hW : ∀ x : ℝ, 0 < x → W x = W 1 * Real.exp (φ * (x - 1) + F x) := by
    intro x hx
    rcases le_total 1 x with h | h
    · rw [hexp 1 x one_pos h, hsplit x hx]
    · have := hexp x 1 hx h
      have hs : (∫ t in x..(1:ℝ), φ + g t) = -(φ * (x - 1) + F x) := by
        rw [intervalIntegral.integral_symm, hsplit x hx]
      rw [hs] at this
      rw [this, mul_assoc, ← Real.exp_add]; simp
  have hVeq : EqOn V (fun x => (W 1 * Real.exp (-φ)) * Real.exp (F x)) (Ioi 0) := by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    rw [hV x hx, hW x hx]
    have : Real.exp (-(φ * x)) * Real.exp (φ * (x - 1) + F x)
        = Real.exp (-φ) * Real.exp (F x) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc Real.exp (-(φ * x)) * (W 1 * Real.exp (φ * (x - 1) + F x))
        = W 1 * (Real.exp (-(φ * x)) * Real.exp (φ * (x - 1) + F x)) := by ring
      _ = _ := by rw [this]; ring
  have hFc : ContDiffOn ℝ 1 F (Ioi 0) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    refine hcont.congr ?_
    intro x hx
    exact (hderiv x hx).deriv
  refine ContDiffOn.congr ?_ hVeq
  exact contDiffOn_const.mul (Real.contDiff_exp.comp_contDiffOn hFc)
