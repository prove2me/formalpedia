-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_turn16_first_order_exp_comparison_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:56:04.446211+00:00
-- url     : https://prove2.me/submissions/4a7a7da0-392b-43d4-8f6e-99ba23987305

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology

noncomputable section

theorem solution
    (f : ℝ → ℝ) (r a : ℝ)
    (hCont : ContinuousOn f (Ici a))
    (hDiff : DifferentiableOn ℝ f (Ioi a))
    (hDeriv : ∀ x : ℝ, a < x → deriv f x ≤ r * f x) :
    ∀ x : ℝ, a ≤ x → f x ≤ f a * Real.exp (r * (x - a)) := by
  intro x hx
  let g : ℝ → ℝ := fun t => Real.exp (-r * t) * f t
  have hECont : Continuous (fun t : ℝ => Real.exp (-r * t)) := by fun_prop
  have hGCont : ContinuousOn g (Ici a) := by
    exact hECont.continuousOn.mul hCont
  have hGDer : ∀ t : ℝ, a < t →
      HasDerivAt g ((-r) * Real.exp (-r * t) * f t +
        Real.exp (-r * t) * deriv f t) t := by
    intro t ht
    have hF : HasDerivAt f (deriv f t) t :=
      (hDiff.differentiableAt (isOpen_Ioi.mem_nhds ht)).hasDerivAt
    have hLinear : HasDerivAt (fun s : ℝ => -r * s) (-r) t := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (-r)
    have hExp : HasDerivAt (fun s : ℝ => Real.exp (-r * s))
        ((-r) * Real.exp (-r * t)) t := by
      simpa only [Function.comp_def, mul_comm] using
        (Real.hasDerivAt_exp (-r * t)).comp t hLinear
    exact hExp.mul hF
  have hGDiff : DifferentiableOn ℝ g (interior (Ici a)) := by
    rw [interior_Ici]
    intro t ht
    exact (hGDer t ht).differentiableAt.differentiableWithinAt
  have hGNonpos : ∀ t ∈ interior (Ici a), deriv g t ≤ 0 := by
    intro t ht
    have hat : a < t := by simpa only [interior_Ici, mem_Ioi] using ht
    have hDer := (hGDer t hat).deriv
    calc
      deriv g t =
        (-r) * Real.exp (-r * t) * f t +
          Real.exp (-r * t) * deriv f t := hDer
      _ = Real.exp (-r * t) * (deriv f t - r * f t) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (Real.exp_pos _)) (sub_nonpos.mpr (hDeriv t hat))
  have hAnti : AntitoneOn g (Ici a) :=
    antitoneOn_of_deriv_nonpos (convex_Ici a) hGCont hGDiff hGNonpos
  have hIneq : g x ≤ g a :=
    hAnti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  have hExp0 : Real.exp (r * x) * Real.exp (-r * x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hExpShift : Real.exp (r * x) * Real.exp (-r * a) =
      Real.exp (r * (x - a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hScale := mul_le_mul_of_nonneg_left hIneq
    (le_of_lt (Real.exp_pos (r * x)))
  dsimp [g] at hScale
  calc
    f x = (Real.exp (r * x) * Real.exp (-r * x)) * f x := by
      rw [hExp0]
      ring
    _ = Real.exp (r * x) * (Real.exp (-r * x) * f x) := by ring
    _ ≤ Real.exp (r * x) * (Real.exp (-r * a) * f a) := hScale
    _ = (Real.exp (r * x) * Real.exp (-r * a)) * f a := by ring
    _ = Real.exp (r * (x - a)) * f a := by rw [hExpShift]
    _ = f a * Real.exp (r * (x - a)) := by ring
