-- Prove2me | solution 1 for CarneiroDeSitter.early_time_implicit_solution
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:45:49.904443+00:00
-- url     : https://prove2.me/submissions/be7198e7-c87c-41bb-a4f2-4b2ef688350f

import Mathlib
import Definitions.Def_CarneiroDeSitter2006

open Filter Topology Set CarneiroDeSitter

namespace CarneiroAux6

lemma artanh_eq (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Real.artanh x = 1 / 2 * (Real.log (1 + x) - Real.log (1 - x)) := by
  rw [Real.artanh_eq_half_log ⟨hx.1.le, hx.2.le⟩, Real.log_div (by linarith [hx.1]) (by linarith [hx.2])]

lemma hasDerivAt_artanh (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x := by
  have h1 : 0 < 1 + x := by linarith [hx.1]
  have h2 : 0 < 1 - x := by linarith [hx.2]
  have e : Real.artanh =ᶠ[𝓝 x] fun y => 1 / 2 * (Real.log (1 + y) - Real.log (1 - y)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using artanh_eq y hy
  have := ((((hasDerivAt_id x).const_add 1).log h1.ne').sub
    (((hasDerivAt_id x).const_sub 1).log h2.ne')).const_mul (1 / 2)
  refine (this.congr_deriv ?_).congr_of_eventuallyEq e
  simp only [id]
  rw [show (1 : ℝ) - x ^ 2 = (1 + x) * (1 - x) by ring]
  field_simp
  ring

end CarneiroAux6

open CarneiroAux6 in
theorem solution (H : ℝ → ℝ)
    (hbounds : ∀ t, 0 < H t ∧ H t < 1)
    (hode : ∀ t, HasDerivAt H (-2 * H t ^ 2 + 2 * H t ^ 4) t) :
    ∃ t₀ : ℝ, ∀ t, 2 * (t - t₀) = 1 / H t - Real.artanh (H t) := by
  have hg : ∀ t, HasDerivAt (fun s => 1 / H s - Real.artanh (H s) - 2 * s) 0 t := by
    intro t
    obtain ⟨h0, h1⟩ := hbounds t
    have ha := (hasDerivAt_artanh (H t) ⟨by linarith, h1⟩).comp t (hode t)
    have hi := (hode t).inv h0.ne'
    have := ((hi.sub ha).sub ((hasDerivAt_id t).const_mul 2))
    simp only [one_div] at this ⊢
    refine this.congr_deriv ?_
    have h2 : 0 < 1 - H t ^ 2 := by nlinarith
    field_simp
    ring
  have hc := fun t => is_const_of_deriv_eq_zero (fun y => (hg y).differentiableAt)
    (fun y => (hg y).deriv) t 0
  refine ⟨-(1 / H 0 - Real.artanh (H 0)) / 2, fun t => ?_⟩
  have := hc t
  simp only [mul_zero, sub_zero] at this
  linarith
