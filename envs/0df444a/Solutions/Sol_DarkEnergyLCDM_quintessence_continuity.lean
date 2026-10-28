-- Prove2me | solution 1 for DarkEnergyLCDM.quintessence_continuity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:24:18.318087+00:00
-- url     : https://prove2.me/submissions/5e081747-aa9a-4057-8fbb-a34fafa1a45c

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

open DarkEnergyLCDM

theorem solution (I : Set ℝ) (hI : IsOpen I) (a ϕ V : ℝ → ℝ)
    (hϕ : ContDiffOn ℝ 2 ϕ I) (hV : Differentiable ℝ V)
    (hKG : ∀ t ∈ I, deriv (deriv ϕ) t + 3 * hubble a t * deriv ϕ t + deriv V (ϕ t) = 0) :
    ∀ t ∈ I, ContinuityEq a (quintessenceDensity V ϕ) (quintessencePressure V ϕ) t := by
  intro t ht
  have hn := hI.mem_nhds ht
  have hd1 : DifferentiableAt ℝ ϕ t := (hϕ.differentiableOn (by norm_num)).differentiableAt hn
  have hd2 : DifferentiableAt ℝ (deriv ϕ) t :=
    ((hϕ.deriv_of_isOpen hI (m := 1) (by norm_num)).differentiableOn (by norm_num)).differentiableAt hn
  have hD : HasDerivAt (fun s => deriv ϕ s ^ 2 / 2 + V (ϕ s))
      ((↑2 * deriv ϕ t ^ (2 - 1) * deriv (deriv ϕ) t) / 2 + deriv V (ϕ t) * deriv ϕ t) t :=
    ((hd2.hasDerivAt.pow 2).div_const 2).add ((hV (ϕ t)).hasDerivAt.comp t hd1.hasDerivAt)
  unfold ContinuityEq
  rw [show quintessenceDensity V ϕ = fun s => deriv ϕ s ^ 2 / 2 + V (ϕ s) from rfl, hD.deriv]
  unfold quintessencePressure
  linear_combination (deriv ϕ t) * hKG t ht
