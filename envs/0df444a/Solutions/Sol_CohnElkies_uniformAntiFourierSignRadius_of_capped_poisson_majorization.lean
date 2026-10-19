-- Prove2me | solution 1 for CohnElkies.uniformAntiFourierSignRadius_of_capped_poisson_majorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/2159b054-0976-4d4d-b715-7549ceaa3187

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_uniformAntiFourierSignRadius_of_poisson_majorization
import Theorems.Thm_CohnElkies_antiFourierWitness_norm_le_poisson_of_eventually_capped_radius

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    (hcap :
      ∀ {d : ℕ} (hd : 0 < d) {R : ℝ} (_hR : 0 < R)
        (w : AntiFourierWitness d R),
        ∃ D₀ : ℝ,
          ∀ D : ℝ, D₀ ≤ D →
            ∀ {σ : ℝ}, -1 < σ → σ < 1 →
              ∀ s : ℝ,
                ‖normalizedRadialMellinStrip hd w.function R
                  ((s : ℂ) + Complex.I *
                    (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖ ≤
                  Real.exp
                    (∫ T : ℝ,
                      stripPoissonKernel σ T *
                        lowerGammaBoundaryCapped
                          ((d : ℝ) / 2) R D
                          (s - ((d : ℝ) / 2) * T))) :
    UniformAntiFourierSignRadius := by
  apply uniformAntiFourierSignRadius_of_poisson_majorization
  intro d hd R hR w σ hσbelow hσabove s
  obtain ⟨D₀, hD⟩ := hcap hd hR w
  apply antiFourierWitness_norm_le_poisson_of_eventually_capped_radius
    hd w hσbelow hσabove s
  have hevent : ∀ᶠ n : ℕ in atTop, D₀ ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (Ici_mem_atTop D₀)
  filter_upwards [hevent] with n hn
  exact hD (n : ℝ) hn hσbelow hσabove s
end CohnElkies
