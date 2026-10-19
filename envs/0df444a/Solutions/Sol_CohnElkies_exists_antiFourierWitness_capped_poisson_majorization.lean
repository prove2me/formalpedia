-- Prove2me | solution 1 for CohnElkies.exists_antiFourierWitness_capped_poisson_majorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/09836df6-2260-4c16-bdd2-a46399c582cf

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_exists_antiFourierWitness_eventually_capped_bottom_majorant
import Theorems.Thm_CohnElkies_lowerStripCappedGammaHarmonic_continuousOn
import Theorems.Thm_CohnElkies_antiFourierWitness_capped_poisson_majorization_of_real_extension

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (w : AntiFourierWitness d R) :
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
                      (s - ((d : ℝ) / 2) * T)) := by
  obtain ⟨D₀, hbottom⟩ :=
    exists_antiFourierWitness_eventually_capped_bottom_majorant
      hd hR w
  refine ⟨D₀, ?_⟩
  intro D hD σ hbelow habove s
  apply antiFourierWitness_capped_poisson_majorization_of_real_extension
    hd w D (lowerStripCappedGammaHarmonic d R D)
    (lowerStripCappedGammaHarmonic_continuousOn hd R D)
  · intro z hz
    have hza : z.im ≠ -((d : ℝ) / 2) :=
      ne_of_gt hz.1
    have hzb : z.im ≠ (d : ℝ) / 2 :=
      ne_of_lt hz.2
    simp [lowerStripCappedGammaHarmonic,
      horizontalStripRealTraceExtension, hza, hzb]
  · intro z hz
    simp [lowerStripCappedGammaHarmonic,
      horizontalStripRealTraceExtension, hz]
  · intro z hz
    have hℓ : 0 < (d : ℝ) / 2 :=
      half_pos (Nat.cast_pos.mpr hd)
    have hne : (d : ℝ) / 2 ≠ -((d : ℝ) / 2) := by
      linarith
    simp [lowerStripCappedGammaHarmonic,
      horizontalStripRealTraceExtension, hz, hne]
  · exact hbottom D hD
  · exact hbelow
  · exact habove
end CohnElkies
