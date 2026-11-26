-- Prove2me | solution 1 for Eden.planarDerivativeY_on_radialFrame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:20.661604+00:00
-- url     : https://prove2.me/submissions/77a6a19e-6b56-4379-b3eb-26f04c543348

import Definitions.Def_Eden_CartesianDerivative
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_OrthogonalFrames
import Definitions.Def_Eden_DerivativeFrames
import Theorems.Thm_Eden_planarAmplitude_parameter_identity


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (a b r u v : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    planarDerivativeY Ω t (r * a) (r * b) (a * u - b * v) (b * u + a * v) =
      (a * (radialAmplitude t (r ^ 2) * u) - b * (planarAmplitude t (r ^ 2) * v)) *
          Real.sin (Ω * t) +
        (b * (radialAmplitude t (r ^ 2) * u) + a * (planarAmplitude t (r ^ 2) * v)) *
          Real.cos (Ω * t) := by
  have hs : (r * a) ^ 2 + (r * b) ^ 2 = r ^ 2 := by
    nlinarith [congrArg (fun k : ℝ => r ^ 2 * k) hab]
  have hi : r * a * (a * u - b * v) + r * b * (b * u + a * v) = r * u := by
    nlinarith [congrArg (fun k : ℝ => r * u * k) hab]
  rw [planarDerivativeY, hs, hi, ← planarAmplitude_parameter_identity ht (sq_nonneg r)]
  ring
end Eden
