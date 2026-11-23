-- Prove2me | solution 1 for Formalism.ELL.WeierstrassSeriesLimit.X_dvd_wMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:07.99959+00:00
-- url     : https://prove2.me/submissions/195b01aa-c2f8-4b92-817c-102b3ab23551

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassSeriesLimit
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
namespace Formalism.ELL.WeierstrassSeriesLimit
theorem _root_.solution {a : PowerSeries R} (ha : X ∣ a) : X ∣ T W a := by
  obtain ⟨a', rfl⟩ := ha
  refine ⟨X ^ 2 + C W.a₁ * X * a' + C W.a₂ * X ^ 2 * a' + C W.a₃ * X * a' ^ 2
    + C W.a₄ * X ^ 2 * a' ^ 2 + C W.a₆ * X ^ 2 * a' ^ 3, ?_⟩
  simp only [T]
  ring
end Formalism.ELL.WeierstrassSeriesLimit
