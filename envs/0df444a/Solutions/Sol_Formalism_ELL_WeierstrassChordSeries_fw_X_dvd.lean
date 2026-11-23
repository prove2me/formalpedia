-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.fw_X_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:26.278809+00:00
-- url     : https://prove2.me/submissions/fbe9788c-d028-42b9-9052-483f4a24beb4

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord

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
open Formalism.ELL.WeierstrassChordSeries
variable {K : Type u} [Field K] (W : WeierstrassCurve K)
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution {v : PowerSeries K} (hv : X ∣ v) : X ∣ fw W v := by
  obtain ⟨b, rfl⟩ := hv
  exact ⟨X ^ 2 + C W.a₁ * X * b + C W.a₂ * X ^ 2 * b + C W.a₃ * X * b ^ 2 + C W.a₄ * X ^ 2 * b ^ 2
    + C W.a₆ * X ^ 2 * b ^ 3, by unfold fw; ring⟩
end Formalism.ELL.WeierstrassChordSeries
