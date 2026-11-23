-- Prove2me | solution 1 for Formalism.ELL.WeierstrassPointSeriesTail.wTail_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:07.981915+00:00
-- url     : https://prove2.me/submissions/037735ae-b626-4271-9bd3-6f5531ca966a

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint

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
open Formalism.ELL.WeierstrassPointSeriesTail
namespace Formalism.ELL.WeierstrassPointSeriesTail
theorem _root_.solution {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R)
    (k : ℕ) (hk : 1 ≤ k) (h : (X : PowerSeries R) ^ k ∣ w) :
    (X : PowerSeries R) ^ (k + 1) ∣ wTail W w := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨u, rfl⟩ := h
  refine ⟨C W.a₁ * u + C W.a₂ * X * u + C W.a₃ * X ^ j * u ^ 2 + C W.a₄ * X ^ (j + 1) * u ^ 2 +
    C W.a₆ * X ^ (2 * j + 1) * u ^ 3, ?_⟩
  unfold wTail
  ring
end Formalism.ELL.WeierstrassPointSeriesTail
