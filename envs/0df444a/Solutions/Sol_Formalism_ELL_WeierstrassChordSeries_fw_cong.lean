-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.fw_cong
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:57.647181+00:00
-- url     : https://prove2.me/submissions/0fb5c2a8-86ea-422b-af74-24c27387f01d

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
theorem _root_.solution {n : ℕ} {v v' : PowerSeries K} (h : X ^ n ∣ v - v') (hv : X ∣ v) (hv' : X ∣ v') :
    X ^ (n + 1) ∣ fw W v - fw W v' := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, rfl⟩ := hv
  obtain ⟨b', rfl⟩ := hv'
  refine ⟨C W.a₁ * a + C W.a₂ * X * a + C W.a₃ * a * (b + b') + C W.a₄ * X * a * (b + b')
    + C W.a₆ * X * a * (b ^ 2 + b * b' + b' ^ 2), ?_⟩
  unfold fw
  linear_combination (X * (C W.a₁ + C W.a₂ * X + C W.a₃ * (b + b') + C W.a₄ * X * (b + b')
    + C W.a₆ * X * (b ^ 2 + b * b' + b' ^ 2))) * ha
end Formalism.ELL.WeierstrassChordSeries
