-- Prove2me | solution 1 for Formalism.ELL.WeierstrassCoordinateSubstitution.exists_unit_factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:28.227806+00:00
-- url     : https://prove2.me/submissions/e8274a9e-3dc4-49fb-98cb-53f6ab998408

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor

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
open Formalism.ELL.WeierstrassCoordinateSubstitution
variable {K : Type u} [Field K]
namespace Formalism.ELL.WeierstrassCoordinateSubstitution
theorem _root_.solution {W : WeierstrassCurve K} {w : PowerSeries K} (hw : WFixed W w) :
    ∃ u : PowerSeries K, w = X ^ 3 * u ∧ constantCoeff u = 1 := by
  obtain ⟨h0, heq⟩ := hw
  have hX : (X : PowerSeries K) ≠ 0 := PowerSeries.X_ne_zero
  obtain ⟨v, rfl⟩ := PowerSeries.X_dvd_iff.mpr h0
  have hv : v = X ^ 2 + C W.a₁ * X * v + C W.a₂ * X ^ 2 * v + C W.a₃ * X * v ^ 2
      + C W.a₄ * X ^ 2 * v ^ 2 + C W.a₆ * X ^ 2 * v ^ 3 := by
    apply mul_left_cancel₀ hX
    linear_combination heq
  have hv0 : constantCoeff v = 0 := by simpa using congrArg constantCoeff hv
  obtain ⟨v₂, rfl⟩ := PowerSeries.X_dvd_iff.mpr hv0
  have hv₂ : v₂ = X + C W.a₁ * X * v₂ + C W.a₂ * X ^ 2 * v₂ + C W.a₃ * X ^ 2 * v₂ ^ 2
      + C W.a₄ * X ^ 3 * v₂ ^ 2 + C W.a₆ * X ^ 4 * v₂ ^ 3 := by
    apply mul_left_cancel₀ hX
    linear_combination hv
  have hv₂0 : constantCoeff v₂ = 0 := by simpa using congrArg constantCoeff hv₂
  obtain ⟨u, rfl⟩ := PowerSeries.X_dvd_iff.mpr hv₂0
  have hu : u = 1 + C W.a₁ * X * u + C W.a₂ * X ^ 2 * u + C W.a₃ * X ^ 3 * u ^ 2
      + C W.a₄ * X ^ 4 * u ^ 2 + C W.a₆ * X ^ 6 * u ^ 3 := by
    apply mul_left_cancel₀ hX
    linear_combination hv₂
  refine ⟨u, by ring, ?_⟩
  simpa using congrArg constantCoeff hu
end Formalism.ELL.WeierstrassCoordinateSubstitution
