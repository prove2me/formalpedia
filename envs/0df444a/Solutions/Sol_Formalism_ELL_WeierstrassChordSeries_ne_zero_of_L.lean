-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.ne_zero_of_L
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:03.369354+00:00
-- url     : https://prove2.me/submissions/55b88ba0-4483-479a-884e-a2c707fa1e50

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
variable {K : Type u} [Field K]
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable (W : WeierstrassCurve K) (w : PowerSeries K)
variable {W w}
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution {φ : MvPowerSeries (Fin 2) K} {i : Fin 2} (h : (L i) φ ≠ 0) : φ ≠ 0 := by
  rintro rfl
  exact h (map_zero _)
end Formalism.ELL.WeierstrassChordSeries
