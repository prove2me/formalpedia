-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.X_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:16.169102+00:00
-- url     : https://prove2.me/submissions/8517349b-6d49-4b37-bc7e-95e088150ab3

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
theorem _root_.solution : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ MvPowerSeries.X 1 := by
  intro h
  have := congrArg (MvPowerSeries.coeff (Finsupp.single 0 1)) h
  rw [MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_pos rfl, if_neg] at this
  · exact one_ne_zero this
  · intro h'
    exact absurd (Finsupp.single_left_injective one_ne_zero h') (by decide)
end Formalism.ELL.WeierstrassChordSeries
