-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.L_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:21.811458+00:00
-- url     : https://prove2.me/submissions/4afa0170-afbf-48cc-bba3-50e5f4941c08

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
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution (a : K) (i : Fin 2) : (L i) (MvPowerSeries.C a : MvPowerSeries (Fin 2) K) = 0 := by
  simp [MvPowerSeries.coeff_C]
end Formalism.ELL.WeierstrassChordSeries
