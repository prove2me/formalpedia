-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.L_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:31.277672+00:00
-- url     : https://prove2.me/submissions/521f03c5-7942-4d21-af60-e7cda181f915

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
theorem _root_.solution (i j : Fin 2) : (L i) (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) = if i = j then 1 else 0 := by
  rw [MvPowerSeries.coeff_X]
  by_cases h : i = j
  · subst h
    simp
  · have h' : Finsupp.single i 1 ≠ Finsupp.single j 1 := fun e => h (Finsupp.single_left_injective one_ne_zero e)
    rw [if_neg h', if_neg h]
end Formalism.ELL.WeierstrassChordSeries
