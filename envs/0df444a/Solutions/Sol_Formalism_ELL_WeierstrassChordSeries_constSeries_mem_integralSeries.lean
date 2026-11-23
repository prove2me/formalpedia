-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.constSeries_mem_integralSeries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:31.282992+00:00
-- url     : https://prove2.me/submissions/108b3019-bb87-475f-b627-11d84670b31e

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_mem_T

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
theorem _root_.solution {a : K} (ha : a ∈ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)) : ca a ∈ T W := by
  rw [mem_T]
  intro e
  first
    | rw [MvPowerSeries.coeff_C]
    | rw [ca, MvPowerSeries.coeff_C]
  split_ifs
  · exact Algebra.subset_adjoin ha
  · exact zero_mem _
end Formalism.ELL.WeierstrassChordSeries
