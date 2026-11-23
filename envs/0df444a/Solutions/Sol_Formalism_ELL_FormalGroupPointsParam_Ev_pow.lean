-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsParam.Ev.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:41.899211+00:00
-- url     : https://prove2.me/submissions/a59633fb-9d1b-41ed-8ccc-bde8004feb21

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_ev_C
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul

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
open Formalism.ELL.FormalGroupPointsParam
open Formalism.G
variable {K : Type u} [NormedField K]
variable [CompleteSpace K]
namespace Formalism.ELL.FormalGroupPointsParam
namespace Ev
theorem _root_.solution {f : PowerSeries K} {t a : K} (hf : Ev f t a) (n : ℕ) : Ev (f ^ n) t (a ^ n) := by
  induction n with
  | zero =>
    have h := ev_C (1 : K) t
    rw [map_one] at h
    simpa using h
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul hf
end Ev
end Formalism.ELL.FormalGroupPointsParam
