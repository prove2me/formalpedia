-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsParam.ev_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:14.886696+00:00
-- url     : https://prove2.me/submissions/17d3954a-2e5a-432e-8883-980c74955af8

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef

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
namespace Formalism.ELL.FormalGroupPointsParam
theorem _root_.solution (a t : K) : Ev (C a) t a := by
  have h : ∀ n, coeff n (C a : PowerSeries K) * t ^ n = if n = 0 then a else 0 := by
    intro n; rw [coeff_C]; split_ifs with hn <;> simp [hn]
  refine ⟨?_, ?_⟩
  · have e : (fun n => ‖coeff n (C a : PowerSeries K) * t ^ n‖) = fun n => if n = 0 then ‖a‖ else 0 := by
      funext n; rw [h]; split_ifs <;> simp
    unfold AbsSum; rw [e]
    exact summable_of_ne_finset_zero (s := {0}) (fun n hn => by simp at hn; simp [hn])
  · unfold evalPS
    rw [tsum_eq_single 0 (fun n hn => by rw [h, if_neg hn])]
    simp
end Formalism.ELL.FormalGroupPointsParam
