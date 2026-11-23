-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsParam.ev_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:51.97392+00:00
-- url     : https://prove2.me/submissions/f7d1c29e-b50d-406a-96f8-5a4a8d226a5b

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
theorem _root_.solution (t : K) : Ev (X : PowerSeries K) t t := by
  have h : ∀ n, coeff n (X : PowerSeries K) * t ^ n = if n = 1 then t else 0 := by
    intro n; rw [coeff_X]; split_ifs with hn <;> simp [hn]
  refine ⟨?_, ?_⟩
  · have e : (fun n => ‖coeff n (X : PowerSeries K) * t ^ n‖) = fun n => if n = 1 then ‖t‖ else 0 := by
      funext n; rw [h]; split_ifs <;> simp
    unfold AbsSum; rw [e]
    exact summable_of_ne_finset_zero (s := {1}) (fun n hn => by simp at hn; simp [hn])
  · unfold evalPS
    rw [tsum_eq_single 1 (fun n hn => by rw [h, if_neg hn])]
    simp
end Formalism.ELL.FormalGroupPointsParam
