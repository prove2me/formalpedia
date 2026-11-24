-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.ptEntry_app_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:05.05058+00:00
-- url     : https://prove2.me/submissions/4b3f2568-70c0-44d8-8f29-9eb80e4aa79a

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants
open scoped Matrix
namespace Formalism.FourierDecayAlt.P.PBD
theorem _root_.solution (c : ℂ) : ∀ (H : C.LPt), D.ptEntry (H ++ [(1, c)]) (D.ptSize H) (D.ptSize H) = c
  | [] => by simp [D.ptSize, D.ptEntry]
  | (s, t) :: rest => by
    simp only [List.cons_append, D.ptEntry, D.ptSize, List.map_cons, List.sum_cons]
    have h0 : 0 ≤ (rest.map Prod.fst).sum := Nat.zero_le _
    by_cases hs : s = 0
    · subst hs
      simp only [lt_self_iff_false, false_and, if_false, zero_le, and_self, if_true, zero_add, Nat.sub_zero]
      have := solution c rest
      simpa [D.ptSize] using this
    · rw [if_neg (by omega), if_pos (by omega)]
      have := solution c rest
      simp only [D.ptSize] at this
      rwa [show s + (rest.map Prod.fst).sum - s = (rest.map Prod.fst).sum by omega]
end Formalism.FourierDecayAlt.P.PBD
