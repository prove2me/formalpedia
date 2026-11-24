-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.ptEntry_app_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:38:36.540671+00:00
-- url     : https://prove2.me/submissions/c121b4e5-c9e0-4fda-809b-19e347677ac9

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
theorem _root_.solution (c : ℂ) : ∀ (H : C.LPt) (b : ℕ), b < D.ptSize H →
    D.ptEntry (H ++ [(1, c)]) (D.ptSize H) b = 0
  | [], b, hb => by simp [D.ptSize] at hb
  | (s, t) :: rest, b, hb => by
    simp only [D.ptSize, List.map_cons, List.sum_cons] at hb
    simp only [List.cons_append, D.ptEntry, D.ptSize, List.map_cons, List.sum_cons]
    by_cases h1 : s + (rest.map Prod.fst).sum < s ∧ b < s
    · omega
    · rw [if_neg h1]
      by_cases h2 : s ≤ s + (rest.map Prod.fst).sum ∧ s ≤ b
      · rw [if_pos h2]
        have := solution c rest (b - s) (by simp only [D.ptSize]; omega)
        simp only [D.ptSize] at this
        rwa [show s + (rest.map Prod.fst).sum - s = (rest.map Prod.fst).sum by omega]
      · rw [if_neg h2]
end Formalism.FourierDecayAlt.P.PBD
