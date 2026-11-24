-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.ptEntry_app_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:38:35.87128+00:00
-- url     : https://prove2.me/submissions/d0c7c69c-3fca-4515-b375-2a3ac655f4d9

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
theorem _root_.solution (c : ℂ) : ∀ (H : C.LPt) (a b : ℕ), a < D.ptSize H → b < D.ptSize H →
    D.ptEntry (H ++ [(1, c)]) a b = D.ptEntry H a b
  | [], a, b, ha, _ => by simp [D.ptSize] at ha
  | (s, t) :: rest, a, b, ha, hb => by
    simp only [D.ptSize, List.map_cons, List.sum_cons] at ha hb
    simp only [List.cons_append, D.ptEntry]
    by_cases h1 : a < s ∧ b < s
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : s ≤ a ∧ s ≤ b
      · rw [if_pos h2, if_pos h2]
        exact solution c rest (a - s) (b - s) (by simp only [D.ptSize]; omega) (by simp only [D.ptSize]; omega)
      · rw [if_neg h2, if_neg h2]
end Formalism.FourierDecayAlt.P.PBD
