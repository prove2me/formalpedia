-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.weight_product_append
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:54:02.967811+00:00
-- url     : https://prove2.me/submissions/08390114-f319-41cb-91f4-d3a4dd7f960e

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
theorem _root_.solution (k r : ℕ) (GG : ℝ) (fr : ℕ → ℕ → ℝ) (x : ℕ × ℂ) : ∀ (h : C.LPt) (b : ℕ),
    C.nAux k r GG fr b (h ++ [x]) = C.nAux k r GG fr b h * C.nAux k r GG fr (b + D.ptSize h) [x]
  | [], b => by simp [C.nAux, D.ptSize]
  | (s, t) :: rest, b => by
    have ih := solution k r GG fr x rest (b + s)
    simp only [List.cons_append, C.nAux, ih, D.ptSize, List.map_cons, List.sum_cons, add_assoc, mul_assoc]
end Formalism.FourierDecayAlt.P.PBD
