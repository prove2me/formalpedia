-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:51:56.103803+00:00
-- url     : https://prove2.me/submissions/c9443454-f6f5-483b-b09b-2414e19102b4

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
theorem _root_.solution (k r : ℕ) (GG GG' : ℝ) (fr : ℕ → ℕ → ℝ) : ∀ (h : C.LPt) (b : ℕ), 1 ≤ b →
    b + D.ptSize h ≤ r + 1 → C.nAux k r GG fr b h = C.nAux k r GG' fr b h
  | [], _, _, _ => by simp [C.nAux]
  | (s, t) :: rest, b, hb, hs => by
    simp only [D.ptSize, List.map_cons, List.sum_cons] at hs
    have ih := solution k r GG GG' fr rest (b + s) (by omega) (by simp only [D.ptSize] at *; omega)
    simp only [C.nAux, ih]
    congr 1
    have : ¬ (b + s - 1 = r + 1 ∧ s = 1) := by
      rintro ⟨h1, h2⟩
      have : 0 ≤ (rest.map Prod.fst).sum := Nat.zero_le _
      omega
    rw [if_neg this, if_neg this]
end Formalism.FourierDecayAlt.P.PBD
