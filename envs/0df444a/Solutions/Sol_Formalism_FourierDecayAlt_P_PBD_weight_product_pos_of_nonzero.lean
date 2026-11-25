-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.weight_product_pos_of_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:41:14.141309+00:00
-- url     : https://prove2.me/submissions/5a73a3fa-3289-4acd-9c8a-68945cf94402

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
theorem _root_.solution (k r : ℕ) (GG : ℝ) (fr : ℕ → ℕ → ℝ) (hfr : ∀ b s, 0 < fr b s) :
    ∀ (p : C.LPt) (b : ℕ), 1 ≤ b → b + D.ptSize p ≤ r + 1 → (∀ x ∈ p, 1 ≤ x.1 ∧ x.2 ≠ 0) →
      0 < C.nAux k r GG fr b p
  | [], _, _, _, _ => by simp [C.nAux]
  | (s, t) :: rest, b, hb, hs, h => by
    have h1 := h (s, t) (by simp)
    have ht : 0 < ‖t‖ := norm_pos_iff.2 h1.2
    simp only [D.ptSize, List.map_cons, List.sum_cons] at hs
    have ih := solution k r GG fr hfr rest (b + s) (by omega) (by simp only [D.ptSize]; omega)
      (fun y hy => h y (by simp [hy]))
    simp only [C.nAux]
    refine mul_pos ?_ ih
    have : ¬ (b + s - 1 = r + 1 ∧ s = 1) := by
      rintro ⟨h1, h2⟩
      have : 0 ≤ (rest.map Prod.fst).sum := Nat.zero_le _
      omega
    rw [if_neg this]
    exact zpow_pos (mul_pos (hfr b s) ht) _
end Formalism.FourierDecayAlt.P.PBD
