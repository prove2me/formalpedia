-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TheSec.gA_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:51:58.388805+00:00
-- url     : https://prove2.me/submissions/eeaa5d64-3a5a-4e4a-a807-e419bfba1f94

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSection
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_Hb_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_transitive


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TheSec
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction
variable (k : ℕ)
namespace Formalism.FourierDecayAlt.P.TheSec
theorem _root_.solution {a : Fin (k + 1) → ℂ} {T : ℝ} (hT : 0 < T) (ha : herm (Hb k) a a = -(T : ℂ)) :
    (gA k a T)ᴴ * Hb k * gA k a T = Hb k ∧
      gA k a T *ᵥ (((Real.sqrt T : ℝ) : ℂ) • Pi.single (Fin.last k) 1) = a := by
  have h : 0 < T ∧ herm (Hb k) a a = -(T : ℂ) := ⟨hT, ha⟩
  unfold gA
  rw [dif_pos h]
  exact Classical.choose_spec
    (transitive (Hb k) (Hb_herm k) _ a T h.1 (herm_last_scaled k T h.1) h.2)
end Formalism.FourierDecayAlt.P.TheSec
