-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TheSec.gB_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:52:01.436+00:00
-- url     : https://prove2.me/submissions/a48159b5-250f-44b3-9ea5-b3412d06601f

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
theorem _root_.solution {b : Fin (k + 1) → ℂ} {T' : ℝ} (hT' : 0 < T') (hb : herm (Hb k) b b = -(T' : ℂ)) :
    (gB k b T')ᴴ * Hb k * gB k b T' = Hb k ∧
      gB k b T' *ᵥ b = ((Real.sqrt T' : ℝ) : ℂ) • Pi.single (Fin.last k) 1 := by
  have h : 0 < T' ∧ herm (Hb k) b b = -(T' : ℂ) := ⟨hT', hb⟩
  unfold gB
  rw [dif_pos h]
  exact Classical.choose_spec
    (transitive (Hb k) (Hb_herm k) b _ T' h.1 h.2 (herm_last_scaled k T' h.1))
end Formalism.FourierDecayAlt.P.TheSec
