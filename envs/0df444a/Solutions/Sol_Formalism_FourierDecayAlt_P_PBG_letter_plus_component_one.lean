-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.letter_plus_component_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:27:49.980975+00:00
-- url     : https://prove2.me/submissions/c36463c8-55d2-4a21-95a6-e596703dd12a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BaseIndexConstantInjective
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBG_AAop_congr__23af70070c46
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val



set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (hj1 : 1 ≤ j) (Y : ℝ) (f : Q.Mx k r → E)
    (g : Q.Mx k r) :
    Formalism.FourierDecayAlt.D.vLet k r z z' j hj (true, Y) 1 f g =
      (Dmin k r z z' g ⟨j, by omega⟩)⁻¹ • C3.AAop k r (j - 1) (by omega) ((Y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) f g := by
  show (if (1 : Fin 2) = 1 ∧ j = 0 then 0 else _) = _
  rw [if_neg (by omega)]
  show (if true = true then _ else _) = _
  rw [if_pos rfl, AAop_congr' (m₂ := j - 1) (by simp) _ (by omega)]
end Formalism.FourierDecayAlt.P.PBG
