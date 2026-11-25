-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.letter_minus_component_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:07.152795+00:00
-- url     : https://prove2.me/submissions/a3464b4c-0dfe-4e8d-b284-3e1a52007eb5

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BaseIndexConstantInjective
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBG_AAvop_congr__add1803a240c
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
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (Y : ℝ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    Formalism.FourierDecayAlt.D.vLet k r z z' j hj (false, Y) 0 f g =
      (conj (Dmin k r z z' g ⟨j, by omega⟩))⁻¹ • C3.AAvop k r j hj ((Y : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) f g := by
  show (if (0 : Fin 2) = 1 ∧ j = 0 then 0 else _) = _
  rw [if_neg (by simp)]
  show (if false = true then _ else _) = _
  rw [if_neg (by simp), AAvop_congr' (m₂ := j) (by simp) _ hj]
end Formalism.FourierDecayAlt.P.PBG
