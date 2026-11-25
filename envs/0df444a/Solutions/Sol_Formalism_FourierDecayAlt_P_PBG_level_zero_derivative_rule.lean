-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.level_zero_derivative_rule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:14:54.118999+00:00
-- url     : https://prove2.me/submissions/4fabe9d0-ecac-4d74-8b31-b469fd14ae6a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BaseIndexConstantInjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_position_level_zero_coord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_eh
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_ev_E
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
theorem _root_.solution (hD : IsOpen D) (z' : Fin (2 * r + k + 1) → ℂ) (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K)
    (hR : ∀ g ∈ Q.Glev k r 0 ∩ D, ∀ p q, C3.InNp k r p q → Q.EH k r p q K g = C3.dpsiP k r z' p q • K g)
    (p q : Fin (2 * r + k + 1)) (hpq : C3.InNp k r p q) :
    E0 hD p q (vK hD K hK) = C3.dpsiP k r z' p q • vK hD K hK := by
  refine Subtype.ext (funext fun g => ?_)
  by_cases hg : g ∈ Q.Glev k r 0 ∩ D
  · show ((Eh hD (c0 p) (c0 q) (vK hD K hK)) : Q.Mx k r → E) g = _
    rw [ev_E hD (c0 p) (c0 q) _ hg]
    have hl := (good_eh (E := E) hD (c0 p) (c0 q)).loc ((vK hD K hK) : Q.Mx k r → E) K
      (fun x hx => cut_of_mem K hx) g hg
    rw [hl]
    rw [position_level_zero_coord, position_level_zero_coord, hR g hg p q hpq]
    simp only [Submodule.coe_smul, Pi.smul_apply, vK]
    rw [cut_of_mem K hg]
  · rw [(E0 hD p q (vK hD K hK)).2.2 g hg]
    simp only [Submodule.coe_smul, Pi.smul_apply]
    rw [(vK hD K hK).2.2 g hg, smul_zero]
end Formalism.FourierDecayAlt.P.PBG
