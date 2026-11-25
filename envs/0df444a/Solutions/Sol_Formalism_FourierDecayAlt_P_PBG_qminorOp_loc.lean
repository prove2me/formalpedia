-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.qminorOp_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:25:13.771551+00:00
-- url     : https://prove2.me/submissions/a2a2aa0e-9f10-40b8-98aa-178fc6df491a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BaseIndexConstantInjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_good_foldr
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_good_top_level_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_foldr
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
theorem _root_.solution (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f f₂ : Q.Mx k r → E)
    (h : ∀ x ∈ Q.Glev k r 0 ∩ D, f x = f₂ x) (g : Q.Mx k r) (hg : g ∈ Q.Glev k r 0 ∩ D) :
    qminorOp (Q.EH k r) a b u f g = qminorOp (Q.EH k r) a b u f₂ g := by
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  exact (good_foldr hD _ (fun T hT => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hT
    exact good_top_level_zero hD _ _ _)).loc f f₂ h g hg
end Formalism.FourierDecayAlt.P.PBG
