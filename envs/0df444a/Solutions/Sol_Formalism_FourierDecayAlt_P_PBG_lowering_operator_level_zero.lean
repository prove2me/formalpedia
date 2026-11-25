-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.lowering_operator_level_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:59:49.267946+00:00
-- url     : https://prove2.me/submissions/2de39ee9-6e38-4cf8-99ad-ac1e7553d048

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BaseIndexConstantInjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_quantum_minor_level_eq_hat
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
theorem _root_.solution (hD : IsOpen D) (m : ℕ) (hm : m ≤ r) (ell : ℂ) (v : VS k r 0 D E) (g : Q.Mx k r)
    (hg : g ∈ Q.Glev k r 0 ∩ D) :
    C3.AAvop k r m hm ell (v : Q.Mx k r → E) g =
      ((C3.AAv k r (E0 (E := E) hD) (y0 g) m hm ell) v : Q.Mx k r → E) g := by
  unfold C3.AAvop C3.AAv
  rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs
  · rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, quantum_minor_level_eq_hat hD _ _ _ v g hg]
    rfl
  · simp
end Formalism.FourierDecayAlt.P.PBG
