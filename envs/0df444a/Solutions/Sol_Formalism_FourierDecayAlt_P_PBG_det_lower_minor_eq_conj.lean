-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.det_lower_minor_eq_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:28:45.084535+00:00
-- url     : https://prove2.me/submissions/88c9f903-b9ff-47e1-9844-6792296254ca

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_xi_Y_zhat_identity
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
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (g₀ : Mat k r) (hg : g₀ ∈ GV k r) (m : ℕ) (hm : m ≤ r) :
    (Matrix.of fun a b : Fin m => y0 g₀ (Fin.castLE hm a) (C3.sR k r m hm b)).det =
      starRingEnd ℂ (Dmin k r z z' g₀ ⟨m, by omega⟩) := by
  unfold Dmin
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp only [Matrix.of_apply, y0, C3.sR]
  rw [(Formalism.FourierDecayAlt.P.SignAntidiagonal.xi_Y_zhat_identity k r z z' g₀ (Fin.castLE hm a) (Fin.castLE hm b) hg).2]
  rfl
end Formalism.FourierDecayAlt.P.PBG
