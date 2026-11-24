-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.eabH_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:23:29.755377+00:00
-- url     : https://prove2.me/submissions/ede8df6b-1c48-4c72-9bb0-806324d5df21

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_rdV_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution (a b : Fin (2 * r + k + 1)) {f₁ f₂ : Mat k r → E} {V : Set (Mat k r)} (hV : IsOpen V)
    {g : Mat k r} (hg : g ∈ V) (hgG : g ∈ GV k r) (he : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) :
    EabH (Hpk k r) a b f₁ g = EabH (Hpk k r) a b f₂ g := by
  unfold EabH
  rw [rdV_congr hV hg hgG (hermitian_part_one_mem_lie _) he, rdV_congr hV hg hgG (hermitian_part_two_mem_lie _) he]
end Formalism.FourierDecayAlt.P.PBG
