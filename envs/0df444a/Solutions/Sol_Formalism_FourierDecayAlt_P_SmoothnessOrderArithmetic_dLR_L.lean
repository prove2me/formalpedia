-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.dLR_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:35:24.658325+00:00
-- url     : https://prove2.me/submissions/13427ce3-0b3b-4039-a783-b65e1b1dd28c

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_foldr_LdV_eq_W_lr
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_allLie_lr__c50cf8bc3dd9
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_L_Rw_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
theorem _root_.solution {u v : List (Mat k r)} {X : Mat k r} (hu : ∀ Y ∈ u, inLie k r Y) (hv : ∀ Y ∈ v, inLie k r Y)
    (hX : inLie k r X) {F : Mat k r → E} (hF : CkOn (⊤ : ℕ∞) (GV k r) F) :
    ∀ g ∈ GV k r, dLR u v (LdV X F) g = dLR (u ++ [X]) v F g := by
  intro g hg
  have e1 : dLR u v (LdV X F) = W (lr u []) (Rw v (LdV X F)) := by
    rw [← foldr_LdV_eq_W_lr]; rfl
  have e2 : dLR (u ++ [X]) v F = W (lr u []) (LdV X (Rw v F)) := by
    rw [← foldr_LdV_eq_W_lr]; unfold dLR; rw [List.foldr_append]; rfl
  rw [e1, e2]
  exact W_congr _ (allLie_lr' hu (by simp)) (L_Rw_comm hX v hv F hF) g hg
end Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
