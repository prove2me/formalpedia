-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.L_Rw_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:18:52.744931+00:00
-- url     : https://prove2.me/submissions/880edb74-a331-4a4d-8532-5e0646ab7c2f

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_ckOn_top_nat
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_ckOn_W_top
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_right_word_eq_word
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_allLie_lr__c50cf8bc3dd9
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_congr


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
theorem _root_.solution {X : Mat k r} (hX : inLie k r X) : ∀ (v : List (Mat k r)), (∀ Y ∈ v, inLie k r Y) →
    ∀ K : Mat k r → E, CkOn (⊤ : ℕ∞) (GV k r) K → ∀ g ∈ GV k r,
      Rw v (LdV X K) g = LdV X (Rw v K) g := by
  intro v
  induction v with
  | nil => intro _ K _ g _; rfl
  | cons Y v ih =>
    intro hv K hK g hg
    have hv' : ∀ Z ∈ v, inLie k r Z := fun Z hZ => hv Z (List.mem_cons_of_mem _ hZ)
    have hY := hv Y List.mem_cons_self
    show op false Y (Rw v (LdV X K)) g = op true X (op false Y (Rw v K)) g
    rw [op_congr false hY (ih hv' K hK) g hg]
    have hc : CkOn (⊤ : ℕ∞) (GV k r) (Rw v K) := by
      rw [right_word_eq_word]; exact ckOn_W_top _ (allLie_lr' (by simp) hv') hK
    exact op_comm (ckOn_top_nat hc 2) hX hY hg
end Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
