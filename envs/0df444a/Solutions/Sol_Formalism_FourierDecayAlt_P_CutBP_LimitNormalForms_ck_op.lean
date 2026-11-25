-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.ck_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:21:12.576387+00:00
-- url     : https://prove2.me/submissions/b2c02dfa-5850-412a-aae0-f54e0ec68fb2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UsCompose
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_ck_ap
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_ck_Rw__802bba5733f4
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_op_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_op_nil
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ContDiff Topology
set_option linter.unusedSectionVars false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
theorem _root_.solution {m : ℕ∞} {o : ℕ} {UU : Set (Mat k r)} {J : Mat k r → (Wq →L[ℂ] Wp)} (hJ : CkOn (m + o) UU J) :
    ∀ Θ : DiffOp k r Wp Wq, (∀ T ∈ Θ, CkOn ⊤ UU T.coef ∧ T.word.length ≤ o) → CkOn m UU (opApply Θ J)
  | [], _ => by rw [op_nil]; exact CkOn_zero
  | T :: Θ, h => by
    rw [op_cons]
    have hT := h T (by simp)
    refine CkOn_add (ck_ap (sCkOn_mono le_top hT.1) (ck_Rw' T.word_lie (sCkOn_mono ?_ hJ)))
      (solution hJ Θ (fun T' hT' => h T' (by simp [hT'])))
    have : (T.word.length : ℕ∞) ≤ (o : ℕ∞) := by exact_mod_cast hT.2
    exact add_le_add le_rfl this
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
