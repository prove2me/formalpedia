-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.exists_polyOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:59:28.550692+00:00
-- url     : https://prove2.me/submissions/35a93cfd-f193-4358-a644-b628c26014b8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UsCompose
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_op_cons

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
theorem _root_.solution {o κ : ℕ} : ∀ Θ : DiffOp k r Wp Wq,
    (∀ T ∈ Θ, T.word.length ≤ o ∧ ∃ P : Mat k r → ℂ, U.IsPolyDeg κ P ∧
      ∀ g, T.coef g = P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) →
    ∃ Θ' : DiffOp k r Wp Wq, CutMP.PolyOp o κ Θ' ∧ ∀ F, opApply Θ' F = opApply Θ F
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, fun _ => rfl⟩
  | T :: Θ, h => by
    obtain ⟨Θ', h1, h2⟩ := solution Θ fun T' hT' => h T' (by simp [hT'])
    obtain ⟨hl, P, hP, hc⟩ := h T (by simp)
    refine ⟨scalTerm P T.word T.word_lie :: Θ', fun T' hT' => ?_, fun F => ?_⟩
    · rcases List.mem_cons.1 hT' with rfl | h'
      · exact ⟨hl, P, hP, fun _ => rfl, fun _ => rfl⟩
      · exact h1 T' h'
    · rw [op_cons, op_cons, h2]
      funext g
      rw [hc g]; rfl
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
