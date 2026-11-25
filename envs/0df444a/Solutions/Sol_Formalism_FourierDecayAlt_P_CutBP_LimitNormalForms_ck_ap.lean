-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.ck_ap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:06:51.64003+00:00
-- url     : https://prove2.me/submissions/5207e8e1-abd7-4123-b5f2-a736cac0b2d5

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UsCompose
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_Bd_mono


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
variable {k r : ℕ} {E₁ E₂ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
theorem _root_.solution {m : ℕ∞} {UU : Set (Mat k r)} {a : Mat k r → (E₁ →L[ℂ] E₂)} {Φ : Mat k r → E₁}
    (ha : CkOn m UU a) (hΦ : CkOn m UU Φ) : CkOn m UU (fun g => a g (Φ g)) := by
  intro g₀ hg₀
  obtain ⟨U, a', hU, hgU, hc, hff⟩ := ha g₀ hg₀
  obtain ⟨U₂, Φ', hU₂, hgU₂, hc₂, hff₂⟩ := hΦ g₀ hg₀
  refine ⟨U ∩ U₂, fun g => a' g (Φ' g), hU.inter hU₂, ⟨hgU, hgU₂⟩, ?_,
    fun g hg hgG => by simp only [hff g hg.1 hgG, hff₂ g hg.2 hgG]⟩
  have h1 : ContDiffOn ℝ (m : WithTop ℕ∞)
      (fun g => ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ (a' g)) (U ∩ U₂) :=
    (ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ).contDiff.comp_contDiffOn
      (hc.mono Set.inter_subset_left)
  exact h1.clm_apply (hc₂.mono Set.inter_subset_right)
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
