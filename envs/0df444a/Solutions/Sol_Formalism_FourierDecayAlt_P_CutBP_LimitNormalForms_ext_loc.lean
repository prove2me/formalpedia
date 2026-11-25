-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.ext_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:30:50.822384+00:00
-- url     : https://prove2.me/submissions/44dbd208-aef8-4a85-a710-69585267146c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UsCompose
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal

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
theorem _root_.solution {m : ℕ∞} {UU : Set (Mat k r)} {J : Mat k r → E₁} (hJ : CkOn m UU J) {g₀ : Mat k r} (hg₀ : g₀ ∈ UU) :
    ∃ (f : Mat k r → E₁) (U : Set (Mat k r)), CkOn m (GV k r) f ∧ IsOpen U ∧ g₀ ∈ U ∧
      ∀ x ∈ U, x ∈ GV k r → f x = J x := by
  obtain ⟨U, F, hU, hgU, hc, he⟩ := hJ g₀ hg₀
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU g₀ hgU
  let bb : ContDiffBump g₀ := ⟨ρ / 4, ρ / 2, by positivity, by linarith⟩
  refine ⟨fun x => (bb x : ℝ) • F x, Metric.ball g₀ (ρ / 4), ?_, Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity), fun x hx hxG => ?_⟩
  · intro y _
    by_cases hy : y ∈ Metric.closedBall g₀ (ρ / 2)
    · refine ⟨U, fun x => (bb x : ℝ) • F x, hU, hball (Metric.closedBall_subset_ball (by linarith) hy), ?_,
        fun _ _ _ => rfl⟩
      exact ((bb.contDiff (n := ⊤)).of_le (by exact_mod_cast le_top)).contDiffOn.smul hc
    · refine ⟨(Metric.closedBall g₀ (ρ / 2))ᶜ, fun _ => 0, Metric.isClosed_closedBall.isOpen_compl, hy,
        contDiffOn_const, fun x hx _ => ?_⟩
      have : bb x = 0 := by
        rw [← Function.notMem_support, bb.support_eq]
        exact fun h => hx (Metric.ball_subset_closedBall h)
      simp [this]
  · have h1 : bb x = 1 := bb.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    have hxU : x ∈ U := hball (Metric.ball_subset_ball (by linarith) hx)
    simp only [h1, one_smul]
    exact (he x hxU hxG).symm
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
