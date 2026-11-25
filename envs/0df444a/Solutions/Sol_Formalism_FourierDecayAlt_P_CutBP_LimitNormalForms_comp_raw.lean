-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.comp_raw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:22:12.026258+00:00
-- url     : https://prove2.me/submissions/3ceae457-f378-4b25-86d5-a2f92b19f8f7

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UsCompose
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_exists_polyOp
import Theorems.Thm_differential_operator_compose


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
theorem _root_.solution (ρ : ℕ) : ∀ (r : ℕ), r = 0 + ρ → ∀ (o₁ κ₁ o₂ κ₂ : ℕ) (Θ₁ Θ₂ : DiffOp k r Wp Wq),
    CutMP.PolyOp o₁ κ₁ Θ₁ → CutMP.PolyOp o₂ κ₂ Θ₂ →
    ∃ Θ : DiffOp k r Wp Wq, CutMP.PolyOp (o₁ + o₂) (κ₁ + κ₂) Θ ∧
      ∀ F : Mat k r → (Wq →L[ℂ] Wp), CkOn ((o₁ + o₂ : ℕ) : ℕ∞) (GV k r) F →
        ∀ g ∈ GV k r, opApply Θ F g = opApply Θ₁ (opApply Θ₂ F) g := by
  intro r hr
  subst hr
  intro o₁ κ₁ o₂ κ₂ Θ₁ Θ₂ h₁ h₂
  have hD : ∀ g : Mat k (0 + ρ), U.DjU k 0 ρ g = 1 := fun g => by
    unfold U.DjU; exact Matrix.det_isEmpty
  have toDD : ∀ {o κ : ℕ} {Θ : DiffOp k (0 + ρ) Wp Wq}, CutMP.PolyOp o κ Θ → U.InDD k 0 ρ o κ Θ := by
    intro o κ Θ h T hT
    obtain ⟨hl, P, hP, hc, -⟩ := h T hT
    exact ⟨hl, P, 0, 0, hP, fun g => by rw [hc g]; simp⟩
  obtain ⟨Θ, hΘ, he⟩ := differential_operator_compose k 0 ρ Wp Wq o₁ κ₁ o₂ κ₂ Θ₁ Θ₂ (toDD h₁) (toDD h₂)
  obtain ⟨Θ', h1, h2⟩ := exists_polyOp (o := o₁ + o₂) (κ := κ₁ + κ₂) Θ fun T hT => by
    obtain ⟨hl, P, a, b, hP, hc⟩ := hΘ T hT
    exact ⟨hl, P, by simpa using hP, fun g => by rw [hc g, hD]; simp⟩
  exact ⟨Θ', h1, fun F hF g hg => by rw [h2]; exact he F hF g hg (by rw [hD]; exact one_ne_zero)⟩
end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
