-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.pint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:36:07.688381+00:00
-- url     : https://prove2.me/submissions/f7cb7d29-38cd-4daf-b482-60f705e830a1

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_aesm_fderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
open MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {U : Set X} (hU : IsOpen U)
    (b : α → ℝ) (hb : Integrable b μ) :
    ∀ (N : ℕ) (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E'] (F : α → X → E'),
      (∀ ξ, ContDiffOn ℝ N (F ξ) U) → (∀ y ∈ U, AEStronglyMeasurable (fun ξ => F ξ y) μ) →
      (∀ i ≤ N, ∀ y ∈ U, ∀ ξ, ‖iteratedFDeriv ℝ i (F ξ) y‖ ≤ b ξ) →
      ContDiffOn ℝ N (fun y => ∫ ξ, F ξ y ∂μ) U ∧
      ∀ i ≤ N, ∀ y ∈ U, ∀ b' : α → ℝ, Integrable b' μ → (∀ ξ, ‖iteratedFDeriv ℝ i (F ξ) y‖ ≤ b' ξ) →
        ‖iteratedFDeriv ℝ i (fun y => ∫ ξ, F ξ y ∂μ) y‖ ≤ ∫ ξ, b' ξ ∂μ := by
  intro N
  induction N with
  | zero =>
    intro E' _ _ _ F hc hm hbd
    have h0 : ∀ y ∈ U, ∀ ξ, ‖F ξ y‖ ≤ b ξ := fun y hy ξ => by
      simpa [norm_iteratedFDeriv_zero] using hbd 0 le_rfl y hy ξ
    refine ⟨?_, ?_⟩
    · rw [Nat.cast_zero, contDiffOn_zero]
      refine continuousOn_of_dominated (F := fun y ξ => F ξ y) (bound := b) hm
        (fun y hy => Eventually.of_forall fun ξ => h0 y hy ξ) hb (Eventually.of_forall fun ξ => ?_)
      exact (hc ξ).continuousOn
    · intro i hi y hy b' hb' hbd'
      have hi0 : i = 0 := by omega
      subst hi0
      rw [norm_iteratedFDeriv_zero]
      refine norm_integral_le_of_norm_le hb' (Eventually.of_forall fun ξ => ?_)
      simpa [norm_iteratedFDeriv_zero] using hbd' ξ
  | succ N ih =>
    intro E' _ _ _ F hc hm hbd
    have hdiff : ∀ ξ, ∀ y ∈ U, DifferentiableAt ℝ (F ξ) y := fun ξ y hy =>
      ((hc ξ).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hy)
    have hc' : ∀ ξ, ContDiffOn ℝ N (fun y => fderiv ℝ (F ξ) y) U := fun ξ =>
      (hc ξ).fderiv_of_isOpen hU (by push_cast; exact le_rfl)
    have hm' : ∀ y ∈ U, AEStronglyMeasurable (fun ξ => fderiv ℝ (F ξ) y) μ := fun y hy =>
      aesm_fderiv (fun ξ => hdiff ξ y hy) (Filter.eventually_of_mem (hU.mem_nhds hy) hm)
    have hbd' : ∀ i ≤ N, ∀ y ∈ U, ∀ ξ, ‖iteratedFDeriv ℝ i (fun y => fderiv ℝ (F ξ) y) y‖ ≤ b ξ :=
      fun i hi y hy ξ => by rw [norm_iteratedFDeriv_fderiv]; exact hbd (i + 1) (by omega) y hy ξ
    obtain ⟨ihc, ihb⟩ := ih (X →L[ℝ] E') (fun ξ y => fderiv ℝ (F ξ) y) hc' hm' hbd'
    have hint : ∀ y ∈ U, Integrable (fun ξ => F ξ y) μ := fun y hy =>
      hb.mono' (hm y hy) (Eventually.of_forall fun ξ => by
        simpa [norm_iteratedFDeriv_zero] using hbd 0 (by omega) y hy ξ)
    have hder : ∀ y ∈ U, HasFDerivAt (fun y => ∫ ξ, F ξ y ∂μ) (∫ ξ, fderiv ℝ (F ξ) y ∂μ) y := by
      intro y hy
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun y ξ => F ξ y)
        (F' := fun y ξ => fderiv ℝ (F ξ) y) (bound := b) (hU.mem_nhds hy) ?_ (hint y hy) (hm' y hy) ?_ hb ?_
      · filter_upwards [hU.mem_nhds hy] with z hz using hm z hz
      · refine Eventually.of_forall fun ξ z hz => ?_
        have h1 := hbd 1 (by omega) z hz ξ
        rwa [norm_iteratedFDeriv_one] at h1
      · exact Eventually.of_forall fun ξ z hz => (hdiff ξ z hz).hasFDerivAt
    have hfd : ∀ y ∈ U, fderiv ℝ (fun y => ∫ ξ, F ξ y ∂μ) y = ∫ ξ, fderiv ℝ (F ξ) y ∂μ :=
      fun y hy => (hder y hy).fderiv
    refine ⟨?_, ?_⟩
    · rw [show ((N + 1 : ℕ) : WithTop ℕ∞) = (N : WithTop ℕ∞) + 1 by push_cast; rfl,
        contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun y hy => (hder y hy).differentiableAt.differentiableWithinAt, fun h => absurd h (by simp), ?_⟩
      exact ihc.congr fun y hy => hfd y hy
    · intro i hi y hy b' hb' hbd''
      cases i with
      | zero =>
        rw [norm_iteratedFDeriv_zero]
        refine norm_integral_le_of_norm_le hb' (Eventually.of_forall fun ξ => ?_)
        simpa [norm_iteratedFDeriv_zero] using hbd'' ξ
      | succ j =>
        rw [← norm_iteratedFDeriv_fderiv]
        have heq : (fderiv ℝ (fun y => ∫ ξ, F ξ y ∂μ)) =ᶠ[𝓝 y] (fun y => ∫ ξ, fderiv ℝ (F ξ) y ∂μ) := by
          filter_upwards [hU.mem_nhds hy] with z hz using hfd z hz
        rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
        exact ihb j (by omega) y hy b' hb' fun ξ => by rw [norm_iteratedFDeriv_fderiv]; exact hbd'' ξ
end Formalism.FourierDecayAlt.P.Ux10
