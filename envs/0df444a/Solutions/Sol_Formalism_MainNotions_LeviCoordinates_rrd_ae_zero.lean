-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrd_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:41:42.17127+00:00
-- url     : https://prove2.me/submissions/8ed9d90e-eed0-4e46-b09e-a4535b5dfb57

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrdStronglyMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.MainNotions.LeviCoordinates
open MeasureTheory Filter Topology Set TopologicalSpace
open scoped InnerProductSpace
section Trans
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
private theorem integrable_mul_of_norm_le_of_stronglyMeasurable {α : Type*} [MeasurableSpace α] {ν : Measure α} {f ψ : α → ℂ}
    (hf : Integrable f ν) (hψ : StronglyMeasurable ψ) (M : ℝ) (hM : ∀ g, ‖ψ g‖ ≤ M) :
    Integrable (fun g => f g * ψ g) ν := by
  refine Integrable.mono' (hf.norm.mul_const M) (hf.aestronglyMeasurable.mul hψ.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun g => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM g) (norm_nonneg _)
end Trans
section Main
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SeparableSpace H]
variable {π : G → (H →L[ℂ] H)}
end Main
end Formalism.MainNotions.LeviCoordinates
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Filter Topology Set TopologicalSpace
open scoped InnerProductSpace
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution [SigmaFinite μ] [IsLocallyFiniteMeasure μ] (ψ : G → ℂ) (hψ : StronglyMeasurable ψ) (M : ℝ)
    (hM : ∀ g, ‖ψ g‖ ≤ M) (h0 : ∀ f : G → ℂ, Continuous f → Integrable f μ → ∫ g, f g * ψ g ∂μ = 0) :
    ψ =ᵐ[μ] 0 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  have hreg : μ.WeaklyRegular := by
    first
    | infer_instance
    | exact Measure.WeaklyRegular.of_pseudoMetrizableSpace_secondCountable_of_locallyFinite
  have hint_r : ∀ s, MeasurableSet s → μ s < ⊤ → IntegrableOn ψ s μ := by
    intro s hs hμs
    have hc : IntegrableOn (fun _ : G => M) s μ := by
      first
      | exact integrableOn_const hμs.ne
      | exact integrableOn_const.2 (Or.inr hμs)
      | exact integrableOn_const_iff.2 (Or.inr hμs)
    exact Integrable.mono' hc hψ.aestronglyMeasurable (Filter.Eventually.of_forall hM)
  have hzero : ∀ s, MeasurableSet s → μ s < ⊤ → ∫ x in s, ψ x ∂μ = 0 := by
    intro s hs hμs
    have hk : Integrable (s.indicator fun _ : G => (1 : ℂ)) μ := by
      rw [integrable_indicator_iff hs]
      first
      | exact integrableOn_const hμs.ne
      | exact integrableOn_const.2 (Or.inr hμs)
      | exact integrableOn_const_iff.2 (Or.inr hμs)
    have hI : ∫ x in s, ψ x ∂μ = ∫ x, s.indicator (fun _ : G => (1 : ℂ)) x * ψ x ∂μ := by
      rw [← integral_indicator hs]
      congr 1
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hI]
    have key : ∀ ε > 0, ‖∫ x, s.indicator (fun _ : G => (1 : ℂ)) x * ψ x ∂μ‖ ≤ ε := by
      intro ε hε
      have hε' : 0 < ε / (M + 1) := div_pos hε hM1
      obtain ⟨φ, hφ⟩ := hk.exists_boundedContinuous_integral_sub_le hε'
      have hφi : Integrable (⇑φ) μ := by
        first
        | exact hφ.2
        | exact hφ.1
      have hφd : ∫ x, ‖s.indicator (fun _ : G => (1 : ℂ)) x - φ x‖ ∂μ ≤ ε / (M + 1) := by
        first
        | exact hφ.1
        | exact hφ.2
      have e : ∫ x, s.indicator (fun _ : G => (1 : ℂ)) x * ψ x ∂μ =
          ∫ x, (s.indicator (fun _ : G => (1 : ℂ)) x - φ x) * ψ x ∂μ := by
        have hsplit : (fun x => (s.indicator (fun _ : G => (1 : ℂ)) x - φ x) * ψ x) =
            fun x => s.indicator (fun _ : G => (1 : ℂ)) x * ψ x - φ x * ψ x :=
          funext fun x => sub_mul _ _ _
        rw [hsplit, integral_sub (integrable_mul_of_norm_le_of_stronglyMeasurable hk hψ M hM) (integrable_mul_of_norm_le_of_stronglyMeasurable hφi hψ M hM),
          h0 φ φ.continuous hφi, sub_zero]
      rw [e]
      calc ‖∫ x, (s.indicator (fun _ : G => (1 : ℂ)) x - φ x) * ψ x ∂μ‖
          ≤ ∫ x, ‖s.indicator (fun _ : G => (1 : ℂ)) x - φ x‖ * M ∂μ := by
            refine norm_integral_le_of_norm_le ((hk.sub hφi).norm.mul_const M)
              (Filter.Eventually.of_forall fun x => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)
        _ = (∫ x, ‖s.indicator (fun _ : G => (1 : ℂ)) x - φ x‖ ∂μ) * M := integral_mul_const _ _
        _ ≤ ε / (M + 1) * M := mul_le_mul_of_nonneg_right hφd hM0
        _ ≤ ε / (M + 1) * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) hε'.le
        _ = ε := by field_simp
    by_contra hne
    have hpos : 0 < ‖∫ x, s.indicator (fun _ : G => (1 : ℂ)) x * ψ x ∂μ‖ := norm_pos_iff.2 hne
    have := key _ (half_pos hpos)
    linarith
  exact ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite hint_r hzero
end Formalism.MainNotions.LeviCoordinates
