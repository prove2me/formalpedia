-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.haar_push
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:59:09.362043+00:00
-- url     : https://prove2.me/submissions/5e1b0635-eef3-4b1b-bba4-b0cd5725cdf2

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution {k r : ℕ} {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [MeasurableSpace Γ] [BorelSpace Γ]
    (m : Measure Γ) [m.IsMulLeftInvariant] [m.IsMulRightInvariant] [IsFiniteMeasureOnCompacts m] (hm0 : m ≠ 0)
    (φ : Γ → Mt k r) (hφ : IsClosedEmbedding φ)
    (hmul : ∀ a b : Γ, φ (a * b) = (Matrix.of (φ a) * Matrix.of (φ b) : Mat k r))
    (U : Set (Mat k r)) (hU : Set.range φ = U) : IsHaarOn U (m.map φ) := by
  have hmeas : Measurable φ := hφ.continuous.measurable
  have hUc : @IsClosed (Mt k r) _ U := hU ▸ hφ.isClosed_range
  have hUm : @MeasurableSet (Mt k r) _ U := hUc.measurableSet
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hmeas hUm.compl]
    have : φ ⁻¹' (U : Set (Mt k r))ᶜ = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro x hx
      exact hx (hU ▸ ⟨x, rfl⟩)
    rw [this, measure_empty]
  · intro a ha
    rw [← hU] at ha
    obtain ⟨γ, rfl⟩ := ha
    have hl : Measurable (lmulM (k := k) (r := r) (φ γ)) := by
      have : Continuous (lmulM (k := k) (r := r) (φ γ)) := by
        unfold lmulM
        exact Continuous.matrix_mul continuous_const continuous_id
      exact this.measurable
    rw [Measure.map_map hl hmeas]
    have : lmulM (φ γ) ∘ φ = φ ∘ (fun x => γ * x) := by
      funext x
      simp only [Function.comp, lmulM, hmul]
      rfl
    rw [this, ← Measure.map_map hmeas (measurable_const_mul γ), map_mul_left_eq_self]
  · intro a ha
    rw [← hU] at ha
    obtain ⟨γ, rfl⟩ := ha
    have hl : Measurable (rmulF (φ γ)) := by
      have : Continuous (rmulF (φ γ)) := by
        unfold rmulF
        exact Continuous.matrix_mul continuous_id continuous_const
      exact this.measurable
    rw [Measure.map_map hl hmeas]
    have : rmulF (φ γ) ∘ φ = φ ∘ (fun x => x * γ) := by
      funext x
      simp only [Function.comp, rmulF, hmul]
      rfl
    rw [this, ← Measure.map_map hmeas (measurable_mul_const γ), map_mul_right_eq_self]
  · intro K hK
    rw [Measure.map_apply hmeas hK.isClosed.measurableSet]
    exact (hφ.isCompact_preimage hK).measure_lt_top
  · intro h0
    apply hm0
    have := congrArg (fun μ => μ Set.univ) h0
    simp only [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero, Pi.zero_apply] at this
    exact Measure.measure_univ_eq_zero.mp this
end Formalism.FourierDecayAlt.P.B2x3
