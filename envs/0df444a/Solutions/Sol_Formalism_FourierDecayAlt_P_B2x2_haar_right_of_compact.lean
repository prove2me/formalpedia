-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.haar_right_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:01:26.876716+00:00
-- url     : https://prove2.me/submissions/cd752753-0c15-47a2-997b-7a9f43ad7cbd

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2
namespace Formalism.FourierDecayAlt.P.B2x2
theorem _root_.solution {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (g : G) : μ.map (· * g) = μ := by
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace (μ.map (· * g)) μ
  have hu : (μ.map (· * g)) Set.univ = μ Set.univ := by
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
  have h2 : (μ.map (· * g)) Set.univ = (Measure.haarScalarFactor (μ.map (· * g)) μ : ℝ≥0∞) * μ Set.univ := by
    conv_lhs => rw [h]
    rfl
  rw [hu] at h2
  have hfin : μ Set.univ ≠ ∞ := (isCompact_univ.measure_lt_top).ne
  have hpos : μ Set.univ ≠ 0 := (isOpen_univ.measure_pos μ Set.univ_nonempty).ne'
  have h1 : (Measure.haarScalarFactor (μ.map (· * g)) μ : ℝ≥0∞) = 1 := by
    have : (1 : ℝ≥0∞) * μ Set.univ = (Measure.haarScalarFactor (μ.map (· * g)) μ : ℝ≥0∞) * μ Set.univ := by
      rw [one_mul]; exact h2
    exact ((ENNReal.mul_left_inj hpos hfin).1 this).symm
  have h3 : Measure.haarScalarFactor (μ.map (· * g)) μ = 1 := by exact_mod_cast h1
  rw [h, h3, one_smul]
end Formalism.FourierDecayAlt.P.B2x2
