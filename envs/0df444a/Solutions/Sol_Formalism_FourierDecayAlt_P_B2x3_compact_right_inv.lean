-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.compact_right_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:01:27.990003+00:00
-- url     : https://prove2.me/submissions/7936aae3-2bcd-4cf2-9246-0856357fc087

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
theorem _root_.solution {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [MeasurableSpace Γ] [BorelSpace Γ]
    [CompactSpace Γ] (m : Measure Γ) [m.IsHaarMeasure] : m.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace (Measure.map (fun x => x * g) m) m
  have hu : (Measure.map (fun x => x * g) m) Set.univ = m Set.univ := by
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
  have h2 := hu
  rw [h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  have hpos : m Set.univ ≠ 0 := (isOpen_univ.measure_pos m ⟨1, trivial⟩).ne'
  have hfin : m Set.univ ≠ ⊤ := (isCompact_univ.measure_lt_top).ne
  have h3 : ((Measure.haarScalarFactor (Measure.map (fun x => x * g) m) m : ℝ≥0) : ℝ≥0∞) * m Set.univ = 1 * m Set.univ := by
    rw [h2, one_mul]
  rw [ENNReal.mul_left_inj hpos hfin] at h3
  rw [h]
  have h4 : Measure.haarScalarFactor (Measure.map (fun x => x * g) m) m = 1 := by exact_mod_cast h3
  rw [h4, one_smul]
end Formalism.FourierDecayAlt.P.B2x3
