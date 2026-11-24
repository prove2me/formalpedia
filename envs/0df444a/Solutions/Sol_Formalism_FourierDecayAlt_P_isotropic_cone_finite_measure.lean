-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.isotropic_cone_finite_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:27:54.581+00:00
-- url     : https://prove2.me/submissions/c9474362-678a-4688-aa2c-7e1b27eeffcf

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x8__t_meas_3efb4587c898
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cone_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_ae_first_coordinate_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cg_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cg_finite

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 B2x8
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.ConeFinite := by
  unfold Formalism.FourierDecayAlt.B2.ConeFinite
  intro k r' K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  rw [B2x8.cone_eq]
  refine lt_of_le_of_lt ?_ (B2x8.cg_finite (k := k) (r' := r') (max R 0) (le_max_right _ _))
  refine le_trans (measure_mono (hR.trans (Metric.closedBall_subset_closedBall (le_max_left R 0)))) ?_
  rw [Measure.map_apply B2x8.Ψt_meas measurableSet_closedBall]
  have hnull : (B2x8.μx.prod (volume : Measure (HPar k r'))) {p | ¬ p.1 ≠ 0} = 0 := ae_iff.mp B2x8.ae_first_coordinate_ne_zero
  have hsub : B2x8.Ψt k r' ⁻¹' Metric.closedBall 0 (max R 0) ⊆ B2x8.cgS k r' (max R 0) ∪ {p | ¬ p.1 ≠ 0} := by
    intro p hpK
    by_cases hp : p.1 ≠ 0
    · exact Or.inl (B2x8.cg_mem (max R 0) (le_max_right _ _) p hp (by simpa using hpK))
    · exact Or.inr hp
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
  rw [hnull, add_zero]
end Formalism.FourierDecayAlt.P
