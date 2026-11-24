-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.swap_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:46:37.53817+00:00
-- url     : https://prove2.me/submissions/000a667a-005b-4732-bfd4-64373f477dbf

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_ae_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_uw_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_conjM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_first_coordinate_map_measurable

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
variable {k r : ℕ}
attribute [local fun_prop] mulM_meas invM_meas
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
theorem _root_.solution {z : Vc k r} {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (hW : IsHaarOn (UWset k r z) μW) (hc : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN) :
    (μW.prod μN).map m1 = (μW.prod μN).map mulM := by
  ext S hS
  rw [Measure.map_apply first_coordinate_map_measurable hS, Measure.map_apply mulM_meas hS,
    Measure.prod_apply (first_coordinate_map_measurable hS), Measure.prod_apply (mulM_meas hS)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem hW] with h hh
  have hu := uw_unit hh
  have hT' : MeasurableSet (Prod.mk h ⁻¹' (m1 ⁻¹' S)) :=
    (measurable_const.prodMk measurable_id : Measurable fun n : Mt k r => (h, n)) (first_coordinate_map_measurable hS)
  have hset : Prod.mk h ⁻¹' (mulM ⁻¹' S) = conjM (Matrix.of h) ⁻¹' (Prod.mk h ⁻¹' (m1 ⁻¹' S)) := by
    ext n
    simp only [Set.mem_preimage, m1]
    have e : mulM (conjM (Matrix.of h) n, h) = mulM (h, n) := by
      show (Matrix.of h : Mat k r) * Matrix.of n * (Matrix.of h : Mat k r)⁻¹ * Matrix.of h =
        (Matrix.of h : Mat k r) * Matrix.of n
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
    rw [e]
  rw [hset, ← Measure.map_apply (conjM_cont _).measurable hT', hc _ hh]
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
