-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dilation_scales_heisenberg_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:16:48.959144+00:00
-- url     : https://prove2.me/submissions/81bd6252-5b1d-4a0c-bd98-48332f85b2b0

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_dilation_conjugates_heisenberg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_conjM_cont
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x7__Heis_eq_c8a77834e8df
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_heisF_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_haarHPar
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_dilL_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_det_dilL
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_conjM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_conjM_cont
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x5__Heis_eq_adc2ccc881fd


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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open B2x7
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.DilHeisMeas := by
  intro k r' t ht
  have ht0 : t ≠ 0 := ht.ne'
  have hL : Measurable (dilL k r' t) := (LinearMap.continuous_of_finiteDimensional _).measurable
  have hH : Measurable (heisF k r') := heisF_cont.measurable
  have hC : Measurable (conjM (aDil k (1 + r') t) : Mt k (1 + r') → Mt k (1 + r')) := (conjM_cont _).measurable
  have hcomp : conjM (aDil k (1 + r') t) ∘ heisF k r' = heisF k r' ∘ dilL k r' t := by
    funext x
    show aDil k (1 + r') t * heis0 k r' x * (aDil k (1 + r') t)⁻¹ = heis0 k r' (dilL k r' t x)
    rw [dilation_conjugates_heisenberg k r' t ht0 x, dilL_apply]
  have := haarHPar k r'
  have hdet : LinearMap.det (dilL k r' t) ≠ 0 := by rw [det_dilL t ht0]; exact pow_ne_zero _ ht0
  rw [μHeis_eq, Measure.map_map hC hH, hcomp, ← Measure.map_map hH hL, Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, Measure.map_smul,
    det_dilL t ht0, abs_of_pos (inv_pos.mpr (pow_pos ht _))]
end Formalism.FourierDecayAlt.P
