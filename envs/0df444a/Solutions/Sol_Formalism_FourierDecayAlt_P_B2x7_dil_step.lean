-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x7.dil_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:31:28.573989+00:00
-- url     : https://prove2.me/submissions/9bccfe79-3f79-4334-9978-b19383165752

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_aDil_inv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_dilation_levi_conjugation
import Theorems.Thm_Formalism_FourierDecayAlt_P_modular_exponent_recursion
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_conjM_cont
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x7__Heis_eq_c8a77834e8df
import Theorems.Thm_Formalism_FourierDecayAlt_P_dilation_scales_heisenberg_measure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_mulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_levM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_conjM_mulM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_conjM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_conjM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_levM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_mulM_cont
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
open Formalism.FourierDecayAlt.P.B2x7
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x7
theorem _root_.solution (μ' : Measure (Mt k r')) [SigmaFinite μ'] (t : ℝ) (ht : 0 < t)
    (h' : μ'.map (conjM (aDil k r' t)) = ENNReal.ofReal ((t ^ kap k r')⁻¹) • μ') :
    (((μHeis k r').prod (μ'.map (levM k r'))).map mulM).map (conjM (aDil k (1 + r') t)) =
      ENNReal.ofReal ((t ^ kap k (1 + r'))⁻¹) • ((μHeis k r').prod (μ'.map (levM k r'))).map mulM := by
  have ht0 : t ≠ 0 := ht.ne'
  have hC : Measurable (conjM (aDil k (1 + r') t) : Mt k (1 + r') → Mt k (1 + r')) := (conjM_cont _).measurable
  have hC' : Measurable (conjM (aDil k r' t) : Mt k r' → Mt k r') := (conjM_cont _).measurable
  have hM : Measurable (mulM : Mt k (1 + r') × Mt k (1 + r') → Mt k (1 + r')) := mulM_cont.measurable
  have hL : Measurable (levM k r') := levM_cont.measurable
  have hlev : (conjM (aDil k (1 + r') t) : Mt k (1 + r') → Mt k (1 + r')) ∘ levM k r' = levM k r' ∘ conjM (aDil k r' t) := by
    funext x
    exact dilation_levi_conjugation k r' t ht0 (Matrix.of x)
  have h2 : (μ'.map (levM k r')).map (conjM (aDil k (1 + r') t)) =
      ENNReal.ofReal ((t ^ kap k r')⁻¹) • μ'.map (levM k r') := by
    rw [Measure.map_map hC hL, hlev, ← Measure.map_map hL hC', h', Measure.map_smul]
  have : SFinite (μHeis k r') := by rw [μHeis_eq]; infer_instance
  rw [Measure.map_map hC hM, conjM_mulM _ (aDil_inv_mul _ _ _ ht0), ← Measure.map_map hM (hC.prodMap hC),
    ← Measure.map_prod_map _ _ hC hC, dilation_scales_heisenberg_measure k r' t ht, h2, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, Measure.map_smul, ← ENNReal.ofReal_mul (by positivity), ← mul_inv, ← pow_add, ← modular_exponent_recursion k r']
end Formalism.FourierDecayAlt.P.B2x7
