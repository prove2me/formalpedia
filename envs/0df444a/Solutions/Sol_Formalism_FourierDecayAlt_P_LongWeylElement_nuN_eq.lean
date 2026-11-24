-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.nuN_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:04:09.250229+00:00
-- url     : https://prove2.me/submissions/e3b55684-51bc-47e4-8c56-021c4568f025

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_conjM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_sf
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_haar_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_mulM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_mm_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_levM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_heisF_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_thetaF_meas
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
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
variable {k r r' : ℕ}
attribute [local instance] sfHeis
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution (hC : HeisConjLevMeas) (hN : ClosedN) (μ' : Measure (Mt k r')) (hμ' : IsHaarOn (Nset k r') μ') :
    ((μHeis k r').prod (μ'.map (levM k r'))).map mulM =
      ((volume : Measure (HPar k r')).prod μ').map (thetaF k r') := by
  have : SigmaFinite μ' := sf hμ'
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  have h1 : Measurable fun a : Mt k (1 + r') × Mt k (1 + r') => F (mulM a) := hF.comp mulM_meas
  have h2 : Measurable fun a : HPar k r' × Mt k r' => F (thetaF k r' a) := hF.comp thetaF_meas
  rw [lintegral_map hF mulM_meas, lintegral_map hF thetaF_meas,
    lintegral_prod_symm' _ h1, lintegral_prod_symm' _ h2, lintegral_map h1.lintegral_prod_left' levM_meas]
  refine lintegral_congr_ae ?_
  filter_upwards [haar_ae hμ'] with n hn
  have hu : IsUnit (ιLev k 1 r' (Matrix.of n)).det := lev_unit _ ((hN k r').unit _ hn)
  have hm : Measurable fun y : Mt k (1 + r') => F (mulM (y, levM k r' n)) :=
    hF.comp (mm_meas measurable_id measurable_const)
  calc ∫⁻ y, F (mulM (y, levM k r' n)) ∂(μHeis k r')
      = ∫⁻ y, F (mulM (y, levM k r' n)) ∂((μHeis k r').map (conjM (ιLev k 1 r' (Matrix.of n)))) := by
        rw [hC k r' _ hn.1]
    _ = ∫⁻ y, F (mulM (conjM (ιLev k 1 r' (Matrix.of n)) y, levM k r' n)) ∂(μHeis k r') :=
        lintegral_map hm (conjM_cont _).measurable
    _ = ∫⁻ x, F (mulM (conjM (ιLev k 1 r' (Matrix.of n)) (heisF k r' x), levM k r' n)) := by
        rw [μHeis_eq]
        exact lintegral_map (hm.comp (conjM_cont _).measurable) heisF_meas
    _ = ∫⁻ x, F (thetaF k r' (x, n)) := by
        refine lintegral_congr fun x => ?_
        congr 1
        show ιLev k 1 r' (Matrix.of n) * heis0 k r' x * (ιLev k 1 r' (Matrix.of n))⁻¹ * ιLev k 1 r' (Matrix.of n) =
          ιLev k 1 r' (Matrix.of n) * heis0 k r' x
        rw [Matrix.nonsing_inv_mul_cancel_right _ _ hu]
end Formalism.FourierDecayAlt.P.LongWeylElement
