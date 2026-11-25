-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.isotropic_cone_invariance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:57:10.974955+00:00
-- url     : https://prove2.me/submissions/b0999bfe-3341-444f-b67c-17a6cac43a8f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_Tl_mp
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_Tw_mp
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_Tn_mp
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_gen_induction
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_long_weyl_parametrisation_twist
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x8_cf_lev__t_c6e021a54e58
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x8_cf_heis__t_8476e10eaf02
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_ae_first_coordinate_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_ae_heisenberg_parameter_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cf_mulVec_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cf_inv_of

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
theorem _root_.solution : Formalism.FourierDecayAlt.B2.ConeInv := by
  unfold Formalism.FourierDecayAlt.B2.ConeInv
  intro k r' g hg
  have e : ∀ a b : Mat k (1 + r'), (fun x => (a * b) *ᵥ x) = (fun x => a *ᵥ x) ∘ (fun x => b *ᵥ x) := by
    intro a b; funext x; simp [Matrix.mulVec_mulVec]
  refine B2x8.gen_induction (fun g => (coneMeas k r').map (fun x => g *ᵥ x) = coneMeas k r') ?_ ?_ ?_ ?_ ?_ g hg
  · intro a b ha hb'
    try dsimp only at ha hb' ⊢
    rw [e, ← Measure.map_map (B2x8.cf_mulVec_meas a) (B2x8.cf_mulVec_meas b), hb', ha]
  · intro a b hab hb'
    try dsimp only at hab hb' ⊢
    rw [e, ← Measure.map_map (B2x8.cf_mulVec_meas a) (B2x8.cf_mulVec_meas b), hb'] at hab
    exact hab
  · intro x
    exact B2x8.cf_inv_of _ _ (B2x8.Tn_mp x) (B2x8.ae_first_coordinate_ne_zero.mono fun p hp => B2x8.cf_heis_Ψt x p hp)
  · intro c hc
    exact B2x8.cf_inv_of _ _ (B2x8.Tw_mp c hc)
      ((B2x8.ae_first_coordinate_ne_zero.and B2x8.ae_heisenberg_parameter_ne_zero).mono fun p hp => B2x8.long_weyl_parametrisation_twist c hc p hp.1 hp.2)
  · intro g₁ hg₁
    exact B2x8.cf_inv_of _ _ (B2x8.Tl_mp g₁ hg₁) (Filter.Eventually.of_forall fun p => B2x8.cf_lev_Ψt g₁ hg₁ p)
end Formalism.FourierDecayAlt.P
