-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.S2.oneStepNullFromInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:47:57.083503+00:00
-- url     : https://prove2.me/submissions/669d0128-2d89-4cea-9bf7-6eeaa56b0752

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_sigmaFinite_of_haar
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_S2_cOf_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_S2_sigmaFinite_of_haar

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9 Formalism.FourierDecayAlt.P.B2x9.S2
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x9.S2
theorem _root_.solution : OneStepNullFromInt := by
  intro hInt hEx OM k r' μG hG
  obtain ⟨μG₁, h₁⟩ := hEx k r'
  haveI := sigmaFinite_of_haar h₁
  obtain ⟨C, _, hF⟩ := hInt k r' μG μG₁ hG h₁
  have hSm : MeasurableSet {g : Mt k (1 + r') | herm (Hpk k (1 + r')) (Matrix.of g *ᵥ e0 k r') (e0 k r') = 0} :=
    measurableSet_eq_fun (cOf_meas k r') measurable_const
  rw [← lintegral_indicator_one hSm, hF _ (measurable_one.indicator hSm)]
  refine mul_eq_zero_of_right _ ?_
  refine (lintegral_congr (fun c => ?_)).trans lintegral_zero
  try dsimp only
  by_cases hc : c = 0
  · subst hc
    rw [norm_zero, zero_pow (by omega), ENNReal.ofReal_zero, zero_mul]
  · refine mul_eq_zero_of_right _ ?_
    have hae : ∀ᵐ p ∂((volume : Measure (HPar k r' × HPar k r')).prod μG₁), p.2 ∈ (GV k r' : Set (Mt k r')) := by
      rw [ae_iff]
      refine measure_mono_null (t := Set.univ ×ˢ {g : Mt k r' | g ∉ (GV k r' : Set (Mt k r'))})
        (fun p hp => ⟨Set.mem_univ _, hp⟩) ?_
      rw [Measure.prod_prod]
      exact mul_eq_zero_of_right _ h₁.conc
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [hae] with p hp
    have hv := (OM k r' p.1.1 p.1.2 c hc (Matrix.of p.2) hp).2
    refine Set.indicator_apply_eq_zero.2 (fun hn => ?_)
    have hn' : herm (Hpk k (1 + r')) (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2 *ᵥ e0 k r') (e0 k r') = 0 := hn
    exact absurd (hv.symm.trans hn') hc
end Formalism.FourierDecayAlt.P.B2x9.S2
