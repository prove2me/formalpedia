-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.nu_conc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:19:55.176251+00:00
-- url     : https://prove2.me/submissions/01aad36b-3eb8-436d-ab3d-664193e70e5b

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_sigmaFinite_of_haar
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_swap
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_nu_apply

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution (HIv : HaarInv) (hG : ClosedG) (HI : HeisInv) (OM : OneStepMem)
    (μG₁ : Measure (Mt k r')) (h₁ : IsHaarOn (GV k r') μG₁)
    (hP : IsClosedSubgroup (P1set k r')) (hμP : IsHaarOn (P1set k r') (muP μG₁)) :
    nu μG₁ ((GV k (1 + r'))ᶜ : Set (Mt k (1 + r'))) = 0 := by
  haveI := sigmaFinite_of_haar h₁
  have hGc : @IsClosed (Mt k (1 + r')) _ (GV k (1 + r')) := by
    have hG' := hG k (1 + r')
    first | exact hG'.1 | exact hG'.isClosed | exact hG'.closed | exact hG'.2
  rw [nu_apply _ _ ?hS]
  swap
  · exact hGc.measurableSet.compl
  unfold II
  refine (lintegral_congr (fun c => ?_)).trans lintegral_zero
  try dsimp only
  by_cases hc : c = 0
  · subst hc
    have hw : wt k r' 0 = 0 := by
      unfold wt
      rw [norm_zero, zero_pow (by omega), ENNReal.ofReal_zero]
    rw [hw, zero_mul]
  · have hae : ∀ᵐ p ∂((volume : Measure (HPar k r' × HPar k r')).prod μG₁), p.2 ∈ (GV k r' : Set (Mt k r')) := by
      rw [ae_iff]
      refine measure_mono_null (t := Set.univ ×ˢ {g : Mt k r' | g ∉ (GV k r' : Set (Mt k r'))})
        (fun p hp => ⟨Set.mem_univ _, hp⟩) ?_
      rw [Measure.prod_prod]
      exact mul_eq_zero_of_right _ h₁.conc
    refine mul_eq_zero_of_right _ ?_
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [hae] with p hp
    have hmem := (OM k r' p.1.1 p.1.2 c hc (Matrix.of p.2) hp).1
    classical
    rw [Set.indicator_apply, if_neg (fun hn => hn hmem)]
end Formalism.FourierDecayAlt.P.B2x9
