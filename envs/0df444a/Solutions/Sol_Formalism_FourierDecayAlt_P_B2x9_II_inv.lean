-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.II_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:46:24.038743+00:00
-- url     : https://prove2.me/submissions/63588050-47f2-412e-8954-63eaf87c4e5c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_eta_xi
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_sigmaFinite_of_haar
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_tau_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_xi_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_eta_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_cone_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_Ff_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_II_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_ae_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_mulVec_cont
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x9_ae_ne__c879158f29b8
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_Ff_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cone_eq


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
theorem _root_.solution (HIv : HaarInv) (hG : ClosedG) (HA : HeisAct) (HI : HeisInv) (OM : OneStepMem) (OC : OneStepCoord) (CI : ConeInv)
    (SD : StabDecomp) (μG₁ : Measure (Mt k r')) (h₁ : IsHaarOn (GV k r') μG₁)
    (hP : IsClosedSubgroup (P1set k r')) (hμP : IsHaarOn (P1set k r') (muP μG₁)) (f : Mt k (1 + r') → ℝ≥0∞) (hf : Measurable f)
    (a : Mat k (1 + r')) (ha : a ∈ GV k (1 + r')) : II μG₁ (fun g => f (lmulM a g)) = II μG₁ f := by
  haveI := sigmaFinite_of_haar h₁
  haveI : SigmaFinite (muP μG₁) := sigmaFinite_of_haar hμP
  have hfa : Measurable fun g => f (lmulM a g) := hf.comp (lmulM_cont a).measurable
  rw [II_eq HIv hG HI μG₁ h₁ hP hμP _ hfa, II_eq HIv hG HI μG₁ h₁ hP hμP f hf]
  have hE : Measurable fun v : Fin (2 * (1 + r') + k + 1) → ℂ => Ff (muP μG₁) f (tau k r' (eta k r' v)) :=
    (Ff_meas _ hf).comp (tau_meas.comp eta_meas)
  have e1 : ∀ x, Ff (muP μG₁) (fun g => f (lmulM a g)) x = Ff (muP μG₁) f (lmulM a x) := by
    intro x
    simp only [Ff]
    congr 1; funext q'; congr 1
    show a * (Matrix.of x * Matrix.of q') = a * Matrix.of x * Matrix.of q'
    exact (Matrix.mul_assoc _ _ _).symm
  have step1 : ∀ᵐ p ∂(mCone k r'), Ff (muP μG₁) (fun g => f (lmulM a g)) (tau k r' p) =
      Ff (muP μG₁) f (tau k r' (eta k r' (a *ᵥ xi k r' p))) := by
    filter_upwards [ae_ne (k := k) (r' := r'), ae_ne' CI a ha] with p hc hv
    obtain ⟨q, hq, hq'⟩ := key hG HA HI OM OC SD hP a ha p hc hv
    have hk : lmulM a (tau k r' p) = mulM (tau k r' (eta k r' (a *ᵥ xi k r' p)), q) := hq'
    rw [e1, hk, Ff_right _ hμP hf _ _ hq]
  rw [lintegral_congr_ae step1]
  have hxi : Measurable (xi k r') := xi_cont.measurable
  have hav : Measurable fun v : Fin (2 * (1 + r') + k + 1) → ℂ => a *ᵥ v := (mulVec_cont a).measurable
  calc ∫⁻ p, Ff (muP μG₁) f (tau k r' (eta k r' (a *ᵥ xi k r' p))) ∂(mCone k r')
      = ∫⁻ v, Ff (muP μG₁) f (tau k r' (eta k r' (a *ᵥ v))) ∂(coneMeas k r') := by
        rw [cone_eq, lintegral_map (f := fun v => Ff (muP μG₁) f (tau k r' (eta k r' (a *ᵥ v)))) (hE.comp hav) hxi]
    _ = ∫⁻ v, Ff (muP μG₁) f (tau k r' (eta k r' v)) ∂(coneMeas k r') := by
        conv_rhs => rw [← CI k r' a ha]
        rw [lintegral_map (f := fun v => Ff (muP μG₁) f (tau k r' (eta k r' v))) hE hav]
    _ = ∫⁻ p, Ff (muP μG₁) f (tau k r' (eta k r' (xi k r' p))) ∂(mCone k r') := by
        rw [cone_eq, lintegral_map (f := fun v => Ff (muP μG₁) f (tau k r' (eta k r' v))) hE hxi]
    _ = ∫⁻ p, Ff (muP μG₁) f (tau k r' p) ∂(mCone k r') := by
        apply lintegral_congr_ae
        filter_upwards [ae_ne (k := k) (r' := r')] with p hc
        rw [eta_xi p hc]
end Formalism.FourierDecayAlt.P.B2x9
