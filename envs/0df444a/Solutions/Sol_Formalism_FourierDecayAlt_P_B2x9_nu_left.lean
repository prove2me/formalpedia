-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.nu_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:04:03.94972+00:00
-- url     : https://prove2.me/submissions/05affa2e-163a-48b6-8e2a-964c40fe1299

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_sigmaFinite_of_haar
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_II_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_nu_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lmulM_cont


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
    (hP : IsClosedSubgroup (P1set k r')) (hμP : IsHaarOn (P1set k r') (muP μG₁))
    (a : Mat k (1 + r')) (ha : a ∈ GV k (1 + r')) : (nu μG₁).map (lmulM a) = nu μG₁ := by
  haveI := sigmaFinite_of_haar h₁
  ext S hS
  rw [Measure.map_apply (lmulM_cont a).measurable hS, nu_apply _ _ ((lmulM_cont a).measurable hS),
    nu_apply _ _ hS]
  have hi : (lmulM a ⁻¹' S).indicator (1 : Mt k (1 + r') → ℝ≥0∞) = fun g => S.indicator 1 (lmulM a g) := by
    funext g
    first | rfl | simp [Set.indicator_apply]
  rw [hi]
  exact II_inv HIv hG HA HI OM OC CI SD μG₁ h₁ hP hμP _ (measurable_one.indicator hS) a ha
end Formalism.FourierDecayAlt.P.B2x9
