-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.Ff_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:13:00.485424+00:00
-- url     : https://prove2.me/submissions/4907c3f7-13d6-4456-a16e-a5f898131128

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_mulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_mulM_cont


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
theorem _root_.solution (μP : Measure (Mt k (1 + r'))) (S : Set (Mt k (1 + r'))) (hS : MeasurableSet S) (g : Mt k (1 + r')) :
    Ff μP (S.indicator 1) g = μP ((fun q => mulM (g, q)) ⁻¹' S) := by
  unfold Ff
  have hm : MeasurableSet ((fun q => mulM (g, q)) ⁻¹' S) :=
    (mulM_cont.comp (continuous_const.prodMk continuous_id)).measurable hS
  rw [← lintegral_indicator_one hm]
  first | rfl | (congr 1; ext q; simp [Set.indicator_apply])
end Formalism.FourierDecayAlt.P.B2x9
