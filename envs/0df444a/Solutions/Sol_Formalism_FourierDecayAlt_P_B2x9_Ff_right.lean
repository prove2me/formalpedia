-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.Ff_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:29:28.022552+00:00
-- url     : https://prove2.me/submissions/1cc84b25-9643-490e-879f-7dc31a2bcbb8

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_mulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lmulM_cont
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
theorem _root_.solution (μP : Measure (Mt k (1 + r'))) (hμP : IsHaarOn (P1set k r') μP) {f : Mt k (1 + r') → ℝ≥0∞} (hf : Measurable f)
    (g q : Mt k (1 + r')) (hq : q ∈ (P1set k r' : Set (Mt k (1 + r')))) : Ff μP f (mulM (g, q)) = Ff μP f g := by
  unfold Ff
  have hmeas : Measurable fun q' : Mt k (1 + r') => f (mulM (g, q')) :=
    hf.comp (mulM_cont.comp (continuous_const.prodMk continuous_id)).measurable
  calc ∫⁻ q', f (mulM (mulM (g, q), q')) ∂μP
      = ∫⁻ q', f (mulM (g, lmulM q q')) ∂μP := by
        congr 1; funext q'; congr 1
        show Matrix.of g * Matrix.of q * Matrix.of q' = Matrix.of g * (Matrix.of q * Matrix.of q')
        exact Matrix.mul_assoc _ _ _
    _ = ∫⁻ q', f (mulM (g, q')) ∂(μP.map (lmulM q)) := (lintegral_map hmeas (lmulM_cont q).measurable).symm
    _ = ∫⁻ q', f (mulM (g, q')) ∂μP := by rw [hμP.left q hq]
end Formalism.FourierDecayAlt.P.B2x9
