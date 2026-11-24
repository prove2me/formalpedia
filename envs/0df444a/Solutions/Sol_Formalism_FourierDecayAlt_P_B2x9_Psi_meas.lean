-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.Psi_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:59:21.088816+00:00
-- url     : https://prove2.me/submissions/8de3196e-2fe8-4e66-aa11-2042062ecc02

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_mulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_heisenberg_map_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_long_weyl_family_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_levM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_levM_cont
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
variable {k r r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution : Measurable (Psi k r') := by
  have hm : ∀ {α : Type} [MeasurableSpace α] (f g : α → Mt k (1 + r')), Measurable f → Measurable g →
      Measurable fun p => mulM (f p, g p) :=
    fun f g hf hg => mulM_cont.measurable.comp (hf.prodMk hg)
  have hx : Measurable fun p : ℂ × ((HPar k r' × HPar k r') × Mt k r') => heisF k r' p.2.1.1 :=
    heisenberg_map_continuous.measurable.comp (measurable_fst.comp (measurable_fst.comp measurable_snd))
  have hx' : Measurable fun p : ℂ × ((HPar k r' × HPar k r') × Mt k r') => heisF k r' p.2.1.2 :=
    heisenberg_map_continuous.measurable.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hw : Measurable fun p : ℂ × ((HPar k r' × HPar k r') × Mt k r') => w0F k r' p.1 :=
    long_weyl_family_measurable.comp measurable_fst
  have hg : Measurable fun p : ℂ × ((HPar k r' × HPar k r') × Mt k r') => levM k r' p.2.2 :=
    levM_cont.measurable.comp (measurable_snd.comp measurable_snd)
  have hi : Measurable fun p : ℂ × ((HPar k r' × HPar k r') × Mt k r') => invM (heisF k r' p.2.1.1) :=
    invM_meas.comp hx
  exact hm _ _ (hm _ _ (hm _ _ hi hw) hg) hx'
end Formalism.FourierDecayAlt.P.B2x9
