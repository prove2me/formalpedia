-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.S1.assembleStab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:28:18.642204+00:00
-- url     : https://prove2.me/submissions/a43fa12a-7412-42d6-9a1b-c6ed7c34f58b

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_S1_rho_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_S1_rho_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_S1_parabolic_subgroup_closed

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9 Formalism.FourierDecayAlt.P.B2x9.S1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9.S1
theorem _root_.solution : AssembleStab := by
  intro hSemi hLev hG hHC hHH hConj hConjM hStab k r' μG₁ hμ
  obtain ⟨hBcl, hBhaar⟩ := hLev k r' (GV k r') μG₁ (hG k r') hμ
  have key := hSemi k (1 + r') (Hset k r') (ιLev k 1 r' '' GV k r') (μHeis k r') (μG₁.map (levM k r')) (rho k r')
    (hHC k r').2 hBcl
    (by
      rintro _ ⟨g, hg, rfl⟩ _ ⟨x, rfl⟩
      exact ⟨_, (hConj k r' g hg x).symm⟩)
    (by rw [← hStab]; exact parabolic_subgroup_closed hG)
    rho_cont
    (by
      rintro _ ⟨x, rfl⟩ _ ⟨g, _, rfl⟩
      exact rho_prod x g)
    (hHH k r') hBhaar
    (by
      rintro _ ⟨g, hg, rfl⟩
      exact hConjM k r' g hg)
  rw [← hStab] at key
  exact key
end Formalism.FourierDecayAlt.P.B2x9.S1
