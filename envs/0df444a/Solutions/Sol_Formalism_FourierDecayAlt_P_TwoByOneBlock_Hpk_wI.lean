-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.Hpk_wI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:17:18.092554+00:00
-- url     : https://prove2.me/submissions/f56ff9f2-36f0-495f-8c4b-536fc9182dd7

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mid_wI
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_wI_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Hpk_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_wI_inj
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_mid


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution (a b : Fin (k + 1)) : Hpk k r (wI k r a) (wI k r b) = Hb k a b := by
  rw [GBasic.Hpk_eq, GBasic.sig_mid _ _ _ (mid_wI a).1 (mid_wI a).2]
  unfold Hb
  rw [Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h
    rw [if_pos rfl, if_pos rfl]
    simp [GBasic.sgn, wI, Fin.ext_iff]
  · rw [if_neg h, if_neg (fun h' => h (wI_inj h').symm)]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
