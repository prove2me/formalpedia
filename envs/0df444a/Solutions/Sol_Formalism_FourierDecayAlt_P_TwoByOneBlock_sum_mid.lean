-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.sum_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:53:40.947916+00:00
-- url     : https://prove2.me/submissions/d9425403-149b-43b5-8405-8608662281a4

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mid_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_wI_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_wI_inj


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
theorem _root_.solution (f : Fin (2 * r + k + 1) → ℂ) (hf : ∀ i, ¬ mid k r i → f i = 0) :
    ∑ i, f i = ∑ a : Fin (k + 1), f (wI k r a) := by
  symm
  apply Finset.sum_of_injOn (wI k r) (wI_inj.injOn) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  · intro i _ hi
    apply hf
    intro hm
    obtain ⟨a, rfl⟩ := mid_exists hm
    exact hi ⟨a, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩
  · intro i _; rfl
end Formalism.FourierDecayAlt.P.TwoByOneBlock
