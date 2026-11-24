-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_jV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:35:10.146274+00:00
-- url     : https://prove2.me/submissions/2e2c7e03-bd2b-4a52-a852-186176338e5d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_sum_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_jV_wI
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_jV_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Hpk_wI

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
theorem _root_.solution (u u' : Fin (k + 1) → ℂ) : herm (Hpk k r) (jV k r u) (jV k r u') = herm (Hb k) u u' := by
  show ∑ i, star (jV k r u') i * ∑ j, Hpk k r i j * jV k r u j = ∑ a, star u' a * ∑ b, Hb k a b * u b
  rw [sum_mid _ (fun i hi => by rw [Pi.star_apply, jV_out u' hi, star_zero, zero_mul])]
  apply Finset.sum_congr rfl
  intro a _
  rw [sum_mid _ (fun j hj => by rw [jV_out u hj, mul_zero])]
  simp only [Pi.star_apply, jV_wI, Hpk_wI]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
