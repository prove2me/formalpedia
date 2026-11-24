-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.Vb_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:19:08.079265+00:00
-- url     : https://prove2.me/submissions/ba67e6fd-5d5c-4d80-8723-bf4861bf780e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans

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
open Set
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution (k : ℕ) : Vb k ≠ ∞ := by
  have : {x : Fin k → ℂ | Sq k x ≤ 1} ⊆ Metric.closedBall 0 1 := by
    intro x hx
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : Complex.normSq (x i) ≤ Sq k x :=
      Finset.single_le_sum (f := fun i => Complex.normSq (x i)) (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    have h2 : ‖x i‖ ^ 2 ≤ 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h1.trans hx
    nlinarith [norm_nonneg (x i)]
  exact ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono this)
end Formalism.FourierDecayAlt.P.TwoByOneBlock
