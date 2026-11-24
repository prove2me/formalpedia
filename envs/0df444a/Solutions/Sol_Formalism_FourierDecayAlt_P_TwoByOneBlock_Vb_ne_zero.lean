-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.Vb_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:45:22.294847+00:00
-- url     : https://prove2.me/submissions/49c70780-b09c-44f6-b819-2b0a7d63b8bd

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Sq_cont

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
theorem _root_.solution (k : ℕ) : Vb k ≠ 0 := by
  have ho : IsOpen {x : Fin k → ℂ | Sq k x < 1} := isOpen_lt (Sq_cont k) continuous_const
  have hn : {x : Fin k → ℂ | Sq k x < 1}.Nonempty := ⟨0, by simp [Sq]⟩
  have := ho.measure_pos volume hn
  exact (this.trans_le (measure_mono fun x (hx : Sq k x < 1) => (le_of_lt hx : Sq k x ≤ 1))).ne'
end Formalism.FourierDecayAlt.P.TwoByOneBlock
