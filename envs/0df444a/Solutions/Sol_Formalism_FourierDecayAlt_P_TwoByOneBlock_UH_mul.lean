-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:59:54.044249+00:00
-- url     : https://prove2.me/submissions/bc03b16d-26e3-42f8-bbe1-51891c82c1bf

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mem_UH_of_herm

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
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution {m : ℕ} {H g h : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UH H) (hh : h ∈ UH H) : g * h ∈ UH H := by
  apply mem_UH_of_herm
  intro x y
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, herm_UH hg, herm_UH hh]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
