-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.uWbFacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:52:04.787857+00:00
-- url     : https://prove2.me/submissions/5c457596-59f4-4b71-bd36-1b4c68322f5d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_bigCellFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UWb_iff

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
theorem _root_.solution : UWbFacts := by
  intro k r
  refine ⟨?_, ?_, ?_⟩
  · ext g
    rw [UWb_iff]
    constructor
    · rintro ⟨μ, hμ, rfl⟩
      exact ⟨μ, hμ, rfl⟩
    · rintro ⟨μ, hμ, rfl⟩
      exact ⟨μ, hμ, rfl⟩
  · rintro z g ⟨hg, hfix, _⟩
    exact ⟨hg, hfix⟩
  · intro c m hm
    obtain ⟨μ, _, rfl⟩ := (UWb_iff m).1 hm
    rw [← (bigCellFactor k r c μ).1, ← (bigCellFactor k r c μ).2]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
