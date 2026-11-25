-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dilation_jacobian_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:37:16.284982+00:00
-- url     : https://prove2.me/submissions/ae0f04b7-3f8f-496a-a37a-1330748fcf67

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_dj_step

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.AssembleDilJac := by
  intro hU hN hRec _ hEx hLev hH hK
  have raw : DilJacRaw := by
    intro k r
    induction r with
    | zero =>
      intro μN _ t _
      have h1 : aDil k 0 t = 1 := by
        unfold aDil
        rw [← Matrix.diagonal_one]
        congr 1
        funext i
        have := i.isLt
        rw [if_neg (by omega), if_pos (by omega)]
      have h2 : (conjM (1 : Mat k 0) : Mt k 0 → Mt k 0) = id := by
        funext x
        simp [conjM]
        rfl
      have h3 : kap k 0 = 0 := by simp [kap]
      rw [h1, h2, h3]
      simp
    | succ r' ih =>
      rw [Nat.add_comm r' 1]
      intro μN hμN t ht
      obtain ⟨μ', hμ'⟩ := hEx k r'
      exact dj_step hU hN hRec hLev hH hK k r' μ' hμ' (ih μ' hμ') μN hμN t ht
  exact ⟨raw, fun k r Wp Wq _ _ _ _ D t ht => raw k r D.μN D.haarN t ht⟩
end Formalism.FourierDecayAlt.P
