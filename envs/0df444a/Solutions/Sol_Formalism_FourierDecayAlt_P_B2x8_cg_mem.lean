-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.cg_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:04:54.212156+00:00
-- url     : https://prove2.me/submissions/27779edf-d34c-4601-a712-8b1df0ead4ec

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_first
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_middle
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hb_im

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (R : ℝ) (hR : 0 ≤ R) (p : ℂ × HPar k r') (h1 : p.1 ≠ 0) (h : ‖Ψt k r' p‖ ≤ R) : p ∈ cgS k r' R := by
  have hall : ∀ i, ‖Ψt k r' p i‖ ≤ R := fun i => (norm_le_pi_norm _ i).trans h
  have hL : cL (Ψt k r' p) = p.1 := by unfold Ψt; rw [three_block_last]
  have hM : mid (Ψt k r' p) = p.2.1 := by unfold Ψt; rw [three_block_middle]
  have hF : cF (Ψt k r' p) = hb k r' p.2.1 p.2.2 / conj p.1 := by unfold Ψt; rw [three_block_first]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hL]; exact hall _
  · rw [← hM, pi_norm_le_iff_of_nonneg hR]; intro j; exact hall _
  · have h3 : ‖hb k r' p.2.1 p.2.2 / conj p.1‖ ≤ R := by rw [← hF]; exact hall _
    rw [norm_div, RCLike.norm_conj, div_le_iff₀ (norm_pos_iff.2 h1)] at h3
    refine le_trans ?_ h3
    have := Complex.abs_im_le_norm (hb k r' p.2.1 p.2.2)
    rwa [hb_im] at this
end Formalism.FourierDecayAlt.P.B2x8
