-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gram_block_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:37:47.995832+00:00
-- url     : https://prove2.me/submissions/811e2e89-deb3-46f6-a061-c55bbc4d1a80

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x6_herm_ff
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_swap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x5 C2x6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.GramBlocks := by
  intro k r z z' hz hz' g hg
  have hH := GBasic.Hpk_herm k r

  have hpres : ∀ v w, herm (Hpk k r) (g *ᵥ v) (g *ᵥ w) = herm (Hpk k r) v w := by
    intro v w
    simp only [herm]
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, show gᴴ * Hpk k r * g = Hpk k r from hg]
  ext i j
  rcases i with a | a <;> rcases j with b | b
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₁₁]
    exact herm_ff hz.1 a b
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₁₂]
    rfl
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply]
    rw [ggHerm_swap _ hH]
    rfl
  · simp only [gramM, gramVec, Matrix.fromBlocks_apply₂₂]
    rw [hpres]
    exact herm_ff hz'.1 a b
end Formalism.FourierDecayAlt.P
