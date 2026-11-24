-- Prove2me | solution 1 for Formalism.L2.SG.GGMirabolic.termsGGBound_of_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:17:23.227806+00:00
-- url     : https://prove2.me/submissions/46ea4a68-f989-4f4c-8b8d-9cb3c295e549

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicBase
import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.GGMirabolic
open Finset Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Classical
namespace Formalism.L2.SG.GGMirabolic
theorem _root_.solution (h : GGMatrixBound) : TermsGGBound := by
  intro ι _ Fq _ _ k ψ hψ hq X _ _ hfree d hd τ Rw H H₁ _ _ _ _ T hGG hG1
  have h2 := (h ι Fq k ψ hψ hq X hfree d hd).2
  unfold Formalism.FourierDecayAlt.PB.Terms.GGBound
  have hM : Matrix.of T.GG = Matrix.of fun i j =>
      if ∃ x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ, x • j = i then conj (gamProd ψ (d i j)) else 0 := by
    ext i j; simp [hGG]
  rw [hM, hG1]
  convert h2 using 3
end Formalism.L2.SG.GGMirabolic
