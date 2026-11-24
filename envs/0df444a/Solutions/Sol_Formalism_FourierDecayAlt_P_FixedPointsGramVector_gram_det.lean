-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FixedPointsGramVector.gram_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:15:27.044881+00:00
-- url     : https://prove2.me/submissions/4dedd63e-8eaf-44be-a9d8-ff8d59129a26

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedFrameProperty
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector
import Theorems.Thm_Formalism_QuantumDeterminants_gn_gramM_eq
import Theorems.Thm_Formalism_QuantumDeterminants_group_gram_holds


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
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FixedPointsGramVector
open C2x5 C2x6 C2x7 HermitianProjections
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FixedPointsGramVector
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hstd : C2.Std k r z z')
    (hpos : C2.PosPt k r z z' γ) : IsUnit ((gnB k r z z' γ)ᴴ * Hpk k r * gnB k r z z' γ).det := by
  rw [← gn_gramM_eq]
  have h := group_gram_holds k r z z' hstd.2.1.1 hstd.2.2.1 γ hpos.1
  apply isUnit_iff_ne_zero.mpr
  intro h0
  rw [h0, mul_zero] at h
  have := hpos.2
  have h' : (Gf k r z z' γ : ℂ) ≠ 0 := by exact_mod_cast this.ne'
  exact h' h
end Formalism.FourierDecayAlt.P.FixedPointsGramVector
