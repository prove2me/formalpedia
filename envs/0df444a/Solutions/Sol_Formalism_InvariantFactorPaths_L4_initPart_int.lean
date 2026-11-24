-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.initPart_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:49:18.628795+00:00
-- url     : https://prove2.me/submissions/00d15253-e8f9-47dc-ba82-718f93573fee

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_ShiftLastLetterThresholds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_intPol_iff_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) (hf : f ∈ IntPol p σ) :
    initPart v e f ∈ IntPol p σ := by
  rw [intPol_iff_norm] at hf ⊢
  intro m
  rw [coeff_initPart]
  split_ifs
  · exact hf m
  · rw [norm_zero]
    exact zero_le_one
end Formalism.InvariantFactorPaths.L4
