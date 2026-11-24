-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.cW_eq_of_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:46:59.805056+00:00
-- url     : https://prove2.me/submissions/9eeb5000-9e7c-44a4-8c31-5fb6ebb66263

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution {ι : Type} (D : SizeData₂ ι) (P : Par) (τ : ι) (l : ℕ) (h1 : D.mw τ l = 0)
    (h2 : D.mwF τ l = 0) (h3 : D.ecl τ l = 0) :
    D.cW P τ l = ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * ((P.h + (P.Nr : ℝ)) / ((l : ℝ) - 1) + 6)
      + (P.k : ℝ) * (P.S / (l : ℝ) + IlInd l (D.xlo τ) (D.xhi τ) (D.maxB τ))
      + gatedCoefficientTerm D P τ l
      + ((D.q τ : ℝ) * P.h / (l : ℝ)) * (1 + max 0 (Real.log (P.h / (l : ℝ)))) := by
  simp only [SizeData₂.cW, SizeData₂.depth, gatedCoefficientTerm, h1, h2, h3, Nat.cast_zero, mul_zero, add_zero,
    zero_mul, zero_add]
end Formalism.CohomologicalDescent.LogSmallConstantBounds
