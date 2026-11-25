-- Prove2me | solution 1 for Formalism.HermitianLattices.WeakMeanSquareEstimates.mean_square_weak_of_prime_number_theorem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:32:38.859856+00:00
-- url     : https://prove2.me/submissions/8226a31e-359c-4e7a-95d4-ba823942a205

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_MeanSquareOfPrimeNumberTheorem
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_MeanSquareWeakOfPrimeNumberTheorem
import Theorems.Thm_Formalism_HermitianLattices_PrimeNumberTheoremConsequences_mean_square_of_prime_number_theorem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.WeakMeanSquareEstimates
namespace Formalism.HermitianLattices.WeakMeanSquareEstimates
theorem _root_.solution : Formalism.HermitianLattices.PrimeNumberTheoremConsequences.PNTAPRelW →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C x₀ : ℝ, 0 < C ∧ MeanSquareHypW ε C x₀ :=
  Formalism.HermitianLattices.PrimeNumberTheoremConsequences.mean_square_of_prime_number_theorem
end Formalism.HermitianLattices.WeakMeanSquareEstimates
