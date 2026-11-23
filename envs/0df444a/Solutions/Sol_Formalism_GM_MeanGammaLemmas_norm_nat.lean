-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.norm_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:50.296256+00:00
-- url     : https://prove2.me/submissions/1bc60414-a980-4d33-abfb-b1eddd5fd31c

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Polynomial Finset
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : n ≠ 0) :
    ‖(n : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
  have h1 : ((n : ℚ) : ℚ_[p]) = (n : ℚ_[p]) := by push_cast; rfl
  rw [← h1, Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn),
    padicValRat.of_nat]
  push_cast
  try rfl
end Formalism.GM.MeanGammaLemmas
