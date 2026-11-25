-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.GoodQ_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:47:59.353535+00:00
-- url     : https://prove2.me/submissions/65ca1df1-2546-477b-bb2b-6776d4553805

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas__v_zero_b9ef19ebc562

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (ρ : Fin r) : GoodQ (N := N) ρ 0 0 := ⟨δv_zero, by simp⟩
end Formalism.GM.gammaIntegralityLemmas
