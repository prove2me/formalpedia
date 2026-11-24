-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.glAct_wtspC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:48:57.208791+00:00
-- url     : https://prove2.me/submissions/97f810f6-3525-4bd3-ae19-655d41917413

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_keep
import Theorems.Thm_Formalism_CountingSumsFrames_wt_shift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (c d : Fin r) (μ : Fin r → ℤ) :
    ∀ x ∈ WtSpC p LL j Cs μ, glAct p LL j c d x ∈ WtSpC p LL j Cs (shiftW μ c d) := by
  intro x hx
  refine glAct_keep LL j c d {m | ∀ e ∈ Cs, wt LL j e m = μ e}
    {m | ∀ e ∈ Cs, wt LL j e m = shiftW μ c d e} ?_ ?_ x hx
  · intro i hi hv m hm h1
    rw [Set.mem_setOf_eq] at hm ⊢
    intro e he
    rw [(wt_shift LL j c d e i hi m).1 hv h1, hm e he]
    rfl
  · intro i hi hv m hm h1
    rw [Set.mem_setOf_eq] at hm ⊢
    intro e he
    rw [(wt_shift LL j c d e i hi m).2 hv h1, hm e he]
    rfl
end Formalism.InvariantFactorPaths.L4
