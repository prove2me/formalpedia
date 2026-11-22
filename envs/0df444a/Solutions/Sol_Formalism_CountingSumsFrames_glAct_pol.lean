-- Prove2me | solution 1 for Formalism.CountingSumsFrames.glAct_pol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:52:55.451798+00:00
-- url     : https://prove2.me/submissions/d8dd3e51-3f50-45ac-8102-000dec318ca5

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_shift_apply
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_keep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (LL : Letters N) (j : ℕ) (c d : Fin r) :
    ∀ x ∈ Pol p r LL, glAct p LL j c d x ∈ Pol p r LL := by
  have key : ∀ (i : Fin N) (a b : Fin r) (m : Fin N × Fin r →₀ ℕ), MultiDeg LL m → 1 ≤ m (i, b) →
      MultiDeg LL (Finsupp.single (i, a) 1 + (m - Finsupp.single (i, b) 1)) := by
    intro i a b m hm hb i'
    have h := hm i'
    have : ((∑ c', ((Finsupp.single (i, a) 1 + (m - Finsupp.single (i, b) 1) : Fin N × Fin r →₀ ℕ)) (i', c') : ℕ) : ℤ) =
        ((∑ c', m (i', c') : ℕ) : ℤ) := by
      rw [Nat.cast_sum, Nat.cast_sum]
      rw [Finset.sum_congr rfl (fun c' _ => shift_apply m (i, a) (i, b) (i', c') hb)]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      by_cases hi : i = i'
      · subst hi
        simp [Prod.mk.injEq]
      · simp [Prod.mk.injEq, hi]
    have := Nat.cast_injective this
    rw [this, h]
  exact glAct_keep LL j c d _ _ (fun i _ _ m hm hb => key i c d m hm hb) (fun i _ _ m hm hb => key i d c m hm hb)
end Formalism.CountingSumsFrames
