-- Prove2me | solution 1 for Formalism.CountingSumsFrames.glAct_keep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:48:47.421811+00:00
-- url     : https://prove2.me/submissions/9bcbc7f4-cd8a-43e8-b18a-08b167e3a352

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_XD_keep

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
theorem _root_.solution (LL : Letters N) (j : ℕ) (c d : Fin r) (Q Q' : Set (Fin N × Fin r →₀ ℕ))
    (hv : ∀ i : Fin N, (i : ℕ) < j → LL.vec i = true → ∀ m ∈ Q, 1 ≤ m (i, d) →
      Finsupp.single (i, c) 1 + (m - Finsupp.single (i, d) 1) ∈ Q')
    (hc : ∀ i : Fin N, (i : ℕ) < j → LL.vec i = false → ∀ m ∈ Q, 1 ≤ m (i, c) →
      Finsupp.single (i, d) 1 + (m - Finsupp.single (i, c) 1) ∈ Q') :
    ∀ x ∈ restrictSupport ℚ_[p] Q, glAct p LL j c d x ∈ restrictSupport ℚ_[p] Q' := by
  intro x hx
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : (i : ℕ) < j
  · by_cases hvi : LL.vec i = true
    · simp only [if_pos hi, if_pos hvi]
      exact XD_keep (i, c) (i, d) Q Q' (fun m hm h1 => hv i hi hvi m hm h1) x hx
    · simp only [if_pos hi, if_neg hvi, LinearMap.neg_apply]
      refine Submodule.neg_mem _ ?_
      have hf : LL.vec i = false := by simpa using hvi
      exact XD_keep (i, d) (i, c) Q Q' (fun m hm h1 => hc i hi hf m hm h1) x hx
  · simp only [if_neg hi, LinearMap.zero_apply]
    exact Submodule.zero_mem _
end Formalism.CountingSumsFrames
