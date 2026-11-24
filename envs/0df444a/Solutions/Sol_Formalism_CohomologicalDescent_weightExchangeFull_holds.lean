-- Prove2me | solution 1 for Formalism.CohomologicalDescent.weightExchangeFull_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:10:07.965798+00:00
-- url     : https://prove2.me/submissions/b99e4544-7bf6-4933-99a9-2a4f146e3e53

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWAssembled
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MinorValuationBoundHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightExchangeChainHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Theorems.Thm_Formalism_CohomologicalDescent_twisted_block_bounds
import Theorems.Thm_Formalism_CohomologicalDescent_weightExchangeChain_holds


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
open Formalism Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent
theorem _root_.solution : WEFull := by
  intro ι _ σ k j t q l h F _ _ W U U' bot cst kap c τ hl hlt hW hb hd hU hU' hUb hprod hU0 hU'h
    hsum hblock hcτ
  obtain ⟨h1, h2, h3⟩ := twisted_block_bounds ι σ l h t (k + j + t + q) F W U' bot kap c hl hW hb hd
  have hκ : ∀ i s, |kap i s| ≤ ((h / (l - 1) : ℕ) : ℤ) := by
    intro i s
    have hl2 := hl.two_le
    have hpos : (0 : ℤ) < ((l - 1 : ℕ) : ℤ) := by omega
    have e : ((l - 1 : ℕ) : ℤ) = (l : ℤ) - 1 := by omega
    rw [Int.natCast_div, Int.le_ediv_iff_mul_le hpos, e, mul_comm]
    exact h1 i s
  exact weightExchangeChain_holds k j t q l h (h / (l - 1)) F (U τ) (U' τ) (U (σ τ)) (U' (σ τ)) (bot τ)
    (bot (σ τ)) (cst τ) (cst (σ τ)) (kap τ) (kap (σ τ)) hl hlt (hU τ) (hU' τ) (hU (σ τ))
    (hU' (σ τ)) hU0 (fun a => (hU'h a).2) hsum hblock (hUb (σ τ)) (hprod τ) (hprod (σ τ))
    (hκ τ) (hκ (σ τ)) (h2 τ) (h2 (σ τ)) (by rw [← hcτ]; exact h3 τ)
end Formalism.CohomologicalDescent
