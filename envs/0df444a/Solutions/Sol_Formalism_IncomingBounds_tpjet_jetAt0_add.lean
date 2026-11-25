-- Prove2me | solution 1 for Formalism.IncomingBounds.tpjet_jetAt0_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:40:58.11471+00:00
-- url     : https://prove2.me/submissions/7f4f9ef8-cf11-40de-a740-309d98cf3b51

import Definitions.Def_Formalism_IncomingBounds_DefsThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPJet
import Theorems.Thm_Formalism_IncomingBounds_tpjet_jetAt0_superset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.IncomingBounds
section
variable {C : Type} [Field C]
private theorem mem_support_or_of_mem_support_add {σ : Type} (P Q : MvPolynomial σ C)
    (a : σ →₀ ℕ) (ha : a ∈ (P + Q).support) : a ∈ P.support ∨ a ∈ Q.support := by
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_add] at ha
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff]
  by_cases hP : MvPolynomial.coeff a P = 0
  · right
    rwa [hP, zero_add] at ha
  · exact Or.inl hP
end
end Formalism.IncomingBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
variable {C : Type} [Field C]
namespace Formalism.IncomingBounds
theorem _root_.solution {σ : Type} (P Q : MvPolynomial σ C) (G : MvPowerSeries σ C) :
    jetAt0 (P + Q) G = jetAt0 P G + jetAt0 Q G := by
  classical
  have h1 : (P + Q).support ⊆ P.support ∪ Q.support := by
    intro a ha
    exact Finset.mem_union.2 (mem_support_or_of_mem_support_add P Q a ha)
  have h2 : P.support ⊆ P.support ∪ Q.support := by
    intro a ha
    exact Finset.mem_union.2 (Or.inl ha)
  have h3 : Q.support ⊆ P.support ∪ Q.support := by
    intro a ha
    exact Finset.mem_union.2 (Or.inr ha)
  rw [tpjet_jetAt0_superset (P + Q) G _ h1, tpjet_jetAt0_superset P G _ h2,
    tpjet_jetAt0_superset Q G _ h3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring
end Formalism.IncomingBounds
