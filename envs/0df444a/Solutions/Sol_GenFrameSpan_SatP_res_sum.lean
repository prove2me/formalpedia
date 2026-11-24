-- Prove2me | solution 1 for GenFrameSpan.SatP.res_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:06:55.837483+00:00
-- url     : https://prove2.me/submissions/24d4f93d-d1ca-4a07-933d-957ee3ee155d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatProj
import Theorems.Thm_GenFrameSpan_SatP_res_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open GenFrameSpan
open CutKW MvPolynomial
open GenFrameSpan.SatP
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 : ℕ}
namespace GenFrameSpan.SatP
theorem _root_.solution (n : Lt → (ℕ × Fin N0 →₀ ℕ)) (t : Lt) :
    res t (∑ s, (n s).mapDomain (emb s)) = n t := by
  ext p
  rw [res_apply, Finsupp.finsetSum_apply, Finset.sum_eq_single t]
  · exact Finsupp.mapDomain_apply (emb_inj t) _ _
  · intro s _ hst
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨q, hq⟩
    simp only [emb, Prod.mk.injEq] at hq
    exact hst hq.1
  · intro h
    exact absurd (Finset.mem_univ t) h
end GenFrameSpan.SatP
