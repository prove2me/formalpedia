-- Prove2me | solution 1 for Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts.differentiableOn_wZeta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:40.342511+00:00
-- url     : https://prove2.me/submissions/fcb9d73f-8744-47dd-ac65-9b1f75329378

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_AnalyticIdentityTheoremsZetaFacts
import Theorems.Thm_Formalism_L2_Th1_F_AnalyticIdentityTheoremsZetaFacts_hasSumLU_wZeta
import Theorems.Thm_Formalism_L2_Th1_F_AnalyticIdentityTheoremsZetaFacts_hasDerivAt_term
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Filter Topology
namespace Formalism.L2.Th1.F
namespace AnalyticIdentityTheoremsZetaFacts
private lemma differentiableOn_of_hasSumLocallyUniformlyOn' {ι : Type*} {F : ι → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ}
    (h : HasSumLocallyUniformlyOn F g U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hU : IsOpen U) :
    DifferentiableOn ℂ g U := by
  have h' : TendstoLocallyUniformlyOn (fun s x => ∑ i ∈ s, F i x) g Filter.atTop U := h
  exact h'.differentiableOn
    (Filter.Eventually.of_forall fun s => DifferentiableOn.fun_sum fun i _ => hF i) hU
end AnalyticIdentityTheoremsZetaFacts
open AnalyticIdentityTheoremsZetaFacts
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts
namespace Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts
theorem _root_.solution (L : PeriodPair) :
    DifferentiableOn ℂ (wZeta L) (L.lattice : Set ℂ)ᶜ := by
  refine differentiableOn_of_hasSumLocallyUniformlyOn' (hasSumLU_wZeta L).hasSumLocallyUniformlyOn (fun l => ?_)
    L.isClosed_lattice.isOpen_compl
  intro w hw
  have hwl : w - l ≠ 0 := by
    intro e
    apply hw
    rw [sub_eq_zero.mp e]
    exact l.2
  exact (hasDerivAt_term l w hwl).differentiableAt.differentiableWithinAt
end Formalism.L2.Th1.F.AnalyticIdentityTheoremsZetaFacts
